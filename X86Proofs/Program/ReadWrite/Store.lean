import X86Proofs.Program.Effect
import X86Proofs.Program.ReadWrite.Load

/-!
# Stores: a data write to memory

Shared by the forms whose only visible result is a data write of `n` bits (`n` ∈ {8, 16, 32, 64,
128}) to memory, without flags (`mov m, r`, `mov m, imm`; `movaps m, xmm` at 128 bits): their form
result is `writeResult (dataAccess t "store") (.mem a) v nextIP`, the write's bookkeeping (oracle
bits, a `store` trace event), `Next_IP`, then the memory write (`logicalMemWrite_run`, or
`logicalMemWrite_run_align` for an SSE alignment type; with `nt := true` for the non-temporal
stores MOVNTI, MOVNTPS, MOVNTPD, MOVNTDQ, whose write is the same).

- `MemWritable s addr len`: the `len` bytes at `addr` can be written by one data write and the
  machine stays ready: below 4 GiB, present in RAM, and none of the page-table entries
  (`PageTableEntriesApart`: the eight bytes at `0x1000`, the 32 at `0x2000`). The bytes may cross
  a 4 KiB page.
- `RangeApart a len p codeLen`: the `len` bytes at `a` miss the `codeLen` bytes at `p`
  (`RangeApart.of_toNat` from a comparison of the addresses as numbers).
- `StorePre p codeLen addr len`: a store triple's precondition at `p` for an instruction of
  `codeLen` bytes: RIP = `p`, `MemWritable` at `addr s`, and the written bytes miss the
  instruction's own bytes.
- `SegStorePre p codeLen r base addr len`: `StorePre` at `base + addr s` for an operand with a
  segment override `r` (FS or GS), and the segment ready with base `base`.
- After a store step (`afterStep s length fun t => writeResult (dataAccess t "store") …`):
  `afterStep_store_rip`, `Operand.read_afterStep_store` (the operand reads the value written),
  `ReadyToStep.afterStep_store` (page tables untouched), `AgreesExcept.afterStep_store` (only the
  written bytes and RIP change).
- `storeEffect`, `StepEffect.of_store`: the step of any store form with its effect, from its step
  theorem; `storeEffect_avoids` and `Triple.of_store`: its triple. `StepEffect.of_store_pre` and
  `Triple.of_store_pre` for a stronger precondition (e.g. `SseAlignedStorePre`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The `len` bytes at `addr` can be written in place (`logicalMemWrite_run`): below 4 GiB (the
identity map), present in RAM, and none of the page-table entries (`PageTableEntriesApart`; so
the machine stays ready). They may cross a 4 KiB page. -/
structure MemWritable (s : RamState) (addr : BitVec 64) (len : Nat) : Prop where
  low : addr.toNat + len ≤ 2^32
  mem : ∀ i, i < len → (s.external[addr + BitVec.ofNat 64 i]?).isSome
  tables : PageTableEntriesApart addr.toNat len

/-- Writable bytes are readable. -/
theorem MemWritable.readable {s : RamState} {addr : BitVec 64} {len : Nat}
    (h : MemWritable s addr len) : MemReadable s addr len :=
  ⟨h.low, h.mem⟩

/-- Writability depends only on memory. -/
theorem MemWritable.of_external_eq {s t : RamState} {addr : BitVec 64} {len : Nat}
    (h : MemWritable s addr len) (he : t.external = s.external) : MemWritable t addr len :=
  ⟨h.low, fun i hi => he ▸ h.mem i hi, h.tables⟩

/-- The `len` bytes at `a` and the `codeLen` bytes at `p` are different addresses. -/
def RangeApart (a : BitVec 64) (len : Nat) (p : BitVec 64) (codeLen : Nat) : Prop :=
  ∀ i < len, ∀ j < codeLen, a + BitVec.ofNat 64 i ≠ p + BitVec.ofNat 64 j

/-- Two ranges that do not wrap around 2^64 are apart if one ends before the other starts. -/
theorem RangeApart.of_toNat {a p : BitVec 64} {len codeLen : Nat}
    (ha : a.toNat + len ≤ 2^64) (hp : p.toNat + codeLen ≤ 2^64)
    (h : a.toNat + len ≤ p.toNat ∨ p.toNat + codeLen ≤ a.toNat) : RangeApart a len p codeLen := by
  intro i hi j hj he
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (a := j) (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (a := p.toNat + j) (by omega)] at this
  omega

/-- The precondition of a store triple at `p`, for an instruction of `codeLen` bytes writing the
`len` bytes at the operand's address (a function of the start state, e.g.
`fun s => am.addr s (p + codeLen)`): RIP = `p`, the bytes can be written in place, and they miss
the instruction's own bytes. -/
structure StorePre (p : BitVec 64) (codeLen : Nat) (addr : RamState → BitVec 64) (len : Nat)
    (s : RamState) : Prop where
  rip : s.RIP = p
  write : MemWritable s (addr s) len
  code : RangeApart (addr s) len p codeLen

/-- The precondition of a store triple at `p` (an instruction of `codeLen` bytes) whose memory
operand has a segment override `r` (FS or GS): `StorePre` at `base + addr s` (the operand's offset
plus the segment's base), and the segment is ready with base `base`. -/
structure SegStorePre (p : BitVec 64) (codeLen : Nat) (r : SegReg) (base : BitVec 64)
    (addr : RamState → BitVec 64) (len : Nat) (s : RamState) : Prop where
  store : StorePre p codeLen (fun t => base + addr t) len s
  seg : r.Ready base s

/-! ### Reading back a write -/

/-- Bit `k` of the value `memLoad` assembles from the first `j` bytes `b 0`, …: bit `k % 8` of byte
`k / 8`, or 0 above them. -/
private theorem foldl_bytes_getLsbD {n : Nat} (b : Nat → UInt8) (j k : Nat) (hk : k < n) :
    ((List.range j).foldl (fun acc i =>
      acc ||| (BitVec.ofNat n (b i).toNat <<< (8 * i))) (0 : BitVec n)).getLsbD k =
      (decide (k < 8 * j) && (b (k / 8)).toNat.testBit (k % 8)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, BitVec.getLsbD_or, ih,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat]
    by_cases h1 : k < 8 * j
    · simp [h1, show k < 8 * (j + 1) by omega]
    · by_cases h2 : k < 8 * (j + 1)
      · have hkj : k / 8 = j := by omega
        have hkm : k - 8 * j = k % 8 := by omega
        simp [h1, h2, hkj, hkm, hk, show k % 8 < n by omega]
      · have : (b j).toNat.testBit (k - 8 * j) = false := by
          apply Nat.testBit_lt_two_pow
          exact Nat.lt_of_lt_of_le (b j).toNat_lt (Nat.pow_le_pow_right (by decide) (by omega))
        simp [h1, h2, this]

/-- Bit `k % 8` of the byte `memStore` puts at offset `k / 8` is bit `k` of the value. -/
private theorem storedByte_testBit {n : Nat} (v : BitVec n) (k : Nat) :
    (storedByte v (k / 8)).toNat.testBit (k % 8) = v.getLsbD k := by
  have : ∀ x : Nat, (UInt8.ofNat x).toNat = x % 2 ^ 8 := fun x => by simp
  rw [storedByte, this, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    show 8 * (k / 8) + k % 8 = k by omega, BitVec.testBit_toNat]
  simp [show k % 8 < 8 by omega]

/-- Byte `i` of a value as `memStore` stores it is its 8-bit lane `i`, stored alone. -/
theorem storedByte_extractLsb' {n : Nat} (v : BitVec n) (i : Nat) :
    storedByte v i = storedByte (v.extractLsb' (8 * i) 8) 0 := by
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 8
  · have h1 := storedByte_testBit v (8 * i + j)
    have h2 := storedByte_testBit (v.extractLsb' (8 * i) 8) j
    rw [show (8 * i + j) / 8 = i by omega, show (8 * i + j) % 8 = j by omega] at h1
    rw [show j / 8 = 0 by omega, show j % 8 = j by omega] at h2
    rw [h1, h2, BitVec.getLsbD_extractLsb']
    simp [hj, Nat.add_comm]
  · have hlt (x : UInt8) : x.toNat < 2 ^ j :=
      Nat.lt_of_lt_of_le x.toNat_lt (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_lt_two_pow (hlt _), Nat.testBit_lt_two_pow (hlt _)]

/-- Reading back an `n`-bit write (`n` a multiple of 8, at most 128). -/
theorem memLoad_memStore (m : Ram) (addr : BitVec 64) {n : Nat} (hn : n % 8 = 0) (h64 : n ≤ 128)
    (v : BitVec n) : memLoad (memStore m addr v) addr n = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [memLoad, foldl_bytes_getLsbD _ _ _ hk]
  have hb : memByte (memStore m addr v) (addr + BitVec.ofNat 64 (k / 8)) = storedByte v (k / 8) := by
    rw [memByte]
    simp only [PhysicalMemory.read]
    rw [memStore_getElem?_self m addr v h64 (k / 8) (by omega)]
    rfl
  rw [hb, storedByte_testBit]
  simp [show k < 8 * (n / 8) by omega]

/-- `memLoad_memStore` for a store of at most `2^64` bytes (a `REP` string store). -/
theorem memLoad_memStore_of_le (m : Ram) (addr : BitVec 64) {n : Nat} (hn : n % 8 = 0)
    (hle : n / 8 ≤ 2 ^ 64) (v : BitVec n) : memLoad (memStore m addr v) addr n = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [memLoad, foldl_bytes_getLsbD _ _ _ hk]
  have hb : memByte (memStore m addr v) (addr + BitVec.ofNat 64 (k / 8)) = storedByte v (k / 8) := by
    rw [memByte]
    simp only [PhysicalMemory.read]
    rw [memStore_getElem?_self_of_le m addr v hle (k / 8) (by omega)]
    rfl
  rw [hb, storedByte_testBit]
  simp [show k < 8 * (n / 8) by omega]

/-- Byte `i` of an `n`-bit memory read, as `memStore` would store it, is the byte at `addr + i`
(any `n`, not only up to 64: `rep movsq` reads its whole source range as one value). -/
theorem storedByte_memLoad (m : Ram) (addr : BitVec 64) {n : Nat} (i : Nat) (hi : i < n / 8) :
    storedByte (memLoad m addr n) i = memByte m (addr + BitVec.ofNat 64 i) := by
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 8
  · have h1 := storedByte_testBit (memLoad m addr n) (8 * i + j)
    rw [show (8 * i + j) / 8 = i by omega, show (8 * i + j) % 8 = j by omega] at h1
    rw [h1, memLoad, foldl_bytes_getLsbD _ _ _ (by omega)]
    simp [show 8 * i + j < 8 * (n / 8) by omega, show (8 * i + j) / 8 = i by omega,
      show (8 * i + j) % 8 = j by omega]
  · have hlt (x : UInt8) : x.toNat < 2 ^ j :=
      Nat.lt_of_lt_of_le x.toNat_lt (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_lt_two_pow (hlt _), Nat.testBit_lt_two_pow (hlt _)]

/-- Two `n`-bit memory reads are equal if their bytes are. -/
theorem memLoad_congr {m m' : Ram} {a b : BitVec 64} {n : Nat}
    (h : ∀ i < n / 8, memByte m (a + BitVec.ofNat 64 i) = memByte m' (b + BitVec.ofNat 64 i)) :
    memLoad m a n = memLoad m' b n := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [memLoad, memLoad, foldl_bytes_getLsbD _ _ _ hk, foldl_bytes_getLsbD _ _ _ hk]
  by_cases hk' : k < 8 * (n / 8)
  · rw [h (k / 8) (by omega)]
  · simp [hk']

/-- Equal `n`-bit memory reads have equal bytes. -/
theorem memByte_of_memLoad_eq {m m' : Ram} {a b : BitVec 64} {n : Nat}
    (h : memLoad m a n = memLoad m' b n) (i : Nat) (hi : i < n / 8) :
    memByte m (a + BitVec.ofNat 64 i) = memByte m' (b + BitVec.ofNat 64 i) := by
  rw [← storedByte_memLoad m a i hi, h, storedByte_memLoad m' b i hi]

/-- An `n`-bit memory read (`n` a multiple of 8, any width) is `v` if its bytes are `v`'s, as
`memStore` would store them. -/
theorem memLoad_eq_of_memByte {m : Ram} {a : BitVec 64} {n : Nat} {v : BitVec n} (hn : n % 8 = 0)
    (h : ∀ i < n / 8, memByte m (a + BitVec.ofNat 64 i) = storedByte v i) : memLoad m a n = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [memLoad, foldl_bytes_getLsbD _ _ _ hk, h (k / 8) (by omega), storedByte_testBit]
  simp [show k < 8 * (n / 8) by omega]

/-- Byte `i` of `c` copies of `x` (`w` a multiple of 8) is byte `i mod (w / 8)` of `x`. -/
theorem storedByte_replicate {w : Nat} (x : BitVec w) (hw : w % 8 = 0) (c i : Nat)
    (hi : i < w / 8 * c) : storedByte (x.replicate c) i = storedByte x (i % (w / 8)) := by
  obtain ⟨q, rfl⟩ : ∃ q, w = 8 * q := ⟨w / 8, by omega⟩
  have hq8 : 8 * q / 8 = q := by omega
  rw [hq8] at hi ⊢
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · rw [h0, Nat.zero_mul] at hi
      omega
    · exact h0
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 8
  · have h1 := storedByte_testBit (x.replicate c) (8 * i + j)
    have h2 := storedByte_testBit x (8 * (i % q) + j)
    rw [show (8 * i + j) / 8 = i by omega, show (8 * i + j) % 8 = j by omega] at h1
    rw [show (8 * (i % q) + j) / 8 = i % q by omega,
      show (8 * (i % q) + j) % 8 = j by omega] at h2
    have hd := Nat.mod_add_div i q
    have hlt := Nat.mod_lt i hq
    have hm : (8 * i + j) % (8 * q) = 8 * (i % q) + j := by
      calc (8 * i + j) % (8 * q)
          = (8 * (i % q) + j + 8 * q * (i / q)) % (8 * q) := by
            rw [Nat.mul_assoc]
            congr 1
            omega
        _ = (8 * (i % q) + j) % (8 * q) := Nat.add_mul_mod_self_left _ _ _
        _ = 8 * (i % q) + j := Nat.mod_eq_of_lt (by omega)
    have hlt' : 8 * i + j < 8 * q * c := by
      have := Nat.mul_le_mul_left 8 (show i + 1 ≤ q * c by omega)
      rw [Nat.mul_assoc]
      omega
    rw [h1, h2, BitVec.getLsbD_replicate, hm]
    simp [hlt']
  · have hlt (y : UInt8) : y.toNat < 2 ^ j :=
      Nat.lt_of_lt_of_le y.toNat_lt (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_lt_two_pow (hlt _), Nat.testBit_lt_two_pow (hlt _)]

/-! ### After a store step -/

/-- After a store form ending in `writeResult … nextIP`, RIP is `nextIP`. -/
theorem afterStep_store_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat) {n : Nat}
    (a : BitVec 64) (v : BitVec n) (nextIP : BitVec 64) :
    (afterStep s length fun t =>
      writeResult (dataAccess t "store") (.mem a : Operand n) v nextIP).RIP = nextIP := by
  simp [afterStep, finishStep, writeResult, Operand.write, dataAccess, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- Memory after a store step: the write. -/
@[simp] theorem afterStep_store_external (s : RamState) (length : Nat) {n : Nat} (a : BitVec 64)
    (v : BitVec n) (nextIP : BitVec 64) :
    (afterStep s length fun t =>
      writeResult (dataAccess t "store") (.mem a : Operand n) v nextIP).external =
      memStore s.external a v := rfl

/-- `SegStorePre p codeLen r base addr len`: `StorePre` at `base + addr s` for an operand with a
  segment override `r` (FS or GS), and the segment ready with base `base`.
- After a store step, the written operand reads the value written. -/
theorem Operand.read_afterStep_store (s : RamState) (length : Nat) {n : Nat} (hn : n % 8 = 0)
    (h64 : n ≤ 128) (a : BitVec 64) (v : BitVec n) (nextIP : BitVec 64) :
    (Operand.mem a : Operand n).read (afterStep s length fun t =>
      writeResult (dataAccess t "store") (.mem a : Operand n) v nextIP) = v := by
  simp only [Operand.read, afterStep_store_external]
  exact memLoad_memStore _ _ hn h64 v

/-- Preservation for a store: if the bytes written lie below 4 GiB and outside the page-table
frames, the state after the step is ready to step again. Only memory, the oracle, the trace,
`Next_IP`, RIP and per-step bookkeeping change. -/
theorem ReadyToStep.afterStep_store [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat) {n : Nat}
    (a : BitVec 64) (v : BitVec n) (nextIP : BitVec 64) (hlow : a.toNat + n / 8 ≤ 2^32)
    (htables : PageTableEntriesApart a.toNat (n / 8)) :
    ReadyToStep (afterStep s length fun t =>
      writeResult (dataAccess t "store") (.mem a : Operand n) v nextIP) := by
  have hst : SameControls s (afterStep s length fun t =>
      writeResult (dataAccess t "store") (.mem a : Operand n) v nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  have hmem : Prelude.IdentityMappedMemory (afterStep s length fun t =>
      writeResult (dataAccess t "store") (.mem a : Operand n) v nextIP) := by
    refine ⟨h.memory.cr3, ?_⟩
    rw [afterStep_store_external]
    exact IdentityPageTableMemory.memStore h.memory.tables _ _ hlow htables
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass, hc.debug,
      hc.aet⟩,
    hmem,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, hr.tf, hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-- A store of `n` bits at `a` changes only those `n / 8` bytes and RIP (besides the per-step
bookkeeping). -/
theorem AgreesExcept.afterStep_store (s : RamState) (length : Nat) {n : Nat} (a : BitVec 64)
    (v : BitVec n) (nextIP : BitVec 64) :
    AgreesExcept [.mem a (n / 8), .rip] s (afterStep s length fun t =>
      writeResult (dataAccess t "store") (.mem a : Operand n) v nextIP) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r => rfl
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => rfl
  · rw [afterStep_store_external]
    apply memStore_getElem?_of_ne
    intro i hi he
    exact hx (.mem a (n / 8)) (by simp) ⟨i, hi, he.symm⟩
  · simp only [fixedPart, afterStep, finishStep, writeResult, Operand.write, dataAccess,
      afterFetches, beforeFetch, resetStepFields]
  · rw [afterStep_store_external]
    exact memStore_isSome _ _ _ x hx

/-! ### Effect and triple -/

/-- The effect of a store at `p` of an instruction `len` bytes long: RIP = `p + len`, and the
`n`-bit memory operand at `addr s` set to `v s` (both functions of the start state `s`). -/
def storeEffect (p : BitVec 64) (len : Nat) {n : Nat} (addr : RamState → BitVec 64)
    (v : RamState → BitVec n) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.mem (addr s) : Operand n), v s⟩]

@[simp] theorem storeEffect_components (p : BitVec 64) (len : Nat) {n : Nat}
    (addr : RamState → BitVec 64) (v : RamState → BitVec n) (s : RamState) :
    (storeEffect p len addr v s).components = [.mem (addr s) (n / 8), .rip] := rfl

/-- An effect that writes only memory bytes apart from the code (and RIP) avoids the code. -/
theorem Effect.avoids_of_components_mem_rip {e : Effect} {a : BitVec 64} {len : Nat}
    (h : e.components = [.mem a len, .rip]) {p : BitVec 64} {bytes : List UInt8}
    (hap : RangeApart a len p bytes.length) : e.Avoids (codeRange p bytes) := by
  intro x hx c hc hcov
  rw [h] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨i, hi, hxe⟩ := hcov
    obtain ⟨j, hj, hxj⟩ := exists_of_mem_codeRange hx
    exact hap i hi j hj (hxe.symm.trans hxj)
  · exact hcov

/-- A store effect avoids the instruction's code when the store precondition holds: the written
bytes are apart from the instruction's `len` bytes. -/
theorem storeEffect_avoids {p : BitVec 64} {bytes : List UInt8} {len : Nat}
    (hlen : bytes.length = len) {n : Nat} (addr : RamState → BitVec 64) (v : RamState → BitVec n)
    {s : RamState} (h : StorePre p len addr (n / 8) s) :
    (storeEffect p len addr v s).Avoids (codeRange p bytes) := by
  subst hlen
  exact Effect.avoids_of_components_mem_rip (storeEffect_components p _ addr v s) h.code

/--
The step of a store form at `p` with its effect, under a precondition `P` that implies `StorePre`
(e.g. `StorePre` plus SSE support and alignment, for `movaps`), from its step theorem. If from
every ready state with the instruction `bytes` at `p` and `P`, one `step` runs the form, ending in
an `n`-bit store of `v s` at `addr s` with `Next_IP` = `p + len`, then that step reaches a ready
state with the effect `storeEffect p len addr v`.
-/
theorem StepEffect.of_store_pre [Bindings] {P : RamState → Prop} {p : BitVec 64}
    {bytes : List UInt8} {len : Nat} {n : Nat} (hn : n % 8 = 0) (h64 : n ≤ 128)
    (addr : RamState → BitVec 64) (v : RamState → BitVec n)
    (hpre : ∀ s, P s → StorePre p len addr (n / 8) s)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → P s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        writeResult (dataAccess t "store") (.mem (addr s) : Operand n) (v s)
          (BitVec.add p (BitVec.ofNat 64 len))))) :
    StepEffect P (codeRange p bytes) (storeEffect p len addr v) := by
  intro s h hcode hs
  have hp := hpre s hs
  exact ⟨_, hstep s h hcode hs,
    ReadyToStep.afterStep_store h _ _ _ _ hp.write.low hp.write.tables,
    ⟨afterStep_store_rip h _ _ _ _, Operand.read_afterStep_store s _ hn h64 _ _ _, trivial,
      AgreesExcept.afterStep_store s _ _ _ _⟩⟩

/-- The step of a store form with its effect, under `StorePre`: `StepEffect.of_store_pre` with
`P = StorePre`. -/
theorem StepEffect.of_store [Bindings] {p : BitVec 64} {bytes : List UInt8} {len : Nat}
    {n : Nat} (hn : n % 8 = 0) (h64 : n ≤ 128)
    (addr : RamState → BitVec 64) (v : RamState → BitVec n)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s →
      StorePre p len addr (n / 8) s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        writeResult (dataAccess t "store") (.mem (addr s) : Operand n) (v s)
          (BitVec.add p (BitVec.ofNat 64 len))))) :
    StepEffect (StorePre p len addr (n / 8)) (codeRange p bytes) (storeEffect p len addr v) :=
  StepEffect.of_store_pre hn h64 addr v (fun _ h => h) hstep

/--
The triple of a store form at `p` under a precondition `P` that implies `StorePre`, from its step
theorem (as `StepEffect.of_store_pre`): the effect `storeEffect p len addr v`, which avoids the
instruction's `len` bytes (`storeEffect_avoids`).
-/
theorem Triple.of_store_pre [Bindings] {P : RamState → Prop} {p : BitVec 64} {bytes : List UInt8}
    {len : Nat} (hlen : bytes.length = len) {n : Nat} (hn : n % 8 = 0) (h64 : n ≤ 128)
    (addr : RamState → BitVec 64) (v : RamState → BitVec n)
    (hpre : ∀ s, P s → StorePre p len addr (n / 8) s)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → P s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        writeResult (dataAccess t "store") (.mem (addr s) : Operand n) (v s)
          (BitVec.add p (BitVec.ofNat 64 len))))) :
    Triple P (codeRange p bytes) (Effect.post (storeEffect p len addr v)) :=
  Triple.of_effect (fun s hs => storeEffect_avoids hlen addr v (hpre s hs))
    (StepEffect.of_store_pre hn h64 addr v hpre hstep)

/--
The triple of a store form at `p`, from its step theorem. If from every ready state with the
instruction `bytes` (`len` long) at `p` and `StorePre`, one `step` runs the form, ending in an
`n`-bit store of `v s` at `addr s` with `Next_IP` = `p + len`, then the triple holds with the effect
`storeEffect p len addr v`.
-/
theorem Triple.of_store [Bindings] {p : BitVec 64} {bytes : List UInt8} {len : Nat}
    (hlen : bytes.length = len) {n : Nat} (hn : n % 8 = 0) (h64 : n ≤ 128)
    (addr : RamState → BitVec 64) (v : RamState → BitVec n)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s →
      StorePre p len addr (n / 8) s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        writeResult (dataAccess t "store") (.mem (addr s) : Operand n) (v s)
          (BitVec.add p (BitVec.ofNat 64 len))))) :
    Triple (StorePre p len addr (n / 8)) (codeRange p bytes)
      (Effect.post (storeEffect p len addr v)) :=
  Triple.of_store_pre hlen hn h64 addr v (fun _ h => h) hstep

end X86Proofs
