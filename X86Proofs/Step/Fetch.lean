import X86Proofs.Step.LogicalToLinear
import X86Proofs.Step.ReadyToStepCore

/-!
# Instruction fetch

`Mem_Fetch ip n` for `n` = 8, 16, 32 or 64 bits of the instruction at RIP: on a `FetchReady`
state it returns the `n / 8` bytes stored at `ip`, `ip + 1`, … assembled little-endian, and uses up
the oracle bits lean-x86's address translation draws (464 per byte, `afterFetches`).

- `memFetch_byte_stages`: the four stages of one byte's fetch (logical address, linear address,
  physical address, the byte), from `Step/LogicalToLinear.lean` and `Step/Paging.lean`.
- `memFetch_run_imm`: the fetch of `n / 8` bytes, one `memFetch_byte_stages` per byte; the value is
  `immPartial b (n / 8)`, the bytes assembled the way lean-x86 assembles them.
- `memFetch_run`: its one-byte instance; `memFetch_run_of_bytesAt`: byte `i` of an instruction
  stored at RIP (`BytesAt`).

Immediates as byte strings are in `Step/FetchImm.lean`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers
open scoped X86.Runtime.Syntax

/-- The `RamState` facts lean-x86's instruction fetch needs (all from `Prelude`). -/
structure FetchReady [instBindings : Bindings] (s : RamState) : Prop where
  cs : s.CS = userCodeSegment
  cr0 : Prelude.SupportedIntegerCR0 s.CR0
  cr3 : s.CR3 = 0x1000
  cr4 : Prelude.SupportedIntegerCR4 s.CR4
  efer : Prelude.SupportedIntegerEFER s.IA32_EFER
  maxPhysical : Bindings.processor.config.Max_Physical_Address = 52
  early : Bindings.processor.config.Feature_Early_Page_Access_Bit_Update = false
  lam : Prelude.ReportsCPUFeature Bindings.processor s CPUID_LAM_Encoding false
  lass : Prelude.ReportsCPUFeature Bindings.processor s CPUID_LASS_Encoding false
  /-- CPUID.CET_SS is answered (the page walk reads it on writes). -/
  cetSS : ∃ b, Prelude.ReportsCPUFeature Bindings.processor s CPUID_CET_SS_Encoding b
  /-- No physical address is in the SMRR range, so RAM reads are not blocked. -/
  smrr : Prelude.SMRRUnblocked instBindings s
  /-- Write-back memory type below 4 GiB at PAT selector 0. -/
  memoryType : Prelude.WriteBackMemoryType instBindings s 0
  tables : IdentityPageTableMemory s.external

/-- `s` after `k` byte fetches: each draws 464 oracle bits for its address translation. -/
def afterFetches (s : RamState) (k : Nat) : RamState :=
  { s with oracle := oracleSkip s.oracle (464 * k) }

theorem SameControls.afterFetches (s : RamState) (k : Nat) :
    SameControls s (X86Proofs.afterFetches s k) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem FetchReady.afterFetches [Bindings] {s : RamState} (h : FetchReady s) (k : Nat) :
    FetchReady (X86Proofs.afterFetches s k) :=
  have hst := SameControls.afterFetches s k
  ⟨h.cs, h.cr0, h.cr3, h.cr4, h.efer, h.maxPhysical, h.early, reportsCPUFeature_of_sameControls hst h.lam,
    reportsCPUFeature_of_sameControls hst h.lass, h.cetSS.imp fun _ => reportsCPUFeature_of_sameControls hst,
    smrrUnblocked_of_sameControls hst h.smrr,
    writeBackMemoryType_of_sameControls hst h.memoryType, h.tables⟩

/-! ### One byte of a fetch, stage by stage -/

/--
The four stages `Mem_Fetch` goes through for one byte at `ip` (below 4 GiB, present in RAM), on a
`FetchReady` state after `k` fetches: create the logical address (drawing the oracle bits),
translate it to linear (as an instruction fetch, lean-x86's `is_instruction_fetch := true`) and
physical addresses, and read the byte.
-/
theorem memFetch_byte_stages [Bindings] (s : RamState) (k : Nat) (ip : BitVec 64) (byte : UInt8)
    (h : FetchReady s) (haddr : ip.toNat < 2^32) (hmem : s.external[ip]? = some byte) :
    ∃ logical linear physical,
      (Create_Logical_Address (nullDataSegment userCodeSegment) ip 8).run (afterFetches s k) =
        (.ok logical, afterFetches s (k + 1)) ∧
      (Translate_Logical_To_Linear logical .Normal_Alignment userCodeSegment true).run
          (afterFetches s (k + 1)) =
        (.ok linear, afterFetches s (k + 1)) ∧
      (Translate_Linear_To_Physical linear .Memory_Execute).run (afterFetches s (k + 1)) =
        (.ok physical, afterFetches s (k + 1)) ∧
      (Physical_Mem_Fetch physical).run (afterFetches s (k + 1)) =
        (.ok byte.toBitVec, afterFetches s (k + 1)) := by
  have hm := h.afterFetches k
  let u := afterFetches s k
  let v : RamState := {u with oracle := oracleSkip u.oracle 464}
  have hv : v = afterFetches s (k + 1) := by
    simp only [v, u, afterFetches, oracleSkip_oracleSkip, Nat.mul_succ]
  have hmv : FetchReady v := hv ▸ h.afterFetches (k + 1)
  rw [← hv]
  let logical : Address_Translation :=
    { (logicalAddressFromOracle u.oracle (nullDataSegment userCodeSegment) u.CPL ip).1 with
      num_bytes := ((8 / 8 : Nat) : Int) }
  let linear : Address_Translation :=
    {logical with linear_address := ip, is_implicit_supervisor_mode_access := false}
  have hc := createLogicalAddress_run u (nullDataSegment userCodeSegment) ip 8 (by decide)
  have hcan := isCanonicalWrtPagingMode_run v ip 1 hm.cr0 hm.cr4 hm.efer.lme hmv.lam haddr
    (by omega) true
  have hl : (Translate_Logical_To_Linear logical .Normal_Alignment userCodeSegment true).run v =
      (.ok linear, v) :=
    translateLogicalToLinear_run v logical
      (computeLinearAddress_nullDataSegment_run v ip hm.efer.lma)
      (show Is_System_Segment (nullDataSegment userCodeSegment) = _ from rfl)
      (show (nullDataSegment userCodeSegment).is_code.isSome from rfl)
      (show Is_Null_Segment_Selector (nullDataSegment userCodeSegment).selector = _ from rfl) hm.cr0
      hm.efer.lma hmv.lass hcan .Normal_Alignment (by show (0 : Int) < ((8 / 8 : Nat) : Int); decide)
      (AlignmentOk.normal _ _)
  have htranslate : (Translate linear .Memory_Execute).run v =
      (.ok (writeBackIdentityTranslation linear), v) :=
    translate_run v hmv.smrr hmv.memoryType hm.cr3 hm.cr4 hm.efer.lme hm.maxPhysical hm.efer.nxe
      hm.early hm.tables hmv.cetSS linear .Memory_Execute rfl haddr
  have hsplit : (Is_Linear_Access_Split_Across4KB_Pages ip 1).run v = (.ok false, v) := by
    apply isLinearAccessSplitAcross4KBPages_run_of_fits v ip 1 hm.cr0 (by decide)
    have hmod := Int.emod_lt (ip.toNat : Int) (by decide : (4096 : Int) ≠ 0)
    omega
  have hp : (Translate_Linear_To_Physical linear .Memory_Execute).run v =
      (.ok (singleTranslation linear (writeBackIdentityTranslation linear)), v) :=
    translateLinearToPhysical_run v v linear .Memory_Execute _ hm.cr0 hsplit htranslate
  have hb : (Physical_Mem_Fetch (singleTranslation linear (writeBackIdentityTranslation linear))).run v =
      (.ok byte.toBitVec, v) :=
    physicalMemFetch_run _ _ hmv.smrr byte hmem
  exact ⟨logical, linear, _, hc, hl, hp, hb⟩

/-! ### The fetch loop -/

/-- A `for` loop over `g j`, `g (j + 1)`, …, `g (j + m - 1)` whose body takes accumulator `bs i` and
state `ss i` to `bs (i + 1)` and `ss (i + 1)` at each `i` ends with `bs (j + m)` and
`ss (j + m)`. -/
theorem specM_forIn_range'_run {ε σ α β : Type} (g : Nat → α)
    (f : α → β → X86.Runtime.SpecM ε σ (ForInStep β)) (bs : Nat → β) (ss : Nat → σ) (m j : Nat)
    (h : ∀ i, j ≤ i → i < j + m →
      (f (g i) (bs i)).run (ss i) = (.ok (.yield (bs (i + 1))), ss (i + 1))) :
    (forIn ((List.range' j m).map g) (bs j) f).run (ss j) = (.ok (bs (j + m)), ss (j + m)) := by
  induction m generalizing j with
  | zero => rfl
  | succ m ih =>
    simp only [List.range'_succ, List.map_cons, List.forIn_cons]
    rw [specM_bind_run _ _ (h j (Nat.le_refl _) (by omega))]
    have := ih (j + 1) (fun i h1 h2 => h i (by omega) (by omega))
    rw [show j + 1 + m = j + (m + 1) by omega] at this
    exact this

/-- The first `j` bytes `b 0`, …, `b (j - 1)` assembled little-endian into `n` bits, the way
lean-x86's `Mem_Fetch` assembles them (one `setSlice` per byte). -/
def immPartial {n : Nat} (b : Nat → BitVec 8) : Nat → BitVec n
  | 0 => 0
  | j + 1 => X86.Runtime.setSlice (immPartial b j) (8 * j) 8 (b j)

/-- The unwritten-bits mask after `j` bytes. -/
def maskPartial (n : Nat) : Nat → BitVec n
  | 0 => BitVec.allOnes n
  | j + 1 => X86.Runtime.setSlice (maskPartial n j) (8 * j) 8 0

/-- Writing byte `i` into the value assembled from bytes `0`, …, `i - 1` gives the value
assembled from bytes `0`, …, `i`. -/
theorem writeSlice_immPartial_run {σ : Type} {N : Int} (b : Nat → BitVec 8) (i : Nat)
    (hi : 8 * i + 8 ≤ N.toNat) (st : σ) :
    (X86.Runtime.InitializedBits.writeSlice
        (⟨immPartial b i, maskPartial N.toNat i⟩ : X86.Runtime.InitializedBits N) ((i : Int) * 8) 8
        (b i) : X86.Runtime.SpecM X86.Exception σ _).run st =
      (.ok ⟨immPartial b (i + 1), maskPartial N.toNat (i + 1)⟩, st) := by
  have h0 : 0 ≤ N := by omega
  have h1 : (0 : Int) ≤ (i : Int) * 8 := by omega
  have h2 : (i : Int) * 8 + 8 ≤ max N 0 := by omega
  have h3 : ((i : Int) * 8).toNat = 8 * i := by omega
  simp [x86_runtime, h0, h1, h2, h3, immPartial, maskPartial]

/-- lean-x86's `intRange 0 (m - 1)`, the indices of an `m`-byte loop. -/
theorem intRange_zero (m : Nat) (hi : Int) (h : hi = (m : Int) - 1) :
    X86.Runtime.intRange 0 hi = (List.range' 0 m).map (fun i : Nat => (0 : Int) + i) := by
  subst h
  simp only [x86_runtime, ← List.range_eq_range']
  congr
  omega

/-- `ip + i`, as `Mem_Fetch` computes the address of byte `i`. -/
theorem add_int_nat {σ : Type} (ip : BitVec 64) (i : Nat) (st : σ) :
    (liftM (Std.Bits.Add_int (n := 64) ip (i : Int)) :
      X86.Runtime.SpecM X86.Exception σ (BitVec 64)).run st = (.ok (ip + BitVec.ofNat 64 i), st) := by
  simp [x86_runtime, liftM, monadLift, MonadLift.monadLift, ExceptT.run, ExceptT.mk, pure,
    Except.mapError]
  rfl

-- The proof of `memFetch_run_imm` for one size: `nb` bytes, `n` bits. `Mem_Fetch`'s checks, the
-- loop (`specM_forIn_range'_run`, one `memFetch_byte_stages` per byte; byte 0 also records the physical
-- address and memory type for the trace), then the trace and the read of the assembled value.
set_option hygiene false in
local macro "fetch_tac " nb:num n:num : tactic => `(tactic| (
    unfold Mem_Fetch
    rw [accelerated_eq_self]
    unfold Mem_Fetch.source
    simp only [Int.cast_ofNat_Int, assert_of_true, Int.reduceLE, decide_true, ↓reduceIte, pure_bind,
      Int.reduceBEq, Bool.or_true, Bool.true_or, Nat.reduceDiv] at hlimit ⊢
    rw [specM_bind_run _ _ (hg _)]
    refine (specM_bind_run _ _ (value := $nb) rfl).trans ?_
    refine (specM_bind_run _ _
      (value := BitVec.add (BitVec.sub ip s.RIP) (BitVec.ofNat 64 $nb)) rfl).trans ?_
    have hlimit' : ¬X86.Runtime.Unsigned (BitVec.add (BitVec.sub ip s.RIP) (BitVec.ofNat 64 $nb)) > 15 := by
      change ¬(↑(BitVec.add (BitVec.sub ip s.RIP) (BitVec.ofNat 64 $nb)).toNat : Int) > 15
      omega
    simp only [hlimit', decide_false, Bool.false_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ (in64BitMode_of_userCodeSegment (s := afterFetches s k) h.cs h.efer.lma)).trans ?_
    simp only [↓reduceIte]
    rw [specM_bind_run _ _ (hg _)]
    rw [specM_bind_run _ _ hnull]
    refine (specM_bind_run _ _ (value := $nb) rfl).trans ?_
    rw [intRange_zero $nb _ (by decide)]
    obtain ⟨lg0, ln0, ph0, hc0, hl0, hp0, hb0⟩ :=
      memFetch_byte_stages s k (ip + BitVec.ofNat 64 0) (b 0) h (haddr 0 (by decide)) (hmem 0 (by decide))
    refine (specM_bind_run _ _ (specM_forIn_range'_run (fun i : Nat => (0 : Int) + i) _
      (fun i => ((⟨immPartial (fun j => (b j).toBitVec) i, maskPartial _ i⟩ : X86.Runtime.InitializedBits _),
        if i = 0 then X86.Runtime.InitializedBits.empty 64
          else X86.Runtime.InitializedBits.ofValue ph0.translation1.physical_address,
        if i = 0 then none else some ph0.translation1.memory_type))
      (fun i => afterFetches s (k + i)) $nb 0 ?_)).trans ?_
    · intro i _ hi
      obtain ⟨lg, ln, ph, hc, hl, hp, hb, hph⟩ : ∃ lg ln ph,
          (Create_Logical_Address (nullDataSegment userCodeSegment) (ip + BitVec.ofNat 64 i) 8).run
            (afterFetches s (k + i)) = (.ok lg, afterFetches s (k + i + 1)) ∧
          (Translate_Logical_To_Linear lg .Normal_Alignment userCodeSegment true).run
            (afterFetches s (k + i + 1)) = (.ok ln, afterFetches s (k + i + 1)) ∧
          (Translate_Linear_To_Physical ln .Memory_Execute).run (afterFetches s (k + i + 1)) =
            (.ok ph, afterFetches s (k + i + 1)) ∧
          (Physical_Mem_Fetch ph).run (afterFetches s (k + i + 1)) =
            (.ok (b i).toBitVec, afterFetches s (k + i + 1)) ∧ (i = 0 → ph = ph0) := by
        by_cases hi0 : i = 0
        · subst hi0
          exact ⟨lg0, ln0, ph0, hc0, hl0, hp0, hb0, fun _ => rfl⟩
        · obtain ⟨lg, ln, ph, hc, hl, hp, hb⟩ := memFetch_byte_stages s (k + i) (ip + BitVec.ofNat 64 i)
            (b i) h (haddr i (by omega)) (hmem i (by omega))
          exact ⟨lg, ln, ph, hc, hl, hp, hb, fun h => absurd h hi0⟩
      simp only [Int.zero_add]
      refine (specM_bind_run _ _ (add_int_nat ip i _)).trans ?_
      refine (specM_bind_run _ _ hc).trans ?_
      rw [specM_bind_run _ _ (hg _)]
      refine (specM_bind_run _ _ (s := afterFetches s (k + i + 1))
        (by change (Translate_Logical_To_Linear _ _ s.CS true).run _ = _; rw [h.cs]; exact hl)).trans ?_
      refine (specM_bind_run _ _ hp).trans ?_
      simp only [show (i : Int) * 8 ≤ $n - 8 by omega, decide_true, ↓reduceIte, pure_bind]
      refine (specM_bind_run _ _ hb).trans ?_
      refine (specM_bind_run _ _ (writeSlice_immPartial_run (N := $n) _ i (by simp; omega) _)).trans ?_
      by_cases hi0 : i = 0
      · subst hi0
        rw [hph rfl]
        rfl
      · simp [hi0]
        rfl
    · have hmask : maskPartial $n $nb = 0 := by decide
      simp [x86_runtime, X86.Runtime.readInitialized, X86.__Trace_Physical_Mem,
        liftNoSourceException_eq, hmask, bind, ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind,
        ExceptT.bindCont, pure, ExceptT.pure, StateT.pure, Bind.bind]
      rfl))

/--
Fetch of `n / 8` bytes (`n` = 8, 16, 32 or 64). On a `FetchReady` state that has already done
`k` fetches, if the bytes `b 0`, `b 1`, … are stored at `ip`, `ip + 1`, …, below 4 GiB, and
the fetch ends within lean-x86's 15-byte window from RIP, `Mem_Fetch ip n` returns them
assembled little-endian (`immPartial`) and uses up `n / 8` more fetches' oracle bits; nothing
else changes.
-/
theorem memFetch_run_imm [Bindings] (s : RamState) (k : Nat) (h : FetchReady s) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (ip : BitVec 64) (b : Nat → UInt8)
    (hlimit : (BitVec.add (BitVec.sub ip s.RIP) (BitVec.ofNat 64 (n / 8))).toNat ≤ 15)
    (haddr : ∀ j < n / 8, (ip + BitVec.ofNat 64 j).toNat < 2^32)
    (hmem : ∀ j < n / 8, s.external[ip + BitVec.ofNat 64 j]? = some (b j)) :
    (Mem_Fetch ip n).run (afterFetches s k) =
      (.ok (immPartial (fun j => (b j).toBitVec) (n / 8)), afterFetches s (k + n / 8)) := by
  have hg (state : RamState) :
      (get : X86.Runtime.SpecM X86.Exception RamState RamState).run state = (.ok state, state) := rfl
  have hnull : (liftM (Null_Segment (afterFetches s k).CS) :
      X86.Runtime.SpecM X86.Exception RamState X86.Helpers.Segment).run (afterFetches s k) =
        (.ok (nullDataSegment userCodeSegment), afterFetches s k) := by
    change (liftM (Null_Segment s.CS) : X86.Runtime.SpecM X86.Exception RamState X86.Helpers.Segment).run (afterFetches s k) = _
    rw [h.cs]; rfl
  rcases hn with rfl | rfl | rfl | rfl
  · fetch_tac 1 8
  · fetch_tac 2 16
  · fetch_tac 4 32
  · fetch_tac 8 64

/--
Fetch of one byte. On a `FetchReady` state that has already done `k` fetches, fetching the byte
at `ip` (below 4 GiB, within lean-x86's 15-byte instruction window from RIP) returns the byte
stored at `ip` and uses up one more fetch's oracle bits; nothing else changes.
-/
theorem memFetch_run [Bindings]
    (s : RamState) (k : Nat) (ip : BitVec 64) (byte : UInt8) (h : FetchReady s)
    (hlimit : (BitVec.add (BitVec.sub ip s.RIP) 1#64).toNat ≤ 15) (haddr : ip.toNat < 2^32)
    (hmem : s.external[ip]? = some byte) :
    (Mem_Fetch ip 8).run (afterFetches s k) = (.ok byte.toBitVec, afterFetches s (k + 1)) := by
  have := memFetch_run_imm s k h 8 (by decide) ip (fun _ => byte) hlimit
    (fun j hj => by simpa [show j = 0 by omega] using haddr)
    (fun j hj => by simpa [show j = 0 by omega] using hmem)
  simpa [immPartial, X86.Runtime.setSlice] using this

theorem afterFetches_zero (s : RamState) : afterFetches s 0 = s := by
  simp [afterFetches, oracleSkip]

theorem fetch_offset_limit (ip : BitVec 64) (i : Nat) (hi : i < 15) :
    (BitVec.add (BitVec.sub (ip + BitVec.ofNat 64 i) ip) 1#64).toNat ≤ 15 := by
  have hs : BitVec.sub (ip + BitVec.ofNat 64 i) ip = BitVec.ofNat 64 i := by
    exact (congrArg (fun x : BitVec 64 => BitVec.sub x ip) (BitVec.add_comm ip (BitVec.ofNat 64 i))).trans
      (BitVec.add_sub_cancel _ _)
  rw [hs]
  change ((BitVec.ofNat 64 i + 1#64 : BitVec 64)).toNat ≤ 15
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Byte `i` of a byte string at `r` that lies below 4 GiB has an address below 4 GiB. -/
theorem code_address (r : BitVec 64) {i len : Nat} (hr : r.toNat + len ≤ 2^32) (hi : i < len) :
    (BitVec.add r (BitVec.ofNat 64 i)).toNat < 2^32 := by
  have ho : i < 2^64 := by omega
  change (r + BitVec.ofNat 64 i).toNat < 2^32
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  omega

/-- `bytes` are stored in physical memory at `addr`, `addr + 1`, …. -/
def BytesAt (s : RamState) (addr : BitVec 64) (bytes : List UInt8) : Prop :=
  ∀ i (hi : i < bytes.length), s.external[addr + BitVec.ofNat 64 i]? = some bytes[i]

/-- `BytesAt` depends only on memory. -/
theorem BytesAt.of_external_eq {s t : RamState} (he : s.external = t.external) {addr : BitVec 64}
    {bytes : List UInt8} (h : BytesAt s addr bytes) : BytesAt t addr bytes := by
  unfold BytesAt; rw [← he]; exact h

/-- The first part of a byte string stored at `addr` is stored at `addr`. -/
theorem BytesAt.append_left {s : RamState} {addr : BitVec 64} {l₁ l₂ : List UInt8}
    (h : BytesAt s addr (l₁ ++ l₂)) : BytesAt s addr l₁ := fun i hi => by
  have := h i (by simp; omega)
  rwa [List.getElem_append_left hi] at this

/-- The second part of a byte string stored at `addr` is stored right after the first part. -/
theorem BytesAt.append_right {s : RamState} {addr : BitVec 64} {l₁ l₂ : List UInt8}
    (h : BytesAt s addr (l₁ ++ l₂)) : BytesAt s (addr + BitVec.ofNat 64 l₁.length) l₂ :=
  fun i hi => by
  have := h (l₁.length + i) (by simp; omega)
  rw [List.getElem_append_right (by omega), BitVec.ofNat_add, ← BitVec.add_assoc] at this
  simpa only [Nat.add_sub_cancel_left] using this

/--
The fetch lemma. If `bytes` are stored at RIP and lie below 4 GiB, and `k` bytes were already
fetched, fetching byte `i` of the instruction (one of the first 15, lean-x86's instruction-length
limit) returns `bytes[i]` and uses up one more fetch's oracle bits.

Only the fetched bytes need to lie below 4 GiB, not lean-x86's whole 15-byte window: `Mem_Fetch`
translates one address per byte, and the 15-byte limit is a check on the offset from RIP, not on
the address.
-/
theorem memFetch_run_of_bytesAt [Bindings]
    (s : RamState) (k : Nat) (h : FetchReady s) {bytes : List UInt8}
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (i : Nat)
    (hi : i < bytes.length) (h15 : i < 15) :
    (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 i)) 8).run (afterFetches s k) =
      (.ok bytes[i].toBitVec, afterFetches s (k + 1)) := by
  have haddr := code_address s.RIP hlow hi
  exact memFetch_run s k _ bytes[i] h (fetch_offset_limit s.RIP i h15) haddr (hcode i hi)

end X86Proofs
