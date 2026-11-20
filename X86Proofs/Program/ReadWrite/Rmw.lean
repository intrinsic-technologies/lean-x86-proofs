import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Step.Address
import X86Proofs.Program.Compose

/-!
# Read-modify-write memory operands, and memory reads with flags

The form-level results of the memory ALU forms and their step-level facts:

- `writeRmwOutputs t addr out oracleUsed nextIP`: a read-modify-write (`xor [mem], r`, `xor [mem], imm`):
  the read's bookkeeping (`dataAccess t "load"`), then `Next_IP`, the used oracle bits and the
  flags (`writeFlagsOutputs`), then the write's bookkeeping (`dataAccess … "store"`) and the memory write
  of `out.1` at `addr`.
- `writeRmwResult t addr v nextIP`: a read-modify-write that leaves the flags alone (`not [mem]`):
  the read's bookkeeping, `Next_IP`, then the write's bookkeeping and the memory write of `v`.
- A memory compare (`cmp [mem], imm`) ends in `writeFlagsOutputs (dataAccess t "load") f 0 nextIP`: the
  read's bookkeeping, then the flags; memory is untouched.

- `writeRmwRegOutputs t addr out oracleUsed nextIP r v`: a read-modify-write followed by a register
  write (`xadd [mem], r`; `cmpxchg [mem], r` when the comparison fails), with its facts
  `afterStep_rmwReg_rip`, `ReadyToStep.afterStep_rmwReg`, `AgreesExcept.afterStep_rmwReg` (the
  bytes, the register, the flags and RIP change), `Operand.read_afterStep_rmwReg_mem`,
  `Operand.read_afterStep_rmwReg_reg` and `mem_components_rmwReg`; `In64BitMode.afterRmw` for a
  register write after the memory write.
- `writeRmwRegResult t addr v nextIP r w`: a read-modify-write without flags followed by a
  register write (`xchg [mem], r`), with the same facts (`…_rmwRegResult…`; the bytes, the register
  and RIP change) and `In64BitMode.afterRmwResult`.
- `writeRmwRegPairOutputs t addr out oracleUsed nextIP r₁ v₁ r₂ v₂`: the same with two register
  writes (`cmpxchg8b [mem]` when the comparison fails: EDX and EAX), with the same facts
  (`…_rmwRegPair…`; `Operand.read_afterStep_rmwRegPair_reg₁`, `…_reg₂` for distinct registers).

For each: RIP after the step (`afterStep_rmw_rip`, `afterStep_rmwResult_rip`,
`afterStep_loadWriteFlagsOutputs_rip`), preservation of `ReadyToStep` (`ReadyToStep.afterStep_rmw`,
`ReadyToStep.afterStep_rmwResult`: the written bytes must lie below 4 GiB and miss the page-table
frames; `ReadyToStep.afterStep_loadWriteFlagsOutputs`) and the frame (`AgreesExcept.afterStep_rmw`:
only the written bytes, the flags and RIP change; `AgreesExcept.afterStep_rmwResult`: only the
written bytes and RIP; `AgreesExcept.afterStep_loadWriteFlagsOutputs`).

Preconditions: a read-modify-write uses the store's `StorePre` (`Program/ReadWrite/Store.lean`;
`MemWritable.readable` gives the read side); a memory compare only reads, `LoadPre`
(`Program/ReadWrite/Load.lean`). `Effect.avoids_of_mem`: an effect whose only memory component is the
written range avoids code that range is apart from (as `Effect.avoids_of_components_mem_rip`,
with the flags too). `RmwPre p am len codeLen`: the precondition of a read-modify-write of an
`AddrMode` operand (`StorePre` at `am.addr s (p + codeLen)`); `rmw_facts` gives its facts at the
step theorems' address, `mem_components_rmw` (`mem_components_rmwResult` without flags) the
memory component of such an effect. `SegRmwPre p r base am len codeLen`: the same for an operand
with a segment override `r` (FS or GS) with base `base` (`SegStorePre` at
`base + am.addr s (p + codeLen)`); `segRmw_facts` gives its facts. `Rmw32Pre`, `rmw32_facts`: the
same at address size 32 (a `67` prefix, `AddrMode.addr32`). `LockedRmwPre` and
`SegLockedRmwPre` (and `LockedRmw32Pre`, at address size 32): the same for a locked
read-modify-write (LOCK prefix, XCHG with memory), with
`LockReady` for the operand (`lockedRmw_lock`, `segLockedRmw_lock` at the step theorems'
address).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- An effect that writes `len` bytes at `addr` (and registers, flags, RIP) avoids the code at
`p` if the ranges are disjoint. -/
theorem Effect.avoids_of_mem {e : Effect} {addr p : BitVec 64} {len : Nat} {bytes : List UInt8}
    (hc : ∀ c ∈ e.components, c.isMem = true → c = .mem addr len)
    {codeLen : Nat} (hd : RangeApart addr len p codeLen) (hl : bytes.length = codeLen) :
    e.Avoids (codeRange p bytes) := by
  subst hl
  intro x hx c hcm hcov
  cases c with
  | mem a l =>
    obtain ⟨rfl, rfl⟩ := Component.mem.inj (hc _ hcm rfl)
    obtain ⟨i, hi, hxi⟩ := hcov
    obtain ⟨j, hj, hxj⟩ := exists_of_mem_codeRange hx
    exact hd i hi j hj (hxi.symm.trans hxj)
  | _ => exact hcov

/-! ### Read-modify-write -/

/--
Form-level result of a read-modify-write of `n` bits at `addr`, from the state `t` after the
address computation: the read's bookkeeping, `Next_IP := nextIP`, `oracleUsed` oracle bits used
up and the flags `out.2` stored, then the write's bookkeeping and the bytes of `out.1` stored at
`addr`.
-/
def writeRmwOutputs {n : Nat} (t : RamState) (addr : BitVec 64) (out : BitVec n × StatusFlags)
    (oracleUsed : Nat) (nextIP : BitVec 64) : RamState :=
  (Operand.mem addr : Operand n).write
    (dataAccess (writeFlagsOutputs (dataAccess t "load") out.2 oracleUsed nextIP) "store") out.1

/-- A read-modify-write leaves the code segment and EFER alone, so 64-bit mode survives it (for a
register write after it, XADD); stated for `writeRmwOutputs` unfolded, as a form reaches it. -/
theorem In64BitMode.afterRmw {n : Nat} {t : RamState} (h : In64BitMode t) (addr : BitVec 64)
    (f : StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) (v : BitVec n) :
    In64BitMode ((Operand.mem addr : Operand n).write
      (dataAccess (writeFlagsOutputs (dataAccess t "load") f oracleUsed nextIP) "store") v) :=
  h.of_cs_lma_eq (by simp only [writeFlagsOutputs, setFlags, dataAccess, Operand.write])
    (by simp only [writeFlagsOutputs, setFlags, dataAccess, Operand.write])

theorem afterStep_rmw_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    {n : Nat} (addr : BitVec 64) (out : RamState → BitVec n × StatusFlags) (oracleUsed : Nat)
    (nextIP : BitVec 64) :
    (afterStep s length fun t => writeRmwOutputs t addr (out t) oracleUsed nextIP).RIP = nextIP := by
  simp [afterStep, finishStep, writeRmwOutputs, writeFlagsOutputs, setFlags, Operand.write, dataAccess,
    afterFetches, beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

theorem afterStep_rmw_external (s : RamState) (length : Nat) {n : Nat} (addr : BitVec 64)
    (out : RamState → BitVec n × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    (afterStep s length fun t => writeRmwOutputs t addr (out t) oracleUsed nextIP).external =
      memStore s.external addr (out (afterFetches (beforeFetch s) (length + 1))).1 := rfl

/-- After a read-modify-write, the operand holds the written value. -/
theorem Operand.read_afterStep_rmw (s : RamState) (length : Nat) {n : Nat} (hn : n ≤ 128)
    (h8 : n % 8 = 0) (addr : BitVec 64) (out : RamState → BitVec n × StatusFlags) (oracleUsed : Nat)
    (nextIP : BitVec 64) :
    (Operand.mem addr : Operand n).read
        (afterStep s length fun t => writeRmwOutputs t addr (out t) oracleUsed nextIP) =
      (out (afterFetches (beforeFetch s) (length + 1))).1 := by
  show memLoad _ addr n = _
  rw [afterStep_rmw_external]
  exact memLoad_memStore _ _ h8 (by omega) _

/--
Preservation for a read-modify-write: if the written bytes lie below 4 GiB and outside the
page-table frames, the state after the step is ready to step again. Only memory, the flags, the
oracle, the trace, `Next_IP`, RIP and per-step bookkeeping change.
-/
theorem ReadyToStep.afterStep_rmw [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (addr : BitVec 64) (out : RamState → BitVec n × StatusFlags)
    (oracleUsed : Nat) (nextIP : BitVec 64) (hlow : addr.toNat + n / 8 ≤ 2^32)
    (htables : PageTableEntriesApart addr.toNat (n / 8)) :
    ReadyToStep (afterStep s length fun t => writeRmwOutputs t addr (out t) oracleUsed nextIP) := by
  have hst : SameControls s (afterStep s length fun t => writeRmwOutputs t addr (out t) oracleUsed
      nextIP) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  have hmem : Prelude.IdentityMappedMemory
      (afterStep s length fun t => writeRmwOutputs t addr (out t) oracleUsed nextIP) := by
    refine ⟨h.memory.cr3, ?_⟩
    rw [afterStep_rmw_external]
    exact IdentityPageTableMemory.memStore h.memory.tables _ _ hlow htables
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass, hc.debug,
      hc.aet⟩,
    hmem,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, StatusFlags.trapFlagClear_store _ hr.tf, StatusFlags.resumeFlagClear_store _ hr.rf,
      hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-- A read-modify-write of `n` bits at `addr` changes only those bytes, the flags and RIP
(besides the per-step bookkeeping). -/
theorem AgreesExcept.afterStep_rmw (s : RamState) (length : Nat) {n : Nat} (addr : BitVec 64)
    (out : RamState → BitVec n × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    AgreesExcept [.mem addr (n / 8), .flags, .rip] s
      (afterStep s length fun t => writeRmwOutputs t addr (out t) oracleUsed nextIP) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r => rfl
    | flags => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem a l => exact absurd hm (by simp [Component.isMem])
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => exact dfBit_store _ _
  · rw [afterStep_rmw_external]
    apply memStore_getElem?_of_ne
    intro i hi he
    exact hx (.mem addr (n / 8)) (by simp) ⟨i, hi, he.symm⟩
  · simp only [fixedPart, afterStep, finishStep, writeRmwOutputs, writeFlagsOutputs, Operand.write, setFlags,
      dataAccess, afterFetches, beforeFetch, resetStepFields, clearStatusFlags_store]
  · rw [afterStep_rmw_external]
    exact memStore_isSome _ _ _ x hx

/-! ### Memory read with flags (compare) -/

theorem afterStep_loadWriteFlagsOutputs_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (f : RamState → StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    (afterStep s length fun t => writeFlagsOutputs (dataAccess t "load") (f t) oracleUsed nextIP).RIP =
      nextIP := by
  simp [afterStep, finishStep, writeFlagsOutputs, setFlags, dataAccess, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- Preservation for a memory compare: only the flags, the oracle, the trace, `Next_IP`, RIP and
per-step bookkeeping change. -/
theorem ReadyToStep.afterStep_loadWriteFlagsOutputs [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (f : RamState → StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t =>
      writeFlagsOutputs (dataAccess t "load") (f t) oracleUsed nextIP) := by
  have hst : SameControls s (afterStep s length fun t =>
      writeFlagsOutputs (dataAccess t "load") (f t) oracleUsed nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass, hc.debug,
      hc.aet⟩,
    ⟨h.memory.cr3, h.memory.tables⟩,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, StatusFlags.trapFlagClear_store _ hr.tf, StatusFlags.resumeFlagClear_store _ hr.rf,
      hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-- A memory compare changes only the flags and RIP (besides the per-step bookkeeping). -/
theorem AgreesExcept.afterStep_loadWriteFlagsOutputs (s : RamState) (length : Nat) (f : RamState → StatusFlags)
    (oracleUsed : Nat) (nextIP : BitVec 64) :
    AgreesExcept [.flags, .rip] s
      (afterStep s length fun t => writeFlagsOutputs (dataAccess t "load") (f t) oracleUsed nextIP) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r => rfl
    | flags => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem addr len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => exact dfBit_store _ _
  · simp only [fixedPart, afterStep, finishStep, writeFlagsOutputs, setFlags, dataAccess, afterFetches,
      beforeFetch, resetStepFields, clearStatusFlags_store]

/-! ### Read-modify-write without flags -/

/--
Form-level result of a read-modify-write of `n` bits at `addr` that leaves the flags alone (`not
[mem]`), from the state `t` after the address computation: the read's bookkeeping,
`Next_IP := nextIP`, then the write's bookkeeping and the bytes of `v` stored at `addr`.
-/
def writeRmwResult {n : Nat} (t : RamState) (addr : BitVec 64) (v : BitVec n) (nextIP : BitVec 64) :
    RamState :=
  (Operand.mem addr : Operand n).write
    (dataAccess { dataAccess t "load" with Next_IP := nextIP } "store") v

theorem afterStep_rmwResult_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    {n : Nat} (addr : BitVec 64) (v : RamState → BitVec n) (nextIP : BitVec 64) :
    (afterStep s length fun t => writeRmwResult t addr (v t) nextIP).RIP = nextIP := by
  simp [afterStep, finishStep, writeRmwResult, Operand.write, dataAccess, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

theorem afterStep_rmwResult_external (s : RamState) (length : Nat) {n : Nat} (addr : BitVec 64)
    (v : RamState → BitVec n) (nextIP : BitVec 64) :
    (afterStep s length fun t => writeRmwResult t addr (v t) nextIP).external =
      memStore s.external addr (v (afterFetches (beforeFetch s) (length + 1))) := rfl

/-- After a read-modify-write without flags, the operand holds the written value. -/
theorem Operand.read_afterStep_rmwResult (s : RamState) (length : Nat) {n : Nat} (hn : n ≤ 64)
    (h8 : n % 8 = 0) (addr : BitVec 64) (v : RamState → BitVec n) (nextIP : BitVec 64) :
    (Operand.mem addr : Operand n).read
        (afterStep s length fun t => writeRmwResult t addr (v t) nextIP) =
      v (afterFetches (beforeFetch s) (length + 1)) := by
  show memLoad _ addr n = _
  rw [afterStep_rmwResult_external]
  exact memLoad_memStore _ _ h8 (by omega) _

/--
Preservation for a read-modify-write without flags: if the written bytes lie below 4 GiB and
outside the page-table frames, the state after the step is ready to step again. Only memory, the
oracle, the trace, `Next_IP`, RIP and per-step bookkeeping change.
-/
theorem ReadyToStep.afterStep_rmwResult [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (addr : BitVec 64) (v : RamState → BitVec n) (nextIP : BitVec 64)
    (hlow : addr.toNat + n / 8 ≤ 2^32)
    (htables : PageTableEntriesApart addr.toNat (n / 8)) :
    ReadyToStep (afterStep s length fun t => writeRmwResult t addr (v t) nextIP) := by
  have hst : SameControls s (afterStep s length fun t => writeRmwResult t addr (v t) nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  have hmem : Prelude.IdentityMappedMemory
      (afterStep s length fun t => writeRmwResult t addr (v t) nextIP) := by
    refine ⟨h.memory.cr3, ?_⟩
    rw [afterStep_rmwResult_external]
    exact IdentityPageTableMemory.memStore h.memory.tables _ _ hlow htables
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass,
      hc.debug, hc.aet⟩,
    hmem,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, hr.tf, hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-- A read-modify-write without flags of `n` bits at `addr` changes only those bytes and RIP
(besides the per-step bookkeeping). -/
theorem AgreesExcept.afterStep_rmwResult (s : RamState) (length : Nat) {n : Nat} (addr : BitVec 64)
    (v : RamState → BitVec n) (nextIP : BitVec 64) :
    AgreesExcept [.mem addr (n / 8), .rip] s
      (afterStep s length fun t => writeRmwResult t addr (v t) nextIP) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r => rfl
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem a l => exact absurd hm (by simp [Component.isMem])
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => rfl
  · rw [afterStep_rmwResult_external]
    apply memStore_getElem?_of_ne
    intro i hi he
    exact hx (.mem addr (n / 8)) (by simp) ⟨i, hi, he.symm⟩
  · simp only [fixedPart, afterStep, finishStep, writeRmwResult, Operand.write, dataAccess,
      afterFetches, beforeFetch, resetStepFields]
  · rw [afterStep_rmwResult_external]
    exact memStore_isSome _ _ _ x hx

/-- The only memory component of `[.mem a l, .rip]` is `.mem a l`. -/
theorem mem_components_rmwResult (a : BitVec 64) (l : Nat) :
    ∀ c ∈ [Component.mem a l, .rip], c.isMem = true → c = .mem a l := by
  intro c hc hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> simp_all [Component.isMem]

/-! ### Read-modify-write and a register -/

/--
Form-level result of a read-modify-write of `n` bits at `addr` followed by a register write (XADD
`[mem], r`: the old value to `r`; CMPXCHG `[mem], r` when the comparison fails: the old value to
the accumulator): `writeRmwOutputs`, then register `r` set to `v` (`n` bits, merged as
`Operand.write` does).
-/
def writeRmwRegOutputs {n : Nat} (t : RamState) (addr : BitVec 64) (out : BitVec n × StatusFlags)
    (oracleUsed : Nat) (nextIP : BitVec 64) (r : BitVec 5) (v : BitVec n) : RamState :=
  (Operand.reg r : Operand n).write (writeRmwOutputs t addr out oracleUsed nextIP) v

theorem afterStep_rmwReg_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    {n : Nat} (addr : BitVec 64) (out : RamState → BitVec n × StatusFlags) (oracleUsed : Nat)
    (nextIP : BitVec 64) (r : BitVec 5) (v : RamState → BitVec n) :
    (afterStep s length fun t =>
      writeRmwRegOutputs t addr (out t) oracleUsed nextIP r (v t)).RIP = nextIP := by
  simp [afterStep, finishStep, writeRmwRegOutputs, writeRmwOutputs, writeFlagsOutputs, setFlags,
    Operand.write, dataAccess, afterFetches, beforeFetch, resetStepFields, h.ready.repeatClear,
    h.ready.msr]

theorem afterStep_rmwReg_external (s : RamState) (length : Nat) {n : Nat} (addr : BitVec 64)
    (out : RamState → BitVec n × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64)
    (r : BitVec 5) (v : RamState → BitVec n) :
    (afterStep s length fun t =>
      writeRmwRegOutputs t addr (out t) oracleUsed nextIP r (v t)).external =
      memStore s.external addr (out (afterFetches (beforeFetch s) (length + 1))).1 := rfl

/-- After a read-modify-write and a register write, the memory operand holds the written
value. -/
theorem Operand.read_afterStep_rmwReg_mem (s : RamState) (length : Nat) {n : Nat} (hn : n ≤ 64)
    (h8 : n % 8 = 0) (addr : BitVec 64) (out : RamState → BitVec n × StatusFlags)
    (oracleUsed : Nat) (nextIP : BitVec 64) (r : BitVec 5) (v : RamState → BitVec n) :
    (Operand.mem addr : Operand n).read
        (afterStep s length fun t => writeRmwRegOutputs t addr (out t) oracleUsed nextIP r (v t)) =
      (out (afterFetches (beforeFetch s) (length + 1))).1 := by
  show memLoad _ addr n = _
  rw [afterStep_rmwReg_external]
  exact memLoad_memStore _ _ h8 (by omega) _

/-- After a read-modify-write and a write of register `r`, the full register `r` is the written
value merged into its old value. -/
theorem Operand.read_afterStep_rmwReg_reg (s : RamState) (length : Nat) {n : Nat}
    (addr : BitVec 64) (out : RamState → BitVec n × StatusFlags) (oracleUsed : Nat)
    (nextIP : BitVec 64) (r : BitVec 5) (v : RamState → BitVec n) :
    (Operand.reg r : Operand 64).read
        (afterStep s length fun t => writeRmwRegOutputs t addr (out t) oracleUsed nextIP r (v t)) =
      mergeGPR n (v (afterFetches (beforeFetch s) (length + 1)))
        ((Operand.reg r : Operand 64).read s) := by
  rw [Operand.read_afterStep]
  have hold : (Operand.reg r : Operand 64).read
      (writeRmwOutputs (afterFetches (beforeFetch s) (length + 1)) addr
        (out (afterFetches (beforeFetch s) (length + 1))) oracleUsed nextIP) =
      (Operand.reg r : Operand 64).read s := by
    rw [← Operand.read_beforeFetch s, ← Operand.read_afterFetches (beforeFetch s) (length + 1)]
    rfl
  rw [← hold]
  simp [writeRmwRegOutputs, Operand.write, Operand.read]

/--
Preservation for a read-modify-write and a register write: if the written bytes lie below 4 GiB and
outside the page-table frames, the state after the step is ready to step again.
-/
theorem ReadyToStep.afterStep_rmwReg [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (addr : BitVec 64) (out : RamState → BitVec n × StatusFlags)
    (oracleUsed : Nat) (nextIP : BitVec 64) (r : BitVec 5) (v : RamState → BitVec n)
    (hlow : addr.toNat + n / 8 ≤ 2^32)
    (htables : PageTableEntriesApart addr.toNat (n / 8)) :
    ReadyToStep (afterStep s length fun t =>
      writeRmwRegOutputs t addr (out t) oracleUsed nextIP r (v t)) := by
  have hst : SameControls s (afterStep s length fun t =>
      writeRmwRegOutputs t addr (out t) oracleUsed nextIP r (v t)) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  have hmem : Prelude.IdentityMappedMemory
      (afterStep s length fun t =>
        writeRmwRegOutputs t addr (out t) oracleUsed nextIP r (v t)) := by
    refine ⟨h.memory.cr3, ?_⟩
    rw [afterStep_rmwReg_external]
    exact IdentityPageTableMemory.memStore h.memory.tables _ _ hlow htables
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass,
      hc.debug, hc.aet⟩,
    hmem,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, StatusFlags.trapFlagClear_store _ hr.tf, StatusFlags.resumeFlagClear_store _ hr.rf,
      hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-- A read-modify-write of `n` bits at `addr` and a write of register `r` change only those bytes,
`r`, the flags and RIP (besides the per-step bookkeeping). -/
theorem AgreesExcept.afterStep_rmwReg (s : RamState) (length : Nat) {n : Nat} (addr : BitVec 64)
    (out : RamState → BitVec n × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64)
    (r : BitVec 5) (v : RamState → BitVec n) :
    AgreesExcept [.mem addr (n / 8), .reg r, .flags, .rip] s
      (afterStep s length fun t =>
        writeRmwRegOutputs t addr (out t) oracleUsed nextIP r (v t)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r' =>
      have hne : r ≠ r' := fun h => hc (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)
      show (Operand.reg r' : Operand 64).read _ = (Operand.reg r' : Operand 64).read _
      rw [Operand.read_afterStep, writeRmwRegOutputs, Operand.read_write_reg_of_ne _ hne,
        ← Operand.read_beforeFetch s, ← Operand.read_afterFetches (beforeFetch s) (length + 1)]
      rfl
    | flags => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem a l => exact absurd hm (by simp [Component.isMem])
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => exact dfBit_store _ _
  · rw [afterStep_rmwReg_external]
    apply memStore_getElem?_of_ne
    intro i hi he
    exact hx (.mem addr (n / 8)) (by simp) ⟨i, hi, he.symm⟩
  · simp only [fixedPart, afterStep, finishStep, writeRmwRegOutputs, writeRmwOutputs,
      writeFlagsOutputs, Operand.write, setFlags, dataAccess, afterFetches, beforeFetch,
      resetStepFields, clearStatusFlags_store]
  · rw [afterStep_rmwReg_external]
    exact memStore_isSome _ _ _ x hx

/-- The only memory component of `[.mem a l, .reg r, .flags, .rip]` is `.mem a l`. -/
theorem mem_components_rmwReg (a : BitVec 64) (l : Nat) (r : BitVec 5) :
    ∀ c ∈ [Component.mem a l, .reg r, .flags, .rip], c.isMem = true → c = .mem a l := by
  intro c hc hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> simp_all [Component.isMem]

/-! ### Read-modify-write without flags and a register -/

/--
Form-level result of a read-modify-write of `n` bits at `addr` that leaves the flags alone,
followed by a register write (XCHG `[mem], r`: the old value to `r`): `writeRmwResult`, then
register `r` set to `w` (`n` bits, merged as `Operand.write` does).
-/
def writeRmwRegResult {n : Nat} (t : RamState) (addr : BitVec 64) (v : BitVec n)
    (nextIP : BitVec 64) (r : BitVec 5) (w : BitVec n) : RamState :=
  (Operand.reg r : Operand n).write (writeRmwResult t addr v nextIP) w

/-- A read-modify-write without flags leaves the code segment and EFER alone, so 64-bit mode
survives it (for a register write after it, XCHG); stated for `writeRmwResult` unfolded, as a form
reaches it. -/
theorem In64BitMode.afterRmwResult {n : Nat} {t : RamState} (h : In64BitMode t)
    (addr : BitVec 64) (nextIP : BitVec 64) (v : BitVec n) :
    In64BitMode ((Operand.mem addr : Operand n).write
      (dataAccess { dataAccess t "load" with Next_IP := nextIP } "store") v) :=
  h.of_cs_lma_eq (by simp only [dataAccess, Operand.write])
    (by simp only [dataAccess, Operand.write])

theorem afterStep_rmwRegResult_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    {n : Nat} (addr : BitVec 64) (v : RamState → BitVec n) (nextIP : BitVec 64) (r : BitVec 5)
    (w : RamState → BitVec n) :
    (afterStep s length fun t => writeRmwRegResult t addr (v t) nextIP r (w t)).RIP = nextIP := by
  simp [afterStep, finishStep, writeRmwRegResult, writeRmwResult, Operand.write, dataAccess,
    afterFetches, beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

theorem afterStep_rmwRegResult_external (s : RamState) (length : Nat) {n : Nat} (addr : BitVec 64)
    (v : RamState → BitVec n) (nextIP : BitVec 64) (r : BitVec 5) (w : RamState → BitVec n) :
    (afterStep s length fun t => writeRmwRegResult t addr (v t) nextIP r (w t)).external =
      memStore s.external addr (v (afterFetches (beforeFetch s) (length + 1))) := rfl

/-- After a read-modify-write without flags and a register write, the memory operand holds the
written value. -/
theorem Operand.read_afterStep_rmwRegResult_mem (s : RamState) (length : Nat) {n : Nat}
    (hn : n ≤ 64) (h8 : n % 8 = 0) (addr : BitVec 64) (v : RamState → BitVec n)
    (nextIP : BitVec 64) (r : BitVec 5) (w : RamState → BitVec n) :
    (Operand.mem addr : Operand n).read
        (afterStep s length fun t => writeRmwRegResult t addr (v t) nextIP r (w t)) =
      v (afterFetches (beforeFetch s) (length + 1)) := by
  show memLoad _ addr n = _
  rw [afterStep_rmwRegResult_external]
  exact memLoad_memStore _ _ h8 (by omega) _

/-- After a read-modify-write without flags and a write of register `r`, the full register `r` is
the written value merged into its old value. -/
theorem Operand.read_afterStep_rmwRegResult_reg (s : RamState) (length : Nat) {n : Nat}
    (addr : BitVec 64) (v : RamState → BitVec n) (nextIP : BitVec 64) (r : BitVec 5)
    (w : RamState → BitVec n) :
    (Operand.reg r : Operand 64).read
        (afterStep s length fun t => writeRmwRegResult t addr (v t) nextIP r (w t)) =
      mergeGPR n (w (afterFetches (beforeFetch s) (length + 1)))
        ((Operand.reg r : Operand 64).read s) := by
  rw [Operand.read_afterStep]
  have hold : (Operand.reg r : Operand 64).read
      (writeRmwResult (afterFetches (beforeFetch s) (length + 1)) addr
        (v (afterFetches (beforeFetch s) (length + 1))) nextIP) =
      (Operand.reg r : Operand 64).read s := by
    rw [← Operand.read_beforeFetch s, ← Operand.read_afterFetches (beforeFetch s) (length + 1)]
    rfl
  rw [← hold]
  simp [writeRmwRegResult, Operand.write, Operand.read]

/--
Preservation for a read-modify-write without flags and a register write: if the written bytes lie
below 4 GiB and outside the page-table frames, the state after the step is ready to step again.
-/
theorem ReadyToStep.afterStep_rmwRegResult [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (addr : BitVec 64) (v : RamState → BitVec n) (nextIP : BitVec 64)
    (r : BitVec 5) (w : RamState → BitVec n)
    (hlow : addr.toNat + n / 8 ≤ 2^32)
    (htables : PageTableEntriesApart addr.toNat (n / 8)) :
    ReadyToStep (afterStep s length fun t => writeRmwRegResult t addr (v t) nextIP r (w t)) := by
  have hst : SameControls s
      (afterStep s length fun t => writeRmwRegResult t addr (v t) nextIP r (w t)) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  have hmem : Prelude.IdentityMappedMemory
      (afterStep s length fun t => writeRmwRegResult t addr (v t) nextIP r (w t)) := by
    refine ⟨h.memory.cr3, ?_⟩
    rw [afterStep_rmwRegResult_external]
    exact IdentityPageTableMemory.memStore h.memory.tables _ _ hlow htables
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass,
      hc.debug, hc.aet⟩,
    hmem,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, hr.tf, hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-- A read-modify-write without flags of `n` bits at `addr` and a write of register `r` change only
those bytes, `r` and RIP (besides the per-step bookkeeping). -/
theorem AgreesExcept.afterStep_rmwRegResult (s : RamState) (length : Nat) {n : Nat}
    (addr : BitVec 64) (v : RamState → BitVec n) (nextIP : BitVec 64) (r : BitVec 5)
    (w : RamState → BitVec n) :
    AgreesExcept [.mem addr (n / 8), .reg r, .rip] s
      (afterStep s length fun t => writeRmwRegResult t addr (v t) nextIP r (w t)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r' =>
      have hne : r ≠ r' := fun h => hc (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)
      show (Operand.reg r' : Operand 64).read _ = (Operand.reg r' : Operand 64).read _
      rw [Operand.read_afterStep, writeRmwRegResult, Operand.read_write_reg_of_ne _ hne,
        ← Operand.read_beforeFetch s, ← Operand.read_afterFetches (beforeFetch s) (length + 1)]
      rfl
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem a l => exact absurd hm (by simp [Component.isMem])
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => rfl
  · rw [afterStep_rmwRegResult_external]
    apply memStore_getElem?_of_ne
    intro i hi he
    exact hx (.mem addr (n / 8)) (by simp) ⟨i, hi, he.symm⟩
  · simp only [fixedPart, afterStep, finishStep, writeRmwRegResult, writeRmwResult, Operand.write,
      dataAccess, afterFetches, beforeFetch, resetStepFields]
  · rw [afterStep_rmwRegResult_external]
    exact memStore_isSome _ _ _ x hx

/-- The only memory component of `[.mem a l, .reg r, .rip]` is `.mem a l`. -/
theorem mem_components_rmwRegResult (a : BitVec 64) (l : Nat) (r : BitVec 5) :
    ∀ c ∈ [Component.mem a l, .reg r, .rip], c.isMem = true → c = .mem a l := by
  intro c hc hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> simp_all [Component.isMem]

/-! ### Read-modify-write and two registers -/

/--
Form-level result of a read-modify-write of `n` bits at `addr` followed by two register writes
(CMPXCHG8B when the comparison fails: EDX and EAX get the halves of the old value):
`writeRmwOutputs`, then register `r₁` set to `v₁` and register `r₂` to `v₂` (`m` bits each,
merged as `Operand.write` does).
-/
def writeRmwRegPairOutputs {n m : Nat} (t : RamState) (addr : BitVec 64)
    (out : BitVec n × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) (r₁ : BitVec 5)
    (v₁ : BitVec m) (r₂ : BitVec 5) (v₂ : BitVec m) : RamState :=
  (Operand.reg r₂ : Operand m).write
    ((Operand.reg r₁ : Operand m).write (writeRmwOutputs t addr out oracleUsed nextIP) v₁) v₂

theorem afterStep_rmwRegPair_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    {n m : Nat} (addr : BitVec 64) (out : RamState → BitVec n × StatusFlags) (oracleUsed : Nat)
    (nextIP : BitVec 64) (r₁ : BitVec 5) (v₁ : RamState → BitVec m) (r₂ : BitVec 5)
    (v₂ : RamState → BitVec m) :
    (afterStep s length fun t =>
      writeRmwRegPairOutputs t addr (out t) oracleUsed nextIP r₁ (v₁ t) r₂ (v₂ t)).RIP =
      nextIP := by
  simp [afterStep, finishStep, writeRmwRegPairOutputs, writeRmwOutputs, writeFlagsOutputs,
    setFlags, Operand.write, dataAccess, afterFetches, beforeFetch, resetStepFields,
    h.ready.repeatClear, h.ready.msr]

theorem afterStep_rmwRegPair_external (s : RamState) (length : Nat) {n m : Nat}
    (addr : BitVec 64) (out : RamState → BitVec n × StatusFlags) (oracleUsed : Nat)
    (nextIP : BitVec 64) (r₁ : BitVec 5) (v₁ : RamState → BitVec m) (r₂ : BitVec 5)
    (v₂ : RamState → BitVec m) :
    (afterStep s length fun t =>
      writeRmwRegPairOutputs t addr (out t) oracleUsed nextIP r₁ (v₁ t) r₂ (v₂ t)).external =
      memStore s.external addr (out (afterFetches (beforeFetch s) (length + 1))).1 := rfl

/-- After a read-modify-write and two register writes, the memory operand holds the written
value. -/
theorem Operand.read_afterStep_rmwRegPair_mem (s : RamState) (length : Nat) {n m : Nat}
    (hn : n ≤ 128) (h8 : n % 8 = 0) (addr : BitVec 64) (out : RamState → BitVec n × StatusFlags)
    (oracleUsed : Nat) (nextIP : BitVec 64) (r₁ : BitVec 5) (v₁ : RamState → BitVec m)
    (r₂ : BitVec 5) (v₂ : RamState → BitVec m) :
    (Operand.mem addr : Operand n).read
        (afterStep s length fun t =>
          writeRmwRegPairOutputs t addr (out t) oracleUsed nextIP r₁ (v₁ t) r₂ (v₂ t)) =
      (out (afterFetches (beforeFetch s) (length + 1))).1 := by
  show memLoad _ addr n = _
  rw [afterStep_rmwRegPair_external]
  exact memLoad_memStore _ _ h8 (by omega) _

/-- After a read-modify-write and writes of registers `r₁` and `r₂`, the full register `r₂` is its
written value merged into its old value. -/
theorem Operand.read_afterStep_rmwRegPair_reg₂ (s : RamState) (length : Nat) {n m : Nat}
    (addr : BitVec 64) (out : RamState → BitVec n × StatusFlags) (oracleUsed : Nat)
    (nextIP : BitVec 64) (r₁ : BitVec 5) (v₁ : RamState → BitVec m) (r₂ : BitVec 5)
    (v₂ : RamState → BitVec m) (hne : r₁ ≠ r₂) :
    (Operand.reg r₂ : Operand 64).read
        (afterStep s length fun t =>
          writeRmwRegPairOutputs t addr (out t) oracleUsed nextIP r₁ (v₁ t) r₂ (v₂ t)) =
      mergeGPR m (v₂ (afterFetches (beforeFetch s) (length + 1)))
        ((Operand.reg r₂ : Operand 64).read s) := by
  rw [Operand.read_afterStep]
  have hold : (Operand.reg r₂ : Operand 64).read
      ((Operand.reg r₁ : Operand m).write
        (writeRmwOutputs (afterFetches (beforeFetch s) (length + 1)) addr
          (out (afterFetches (beforeFetch s) (length + 1))) oracleUsed nextIP)
        (v₁ (afterFetches (beforeFetch s) (length + 1)))) =
      (Operand.reg r₂ : Operand 64).read s := by
    rw [Operand.read_write_reg_of_ne _ hne, ← Operand.read_beforeFetch s,
      ← Operand.read_afterFetches (beforeFetch s) (length + 1)]
    rfl
  rw [← hold]
  simp [writeRmwRegPairOutputs, Operand.write, Operand.read]

/-- After a read-modify-write and writes of registers `r₁` and `r₂ ≠ r₁`, the full register `r₁`
is its written value merged into its old value. -/
theorem Operand.read_afterStep_rmwRegPair_reg₁ (s : RamState) (length : Nat) {n m : Nat}
    (addr : BitVec 64) (out : RamState → BitVec n × StatusFlags) (oracleUsed : Nat)
    (nextIP : BitVec 64) (r₁ : BitVec 5) (v₁ : RamState → BitVec m) (r₂ : BitVec 5)
    (v₂ : RamState → BitVec m) (hne : r₁ ≠ r₂) :
    (Operand.reg r₁ : Operand 64).read
        (afterStep s length fun t =>
          writeRmwRegPairOutputs t addr (out t) oracleUsed nextIP r₁ (v₁ t) r₂ (v₂ t)) =
      mergeGPR m (v₁ (afterFetches (beforeFetch s) (length + 1)))
        ((Operand.reg r₁ : Operand 64).read s) := by
  rw [Operand.read_afterStep, writeRmwRegPairOutputs, Operand.read_write_reg_of_ne _ hne.symm]
  have hold : (Operand.reg r₁ : Operand 64).read
      (writeRmwOutputs (afterFetches (beforeFetch s) (length + 1)) addr
        (out (afterFetches (beforeFetch s) (length + 1))) oracleUsed nextIP) =
      (Operand.reg r₁ : Operand 64).read s := by
    rw [← Operand.read_beforeFetch s, ← Operand.read_afterFetches (beforeFetch s) (length + 1)]
    rfl
  rw [← hold]
  simp [Operand.write, Operand.read]

/--
Preservation for a read-modify-write and two register writes: if the written bytes lie below
4 GiB and outside the page-table frames, the state after the step is ready to step again.
-/
theorem ReadyToStep.afterStep_rmwRegPair [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n m : Nat} (addr : BitVec 64) (out : RamState → BitVec n × StatusFlags)
    (oracleUsed : Nat) (nextIP : BitVec 64) (r₁ : BitVec 5) (v₁ : RamState → BitVec m)
    (r₂ : BitVec 5) (v₂ : RamState → BitVec m) (hlow : addr.toNat + n / 8 ≤ 2^32)
    (htables : PageTableEntriesApart addr.toNat (n / 8)) :
    ReadyToStep (afterStep s length fun t =>
      writeRmwRegPairOutputs t addr (out t) oracleUsed nextIP r₁ (v₁ t) r₂ (v₂ t)) := by
  have hst : SameControls s (afterStep s length fun t =>
      writeRmwRegPairOutputs t addr (out t) oracleUsed nextIP r₁ (v₁ t) r₂ (v₂ t)) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  have hmem : Prelude.IdentityMappedMemory
      (afterStep s length fun t =>
        writeRmwRegPairOutputs t addr (out t) oracleUsed nextIP r₁ (v₁ t) r₂ (v₂ t)) := by
    refine ⟨h.memory.cr3, ?_⟩
    rw [afterStep_rmwRegPair_external]
    exact IdentityPageTableMemory.memStore h.memory.tables _ _ hlow htables
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass,
      hc.debug, hc.aet⟩,
    hmem,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, StatusFlags.trapFlagClear_store _ hr.tf,
      StatusFlags.resumeFlagClear_store _ hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-- A read-modify-write of `n` bits at `addr` and writes of registers `r₁` and `r₂` change only
those bytes, the two registers, the flags and RIP (besides the per-step bookkeeping). -/
theorem AgreesExcept.afterStep_rmwRegPair (s : RamState) (length : Nat) {n m : Nat}
    (addr : BitVec 64) (out : RamState → BitVec n × StatusFlags) (oracleUsed : Nat)
    (nextIP : BitVec 64) (r₁ : BitVec 5) (v₁ : RamState → BitVec m) (r₂ : BitVec 5)
    (v₂ : RamState → BitVec m) :
    AgreesExcept [.mem addr (n / 8), .reg r₁, .reg r₂, .flags, .rip] s
      (afterStep s length fun t =>
        writeRmwRegPairOutputs t addr (out t) oracleUsed nextIP r₁ (v₁ t) r₂ (v₂ t)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r' =>
      have hne₁ : r₁ ≠ r' := fun h => hc (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)
      have hne₂ : r₂ ≠ r' := fun h =>
        hc (h ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      show (Operand.reg r' : Operand 64).read _ = (Operand.reg r' : Operand 64).read _
      rw [Operand.read_afterStep, writeRmwRegPairOutputs, Operand.read_write_reg_of_ne _ hne₂,
        Operand.read_write_reg_of_ne _ hne₁, ← Operand.read_beforeFetch s,
        ← Operand.read_afterFetches (beforeFetch s) (length + 1)]
      rfl
    | flags => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem a l => exact absurd hm (by simp [Component.isMem])
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => exact dfBit_store _ _
  · rw [afterStep_rmwRegPair_external]
    apply memStore_getElem?_of_ne
    intro i hi he
    exact hx (.mem addr (n / 8)) (by simp) ⟨i, hi, he.symm⟩
  · simp only [fixedPart, afterStep, finishStep, writeRmwRegPairOutputs, writeRmwOutputs,
      writeFlagsOutputs, Operand.write, setFlags, dataAccess, afterFetches, beforeFetch,
      resetStepFields, clearStatusFlags_store]
  · rw [afterStep_rmwRegPair_external]
    exact memStore_isSome _ _ _ x hx

/-- The only memory component of `[.mem a l, .reg r₁, .reg r₂, .flags, .rip]` is `.mem a l`. -/
theorem mem_components_rmwRegPair (a : BitVec 64) (l : Nat) (r₁ r₂ : BitVec 5) :
    ∀ c ∈ [Component.mem a l, .reg r₁, .reg r₂, .flags, .rip], c.isMem = true → c = .mem a l := by
  intro c hc hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp_all [Component.isMem]

/-! ### Read-modify-write of an `AddrMode` operand -/

/-- The only memory component of `[.mem a l, .flags, .rip]` is `.mem a l`. -/
theorem mem_components_rmw (a : BitVec 64) (l : Nat) :
    ∀ c ∈ [Component.mem a l, .flags, .rip], c.isMem = true → c = .mem a l := by
  intro c hc hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> simp_all [Component.isMem]

/-- The precondition of a read-modify-write of `len` bytes at `[am]` by an instruction of
`codeLen` bytes at `p`. -/
abbrev RmwPre (p : BitVec 64) (am : AddrMode) (len codeLen : Nat) : RamState → Prop :=
  StorePre p codeLen (fun s => am.addr s (p + BitVec.ofNat 64 codeLen)) len

/-- `RmwPre`'s address facts at the step theorems' address (`AddrMode.addrAt`). -/
theorem rmw_facts {p : BitVec 64} {am : AddrMode} {len codeLen : Nat} {s : RamState}
    (h : RmwPre p am len codeLen s) :
    MemReadable s (am.addrAt s codeLen) len ∧
      PageTableEntriesApart (am.addrAt s codeLen).toNat len := by
  obtain ⟨hp, hw, -⟩ := h
  subst hp
  exact ⟨hw.readable, hw.tables⟩

/-- `RmwPre` for an operand at address size 32 (a `67` prefix): `StorePre` at
`am.addr32 s (p + codeLen)`. -/
abbrev Rmw32Pre (p : BitVec 64) (am : AddrMode) (len codeLen : Nat) : RamState → Prop :=
  StorePre p codeLen (fun s => am.addr32 s (p + BitVec.ofNat 64 codeLen)) len

/-- `Rmw32Pre`'s address facts at the step theorems' address (`AddrMode.addrAt32`). -/
theorem rmw32_facts {p : BitVec 64} {am : AddrMode} {len codeLen : Nat} {s : RamState}
    (h : Rmw32Pre p am len codeLen s) :
    MemReadable s (am.addrAt32 s codeLen) len ∧
      PageTableEntriesApart (am.addrAt32 s codeLen).toNat len := by
  obtain ⟨hp, hw, -⟩ := h
  subst hp
  exact ⟨hw.readable, hw.tables⟩

/-- The precondition of a read-modify-write of an `AddrMode` operand with a segment override `r`
(FS or GS) whose base is `base`: `SegStorePre` at `base + am.addr s (p + codeLen)`. -/
abbrev SegRmwPre (p : BitVec 64) (r : SegReg) (base : BitVec 64) (am : AddrMode) (len codeLen : Nat) :
    RamState → Prop :=
  SegStorePre p codeLen r base (fun s => am.addr s (p + BitVec.ofNat 64 codeLen)) len

/-- `SegRmwPre`'s facts at the step theorems' address (`segBase` of the segment plus
`AddrMode.addrAt`): the segment is ready, and the bytes are readable and apart from the page
tables. -/
theorem segRmw_facts {p base : BitVec 64} {r : SegReg} {am : AddrMode} {len codeLen : Nat}
    {s : RamState} (h : SegRmwPre p r base am len codeLen s) :
    s.RIP = p ∧ SegReady (r.read s) ∧ segBase (r.read s) = base ∧
      MemReadable s (segBase (r.read s) + am.addrAt s codeLen) len ∧
      PageTableEntriesApart (segBase (r.read s) + am.addrAt s codeLen).toNat len := by
  obtain ⟨⟨hp, hw, -⟩, hseg, hbase⟩ := h
  subst hp hbase
  exact ⟨rfl, hseg, rfl, hw.readable, hw.tables⟩

/-! ### Locked read-modify-write

A LOCK-prefixed read-modify-write (and XCHG with a memory operand, always locked) has the same
effect as the unlocked one; its precondition adds what the locked access needs (`LockReady`,
`Step/Memory.lean`: the operand lies in one cache line, the bus-lock-detect CPUID query is
answered). -/

/-- The precondition of a locked read-modify-write of `len` bytes at `[am]` by an instruction of
`codeLen` bytes at `p`: `RmwPre`, and the operand is ready to lock (`LockReady`). -/
structure LockedRmwPre [Bindings] (p : BitVec 64) (am : AddrMode) (len codeLen : Nat)
    (s : RamState) : Prop where
  rmw : RmwPre p am len codeLen s
  lock : LockReady s (am.addr s (p + BitVec.ofNat 64 codeLen)) len

/-- `LockedRmwPre`'s lock facts at the step theorems' address (`AddrMode.addrAt`). -/
theorem lockedRmw_lock [Bindings] {p : BitVec 64} {am : AddrMode} {len codeLen : Nat}
    {s : RamState} (h : LockedRmwPre p am len codeLen s) :
    LockReady s (am.addrAt s codeLen) len := by
  obtain ⟨⟨hp, -, -⟩, hl⟩ := h
  subst hp
  exact hl

/-- The precondition of a locked read-modify-write of an `AddrMode` operand with a segment
override `r` (FS or GS) whose base is `base`: `SegRmwPre`, and the operand is ready to lock
(`LockReady` at `base + am.addr s (p + codeLen)`). -/
structure SegLockedRmwPre [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) (am : AddrMode)
    (len codeLen : Nat) (s : RamState) : Prop where
  rmw : SegRmwPre p r base am len codeLen s
  lock : LockReady s (base + am.addr s (p + BitVec.ofNat 64 codeLen)) len

/-- `SegLockedRmwPre`'s lock facts at the step theorems' address (`segBase` of the segment plus
`AddrMode.addrAt`). -/
theorem segLockedRmw_lock [Bindings] {p base : BitVec 64} {r : SegReg} {am : AddrMode}
    {len codeLen : Nat} {s : RamState} (h : SegLockedRmwPre p r base am len codeLen s) :
    LockReady s (segBase (r.read s) + am.addrAt s codeLen) len := by
  obtain ⟨⟨⟨hp, -, -⟩, -, hbase⟩, hl⟩ := h
  subst hp hbase
  exact hl

/-- The precondition of a locked read-modify-write at address size 32 (a `67` prefix):
`Rmw32Pre`, and the operand is ready to lock (`LockReady` at `am.addr32 s (p + codeLen)`). -/
structure LockedRmw32Pre [Bindings] (p : BitVec 64) (am : AddrMode) (len codeLen : Nat)
    (s : RamState) : Prop where
  rmw : Rmw32Pre p am len codeLen s
  lock : LockReady s (am.addr32 s (p + BitVec.ofNat 64 codeLen)) len

/-- `LockedRmw32Pre`'s lock facts at the step theorems' address (`AddrMode.addrAt32`). -/
theorem lockedRmw32_lock [Bindings] {p : BitVec 64} {am : AddrMode} {len codeLen : Nat}
    {s : RamState} (h : LockedRmw32Pre p am len codeLen s) :
    LockReady s (am.addrAt32 s codeLen) len := by
  obtain ⟨⟨hp, -, -⟩, hl⟩ := h
  subst hp
  exact hl

/-! ### Read-modify-write and a no-REX byte register (AL–BL, AH–BH)

XADD and XCHG `[mem], r8` without a REX prefix write the byte register `Operand.byteReg r`, which
for AH–BH is bits 8–15 of a register. `writeRmwOpOutputs` and `writeRmwOpResult` are
`writeRmwRegOutputs` and `writeRmwRegResult` with any operand as the register written; the lemmas
below are about a no-REX byte register, whose 64-bit register `byteRegGpr r` gets the byte merged
into its old value (`mergeByteReg`). -/

/-- `writeRmwRegOutputs` with the operand `dst` written last (a byte register, e.g. AH). -/
def writeRmwOpOutputs {n : Nat} (t : RamState) (addr : BitVec 64) (out : BitVec n × StatusFlags)
    (oracleUsed : Nat) (nextIP : BitVec 64) (dst : Operand n) (v : BitVec n) : RamState :=
  dst.write (writeRmwOutputs t addr out oracleUsed nextIP) v

/-- `writeRmwRegResult` with the operand `dst` written last (a byte register, e.g. AH). -/
def writeRmwOpResult {n : Nat} (t : RamState) (addr : BitVec 64) (v : BitVec n)
    (nextIP : BitVec 64) (dst : Operand n) (w : BitVec n) : RamState :=
  dst.write (writeRmwResult t addr v nextIP) w

/-- The byte register write after a read-modify-write is a 64-bit write of `byteRegGpr r`. -/
theorem writeRmwOpOutputs_byteReg (t : RamState) (addr : BitVec 64)
    (out : BitVec 8 × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) (r : BitVec 3)
    (v : BitVec 8) :
    writeRmwOpOutputs t addr out oracleUsed nextIP (Operand.byteReg r) v =
      (Operand.reg (byteRegGpr r) : Operand 64).write
        (writeRmwOutputs t addr out oracleUsed nextIP)
        (mergeByteReg r v ((Operand.reg (byteRegGpr r) : Operand 64).read t)) := by
  have hg : (writeRmwOutputs t addr out oracleUsed nextIP).GPR = t.GPR := by
    simp only [writeRmwOutputs, writeFlagsOutputs, setFlags, Operand.write, dataAccess]
  rw [writeRmwOpOutputs, Operand.write_byteReg_eq_reg64, Operand.read_reg_of_gpr_eq hg]

/-- The byte register write after a read-modify-write without flags is a 64-bit write of
`byteRegGpr r`. -/
theorem writeRmwOpResult_byteReg (t : RamState) (addr : BitVec 64) (v : BitVec 8)
    (nextIP : BitVec 64) (r : BitVec 3) (w : BitVec 8) :
    writeRmwOpResult t addr v nextIP (Operand.byteReg r) w =
      (Operand.reg (byteRegGpr r) : Operand 64).write (writeRmwResult t addr v nextIP)
        (mergeByteReg r w ((Operand.reg (byteRegGpr r) : Operand 64).read t)) := by
  have hg : (writeRmwResult t addr v nextIP).GPR = t.GPR := rfl
  rw [writeRmwOpResult, Operand.write_byteReg_eq_reg64, Operand.read_reg_of_gpr_eq hg]

theorem afterStep_rmwByte_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (addr : BitVec 64) (out : RamState → BitVec 8 × StatusFlags) (oracleUsed : Nat)
    (nextIP : BitVec 64) (r : BitVec 3) (v : RamState → BitVec 8) :
    (afterStep s length fun t =>
      writeRmwOpOutputs t addr (out t) oracleUsed nextIP (Operand.byteReg r) (v t)).RIP =
      nextIP := by
  simp only [writeRmwOpOutputs_byteReg]
  simp [afterStep, finishStep, writeRmwOutputs, writeFlagsOutputs, setFlags, Operand.write,
    dataAccess, afterFetches, beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

theorem afterStep_rmwByte_external (s : RamState) (length : Nat) (addr : BitVec 64)
    (out : RamState → BitVec 8 × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64)
    (r : BitVec 3) (v : RamState → BitVec 8) :
    (afterStep s length fun t =>
      writeRmwOpOutputs t addr (out t) oracleUsed nextIP (Operand.byteReg r) (v t)).external =
      memStore s.external addr (out (afterFetches (beforeFetch s) (length + 1))).1 := by
  simp only [writeRmwOpOutputs_byteReg]
  rfl

/-- After a read-modify-write and a byte register write, RFLAGS holds the stored flags. -/
theorem afterStep_rmwByte_RFLAGS (s : RamState) (length : Nat) (addr : BitVec 64)
    (out : RamState → BitVec 8 × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64)
    (r : BitVec 3) (v : RamState → BitVec 8) :
    (afterStep s length fun t =>
      writeRmwOpOutputs t addr (out t) oracleUsed nextIP (Operand.byteReg r) (v t)).RFLAGS =
      (out (afterFetches (beforeFetch s) (length + 1))).2.store s.RFLAGS := by
  simp only [writeRmwOpOutputs_byteReg]
  rfl

/-- After a read-modify-write and a byte register write, the memory operand holds the written
value. -/
theorem Operand.read_afterStep_rmwByte_mem (s : RamState) (length : Nat) (addr : BitVec 64)
    (out : RamState → BitVec 8 × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64)
    (r : BitVec 3) (v : RamState → BitVec 8) :
    (Operand.mem addr : Operand 8).read
        (afterStep s length fun t =>
          writeRmwOpOutputs t addr (out t) oracleUsed nextIP (Operand.byteReg r) (v t)) =
      (out (afterFetches (beforeFetch s) (length + 1))).1 := by
  show memLoad _ addr 8 = _
  rw [afterStep_rmwByte_external]
  exact memLoad_memStore _ _ (by decide) (by decide) _

/-- After a read-modify-write and a write of no-REX byte register `r`, register `byteRegGpr r` is
its old value with that byte replaced. -/
theorem Operand.read_afterStep_rmwByte_reg (s : RamState) (length : Nat) (addr : BitVec 64)
    (out : RamState → BitVec 8 × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64)
    (r : BitVec 3) (v : RamState → BitVec 8) :
    (Operand.reg (byteRegGpr r) : Operand 64).read
        (afterStep s length fun t =>
          writeRmwOpOutputs t addr (out t) oracleUsed nextIP (Operand.byteReg r) (v t)) =
      mergeByteReg r (v (afterFetches (beforeFetch s) (length + 1)))
        ((Operand.reg (byteRegGpr r) : Operand 64).read s) := by
  rw [Operand.read_afterStep, writeRmwOpOutputs_byteReg, Operand.write_reg64, Operand.read_reg64,
    Operand.read_afterFetches, Operand.read_beforeFetch]
  simp

/-- Preservation for a read-modify-write and a byte register write: if the written bytes lie below
4 GiB and outside the page-table frames, the state after the step is ready to step again. -/
theorem ReadyToStep.afterStep_rmwByte [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (addr : BitVec 64) (out : RamState → BitVec 8 × StatusFlags)
    (oracleUsed : Nat) (nextIP : BitVec 64) (r : BitVec 3) (v : RamState → BitVec 8)
    (hlow : addr.toNat + 1 ≤ 2^32)
    (htables : PageTableEntriesApart addr.toNat 1) :
    ReadyToStep (afterStep s length fun t =>
      writeRmwOpOutputs t addr (out t) oracleUsed nextIP (Operand.byteReg r) (v t)) := by
  have hext := afterStep_rmwByte_external s length addr out oracleUsed nextIP r v
  simp only [writeRmwOpOutputs_byteReg] at hext ⊢
  have hst : SameControls s (afterStep s length fun t =>
      (Operand.reg (byteRegGpr r) : Operand 64).write
        (writeRmwOutputs t addr (out t) oracleUsed nextIP)
        (mergeByteReg r (v t) ((Operand.reg (byteRegGpr r) : Operand 64).read t))) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  have hmem : Prelude.IdentityMappedMemory (afterStep s length fun t =>
      (Operand.reg (byteRegGpr r) : Operand 64).write
        (writeRmwOutputs t addr (out t) oracleUsed nextIP)
        (mergeByteReg r (v t) ((Operand.reg (byteRegGpr r) : Operand 64).read t))) := by
    refine ⟨h.memory.cr3, ?_⟩
    rw [hext]
    exact IdentityPageTableMemory.memStore h.memory.tables _ _ hlow htables
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass,
      hc.debug, hc.aet⟩,
    hmem,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, StatusFlags.trapFlagClear_store _ hr.tf, StatusFlags.resumeFlagClear_store _ hr.rf,
      hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-- A read-modify-write of a byte at `addr` and a write of no-REX byte register `r` change only
that byte, register `byteRegGpr r`, the flags and RIP. -/
theorem AgreesExcept.afterStep_rmwByte (s : RamState) (length : Nat) (addr : BitVec 64)
    (out : RamState → BitVec 8 × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64)
    (r : BitVec 3) (v : RamState → BitVec 8) :
    AgreesExcept [.mem addr (8 / 8), .reg (byteRegGpr r), .flags, .rip] s
      (afterStep s length fun t =>
        writeRmwOpOutputs t addr (out t) oracleUsed nextIP (Operand.byteReg r) (v t)) := by
  have hext := afterStep_rmwByte_external s length addr out oracleUsed nextIP r v
  simp only [writeRmwOpOutputs_byteReg] at hext ⊢
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r' =>
      have hne : byteRegGpr r ≠ r' := fun h => hc (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)
      show (Operand.reg r' : Operand 64).read _ = (Operand.reg r' : Operand 64).read _
      rw [Operand.read_afterStep, Operand.read_write_reg_of_ne _ hne,
        ← Operand.read_beforeFetch s, ← Operand.read_afterFetches (beforeFetch s) (length + 1)]
      rfl
    | flags => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem a l => exact absurd hm (by simp [Component.isMem])
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => exact dfBit_store _ _
  · rw [hext]
    apply memStore_getElem?_of_ne
    intro i hi he
    exact hx (.mem addr (8 / 8)) (by simp) ⟨i, hi, he.symm⟩
  · simp only [fixedPart, afterStep, finishStep, writeRmwOutputs, writeFlagsOutputs, Operand.write,
      setFlags, dataAccess, afterFetches, beforeFetch, resetStepFields, clearStatusFlags_store]
  · rw [hext]
    exact memStore_isSome _ _ _ x hx

theorem afterStep_rmwByteResult_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (addr : BitVec 64) (v : RamState → BitVec 8) (nextIP : BitVec 64) (r : BitVec 3)
    (w : RamState → BitVec 8) :
    (afterStep s length fun t =>
      writeRmwOpResult t addr (v t) nextIP (Operand.byteReg r) (w t)).RIP = nextIP := by
  simp only [writeRmwOpResult_byteReg]
  simp [afterStep, finishStep, writeRmwResult, Operand.write, dataAccess, afterFetches,
    beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

theorem afterStep_rmwByteResult_external (s : RamState) (length : Nat) (addr : BitVec 64)
    (v : RamState → BitVec 8) (nextIP : BitVec 64) (r : BitVec 3) (w : RamState → BitVec 8) :
    (afterStep s length fun t =>
      writeRmwOpResult t addr (v t) nextIP (Operand.byteReg r) (w t)).external =
      memStore s.external addr (v (afterFetches (beforeFetch s) (length + 1))) := by
  simp only [writeRmwOpResult_byteReg]
  rfl

/-- After a read-modify-write without flags and a byte register write, the memory operand holds the
written value. -/
theorem Operand.read_afterStep_rmwByteResult_mem (s : RamState) (length : Nat) (addr : BitVec 64)
    (v : RamState → BitVec 8) (nextIP : BitVec 64) (r : BitVec 3) (w : RamState → BitVec 8) :
    (Operand.mem addr : Operand 8).read
        (afterStep s length fun t =>
          writeRmwOpResult t addr (v t) nextIP (Operand.byteReg r) (w t)) =
      v (afterFetches (beforeFetch s) (length + 1)) := by
  show memLoad _ addr 8 = _
  rw [afterStep_rmwByteResult_external]
  exact memLoad_memStore _ _ (by decide) (by decide) _

/-- After a read-modify-write without flags and a write of no-REX byte register `r`, register
`byteRegGpr r` is its old value with that byte replaced. -/
theorem Operand.read_afterStep_rmwByteResult_reg (s : RamState) (length : Nat) (addr : BitVec 64)
    (v : RamState → BitVec 8) (nextIP : BitVec 64) (r : BitVec 3) (w : RamState → BitVec 8) :
    (Operand.reg (byteRegGpr r) : Operand 64).read
        (afterStep s length fun t =>
          writeRmwOpResult t addr (v t) nextIP (Operand.byteReg r) (w t)) =
      mergeByteReg r (w (afterFetches (beforeFetch s) (length + 1)))
        ((Operand.reg (byteRegGpr r) : Operand 64).read s) := by
  rw [Operand.read_afterStep, writeRmwOpResult_byteReg, Operand.write_reg64, Operand.read_reg64,
    Operand.read_afterFetches, Operand.read_beforeFetch]
  simp

/-- Preservation for a read-modify-write without flags and a byte register write. -/
theorem ReadyToStep.afterStep_rmwByteResult [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (addr : BitVec 64) (v : RamState → BitVec 8) (nextIP : BitVec 64)
    (r : BitVec 3) (w : RamState → BitVec 8)
    (hlow : addr.toNat + 1 ≤ 2^32)
    (htables : PageTableEntriesApart addr.toNat 1) :
    ReadyToStep (afterStep s length fun t =>
      writeRmwOpResult t addr (v t) nextIP (Operand.byteReg r) (w t)) := by
  have hext := afterStep_rmwByteResult_external s length addr v nextIP r w
  simp only [writeRmwOpResult_byteReg] at hext ⊢
  have hst : SameControls s (afterStep s length fun t =>
      (Operand.reg (byteRegGpr r) : Operand 64).write (writeRmwResult t addr (v t) nextIP)
        (mergeByteReg r (w t) ((Operand.reg (byteRegGpr r) : Operand 64).read t))) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  have hmem : Prelude.IdentityMappedMemory (afterStep s length fun t =>
      (Operand.reg (byteRegGpr r) : Operand 64).write (writeRmwResult t addr (v t) nextIP)
        (mergeByteReg r (w t) ((Operand.reg (byteRegGpr r) : Operand 64).read t))) := by
    refine ⟨h.memory.cr3, ?_⟩
    rw [hext]
    exact IdentityPageTableMemory.memStore h.memory.tables _ _ hlow htables
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass,
      hc.debug, hc.aet⟩,
    hmem,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, hr.tf, hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-- A read-modify-write without flags of a byte at `addr` and a write of no-REX byte register `r`
change only that byte, register `byteRegGpr r` and RIP. -/
theorem AgreesExcept.afterStep_rmwByteResult (s : RamState) (length : Nat) (addr : BitVec 64)
    (v : RamState → BitVec 8) (nextIP : BitVec 64) (r : BitVec 3) (w : RamState → BitVec 8) :
    AgreesExcept [.mem addr (8 / 8), .reg (byteRegGpr r), .rip] s
      (afterStep s length fun t =>
        writeRmwOpResult t addr (v t) nextIP (Operand.byteReg r) (w t)) := by
  have hext := afterStep_rmwByteResult_external s length addr v nextIP r w
  simp only [writeRmwOpResult_byteReg] at hext ⊢
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r' =>
      have hne : byteRegGpr r ≠ r' := fun h => hc (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)
      show (Operand.reg r' : Operand 64).read _ = (Operand.reg r' : Operand 64).read _
      rw [Operand.read_afterStep, Operand.read_write_reg_of_ne _ hne,
        ← Operand.read_beforeFetch s, ← Operand.read_afterFetches (beforeFetch s) (length + 1)]
      rfl
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem a l => exact absurd hm (by simp [Component.isMem])
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => rfl
  · rw [hext]
    apply memStore_getElem?_of_ne
    intro i hi he
    exact hx (.mem addr (8 / 8)) (by simp) ⟨i, hi, he.symm⟩
  · simp only [fixedPart, afterStep, finishStep, writeRmwResult, Operand.write, dataAccess,
      afterFetches, beforeFetch, resetStepFields]
  · rw [hext]
    exact memStore_isSome _ _ _ x hx

/-! ### Preconditions after a block -/

section Carry

variable {e : Effect} {s s' : RamState}

@[x86_pre] theorem LockedRmwPre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} {am : AddrMode} {len codeLen : Nat}
    (hrmw : RmwPre p am len codeLen s')
    (hl : LockReady s (am.addr (e.after s true) (p + BitVec.ofNat 64 codeLen)) len) :
    LockedRmwPre p am len codeLen s' :=
  ⟨hrmw, by rw [Obs.back_addr ho]; exact h.lockReady_iff.mpr hl⟩

@[x86_pre] theorem SegLockedRmwPre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p base : BitVec 64} {r : SegReg} {am : AddrMode}
    {len codeLen : Nat} (hrmw : SegRmwPre p r base am len codeLen s')
    (hl : LockReady s (base + am.addr (e.after s true) (p + BitVec.ofNat 64 codeLen)) len) :
    SegLockedRmwPre p r base am len codeLen s' :=
  ⟨hrmw, by rw [Obs.back_addr ho]; exact h.lockReady_iff.mpr hl⟩

@[x86_pre] theorem LockedRmw32Pre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} {am : AddrMode} {len codeLen : Nat}
    (hrmw : Rmw32Pre p am len codeLen s')
    (hl : LockReady s (am.addr32 (e.after s true) (p + BitVec.ofNat 64 codeLen)) len) :
    LockedRmw32Pre p am len codeLen s' :=
  ⟨hrmw, by rw [Obs.back_addr32 ho]; exact h.lockReady_iff.mpr hl⟩

end Carry

end X86Proofs
