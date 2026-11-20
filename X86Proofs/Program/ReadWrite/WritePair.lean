import X86Proofs.Program.ReadWrite.LoadFlags

/-!
# Write-back to two registers

`writePairOutputs s r₁ r₂ v₁ v₂ f oracleUsed nextIP` is the form-level result of an instruction
with two register destinations and the status flags: the one-operand multiplies and divides write
RDX:RAX (`MUL`, `IMUL`: RAX then RDX; `DIV`, `IDIV`: the remainder to RDX, then the quotient to
RAX). It is `writeOutputs` to `r₁` followed by a write of `r₂`; each register write merges into
the old value as `Operand.write` does (`mergeGPR`: zero-extended at 32 bits, the bits above kept at
16).

For a step whose form ends in `writePairOutputs` (with two different registers), the same facts as
for `writeOutputs`, directly and after a memory read (`dataAccess t "load"`, the memory forms):
- `afterStep_writePairOutputs_rip`, `afterStep_loadWritePairOutputs_rip`: RIP after the step is
  `nextIP`;
- `ReadyToStep.afterStep_writePairOutputs`, `ReadyToStep.afterStep_loadWritePairOutputs`: the state
  after the step is ready to step again;
- `AgreesExcept.afterStep_writePairOutputs`, `AgreesExcept.afterStep_loadWritePairOutputs`: only the
  two registers, the flags and RIP change;
- `Operand.read_writePairOutputs_fst`, `Operand.read_writePairOutputs_snd`: the two registers
  after it, as 64-bit values.

`Operand.write_write_setFlags` and `Operand.write_setFlags` move a flags update out from under
register writes, for proofs that compare lean-x86's order of writes with this one.

The two registers may also be the same (XADD, XCHG of a register with itself): then the second
write wins, `Operand.read_writePairOutputs_same`.

`writeResultPair s r₁ r₂ v₁ v₂ nextIP` is the same without the flags (XCHG): `writeResult` to `r₁`
followed by a write of `r₂`, with the same facts (`afterStep_writeResultPair_rip`,
`ReadyToStep.afterStep_writeResultPair`, `AgreesExcept.afterStep_writeResultPair`, and the reads
`Operand.read_writeResultPair_fst`, `_snd`, `_same`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- Form-level write-back of an instruction with two register destinations and the status flags:
`s` with `Next_IP` set, `oracleUsed` oracle bits used up, the flags `f` stored, register `r₁` set
to `v₁` and then register `r₂` to `v₂` (each `n` bits, merged as `Operand.write` does). -/
def writePairOutputs {σ : Type} [PhysicalMemory σ] {n : Nat} (s : X86.State σ) (r₁ r₂ : BitVec 5)
    (v₁ v₂ : BitVec n) (f : StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    X86.State σ :=
  (Operand.reg r₂ : Operand n).write
    ((Operand.reg r₁ : Operand n).write
      (setFlags { s with Next_IP := nextIP, oracle := oracleSkip s.oracle oracleUsed } f) v₁) v₂

/-- A register write commutes with a flags update and an oracle update before it. -/
theorem Operand.write_setFlags {σ : Type} [PhysicalMemory σ] {n : Nat} (s : X86.State σ)
    (r : BitVec 5) (v : BitVec n) (o : X86.Runtime.Oracle) (f : StatusFlags) :
    (Operand.reg r : Operand n).write (setFlags { s with oracle := o } f) v =
      setFlags { (Operand.reg r : Operand n).write s v with oracle := o } f := rfl

/-- Two register writes commute with a flags update and an oracle update before them. -/
theorem Operand.write_write_setFlags {σ : Type} [PhysicalMemory σ] {n : Nat} (s : X86.State σ)
    (r₁ r₂ : BitVec 5) (v₁ v₂ : BitVec n) (o : X86.Runtime.Oracle) (f : StatusFlags) :
    (Operand.reg r₂ : Operand n).write
        ((Operand.reg r₁ : Operand n).write (setFlags { s with oracle := o } f) v₁) v₂ =
      setFlags
        { (Operand.reg r₂ : Operand n).write ((Operand.reg r₁ : Operand n).write s v₁) v₂ with
          oracle := o } f := rfl

theorem gprIndex_ne {r r' : BitVec 5} (h : r ≠ r') : gprIndex r ≠ gprIndex r' :=
  fun e => h (BitVec.eq_of_toNat_eq (Fin.mk.inj_iff.mp e))

/-- After `writePairOutputs`, the full register `r₁` is `v₁` merged into its old value. -/
theorem Operand.read_writePairOutputs_fst {σ : Type} [PhysicalMemory σ] {n : Nat}
    (s : X86.State σ) {r₁ r₂ : BitVec 5} (hne : r₁ ≠ r₂) (v₁ v₂ : BitVec n) (f : StatusFlags)
    (oracleUsed : Nat) (nextIP : BitVec 64) :
    (Operand.reg r₁ : Operand 64).read (writePairOutputs s r₁ r₂ v₁ v₂ f oracleUsed nextIP) =
      mergeGPR n v₁ ((Operand.reg r₁ : Operand 64).read s) := by
  simp [writePairOutputs, Operand.write, Operand.read, setFlags,
    Fin.val_ne_of_ne (gprIndex_ne hne.symm)]

/-- After `writePairOutputs`, the full register `r₂` is `v₂` merged into its old value. -/
theorem Operand.read_writePairOutputs_snd {σ : Type} [PhysicalMemory σ] {n : Nat}
    (s : X86.State σ) {r₁ r₂ : BitVec 5} (hne : r₁ ≠ r₂) (v₁ v₂ : BitVec n) (f : StatusFlags)
    (oracleUsed : Nat) (nextIP : BitVec 64) :
    (Operand.reg r₂ : Operand 64).read (writePairOutputs s r₁ r₂ v₁ v₂ f oracleUsed nextIP) =
      mergeGPR n v₂ ((Operand.reg r₂ : Operand 64).read s) := by
  simp [writePairOutputs, Operand.write, Operand.read, setFlags,
    Fin.val_ne_of_ne (gprIndex_ne hne)]

/-- After `writePairOutputs` to one register twice, the full register is the second value merged
into its old value. -/
theorem Operand.read_writePairOutputs_same {σ : Type} [PhysicalMemory σ] {n : Nat}
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (s : X86.State σ) (r : BitVec 5) (v₁ v₂ : BitVec n)
    (f : StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    (Operand.reg r : Operand 64).read (writePairOutputs s r r v₁ v₂ f oracleUsed nextIP) =
      mergeGPR n v₂ ((Operand.reg r : Operand 64).read s) := by
  simp [writePairOutputs, Operand.write, Operand.read, setFlags, mergeGPR_mergeGPR n hn]

/-- After `writePairOutputs`, a register other than the two reads as before. -/
theorem Operand.read_writePairOutputs_of_ne {σ : Type} [PhysicalMemory σ] {n m : Nat}
    (s : X86.State σ) {r₁ r₂ r : BitVec 5} (h₁ : r₁ ≠ r) (h₂ : r₂ ≠ r) (v₁ v₂ : BitVec n)
    (f : StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    (Operand.reg r : Operand m).read (writePairOutputs s r₁ r₂ v₁ v₂ f oracleUsed nextIP) =
      (Operand.reg r : Operand m).read s := by
  simp [writePairOutputs, Operand.write, Operand.read, setFlags,
    Fin.val_ne_of_ne (gprIndex_ne h₁), Fin.val_ne_of_ne (gprIndex_ne h₂)]

/-- After a form that ends in `writePairOutputs … nextIP`, RIP is `nextIP`. -/
theorem afterStep_writePairOutputs_rip [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (r₁ r₂ : BitVec 5) (v₁ v₂ : RamState → BitVec n)
    (f : RamState → StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    (afterStep s length fun t =>
      writePairOutputs t r₁ r₂ (v₁ t) (v₂ t) (f t) oracleUsed nextIP).RIP = nextIP := by
  simp [afterStep, finishStep, writePairOutputs, Operand.write, setFlags, afterFetches,
    beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- After a load form that ends in `writePairOutputs … nextIP`, RIP is `nextIP`. -/
theorem afterStep_loadWritePairOutputs_rip [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (r₁ r₂ : BitVec 5) (v₁ v₂ : RamState → BitVec n)
    (f : RamState → StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    (afterStep s length fun t =>
      writePairOutputs (dataAccess t "load") r₁ r₂ (v₁ t) (v₂ t) (f t) oracleUsed nextIP).RIP =
      nextIP := by
  simp [afterStep, finishStep, writePairOutputs, Operand.write, setFlags, dataAccess,
    afterFetches, beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- Preservation: after a form that ends in `writePairOutputs`, the state is ready to step again
(only two registers, the status flags, the oracle, `Next_IP`, RIP and per-step bookkeeping
change). -/
theorem ReadyToStep.afterStep_writePairOutputs [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (r₁ r₂ : BitVec 5) (v₁ v₂ : RamState → BitVec n)
    (f : RamState → StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t =>
      writePairOutputs t r₁ r₂ (v₁ t) (v₂ t) (f t) oracleUsed nextIP) := by
  have hst : SameControls s (afterStep s length fun t =>
      writePairOutputs t r₁ r₂ (v₁ t) (v₂ t) (f t) oracleUsed nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass,
      hc.debug, hc.aet⟩,
    ⟨h.memory.cr3, h.memory.tables⟩,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, StatusFlags.trapFlagClear_store _ hr.tf,
      StatusFlags.resumeFlagClear_store _ hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-- Preservation for a load form that ends in `writePairOutputs`. -/
theorem ReadyToStep.afterStep_loadWritePairOutputs [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (r₁ r₂ : BitVec 5) (v₁ v₂ : RamState → BitVec n)
    (f : RamState → StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t =>
      writePairOutputs (dataAccess t "load") r₁ r₂ (v₁ t) (v₂ t) (f t) oracleUsed nextIP) := by
  have hst : SameControls s (afterStep s length fun t =>
      writePairOutputs (dataAccess t "load") r₁ r₂ (v₁ t) (v₂ t) (f t) oracleUsed nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass,
      hc.debug, hc.aet⟩,
    ⟨h.memory.cr3, h.memory.tables⟩,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, StatusFlags.trapFlagClear_store _ hr.tf,
      StatusFlags.resumeFlagClear_store _ hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-- A step whose form ends in `writePairOutputs` to registers `r₁` and `r₂` changes only those
registers, the status flags and RIP (besides the per-step bookkeeping). -/
theorem AgreesExcept.afterStep_writePairOutputs (s : RamState) (length : Nat) {n : Nat}
    (r₁ r₂ : BitVec 5) (v₁ v₂ : RamState → BitVec n) (f : RamState → StatusFlags)
    (oracleUsed : Nat) (nextIP : BitVec 64) :
    AgreesExcept [.reg r₁, .reg r₂, .flags, .rip] s
      (afterStep s length fun t =>
        writePairOutputs t r₁ r₂ (v₁ t) (v₂ t) (f t) oracleUsed nextIP) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r =>
      have h₁ : r₁ ≠ r := fun h => hc (h ▸ List.mem_cons_self)
      have h₂ : r₂ ≠ r := fun h => hc (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)
      have := (Operand.read_afterStep s length
        (fun t => writePairOutputs t r₁ r₂ (v₁ t) (v₂ t) (f t) oracleUsed nextIP)
        (.reg r : Operand 64)).trans
        (Operand.read_writePairOutputs_of_ne (m := 64) _ h₁ h₂ _ _ _ _ _)
      simp only [Operand.read_reg64] at this
      exact this
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
  · simp only [fixedPart, afterStep, finishStep, writePairOutputs, Operand.write, setFlags,
      afterFetches, beforeFetch, resetStepFields, clearStatusFlags_store]

/-- A load form that ends in `writePairOutputs` to registers `r₁` and `r₂` changes only those
registers, the status flags and RIP (besides the per-step bookkeeping). -/
theorem AgreesExcept.afterStep_loadWritePairOutputs (s : RamState) (length : Nat) {n : Nat}
    (r₁ r₂ : BitVec 5) (v₁ v₂ : RamState → BitVec n) (f : RamState → StatusFlags)
    (oracleUsed : Nat) (nextIP : BitVec 64) :
    AgreesExcept [.reg r₁, .reg r₂, .flags, .rip] s
      (afterStep s length fun t =>
        writePairOutputs (dataAccess t "load") r₁ r₂ (v₁ t) (v₂ t) (f t) oracleUsed nextIP) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r =>
      have h₁ : r₁ ≠ r := fun h => hc (h ▸ List.mem_cons_self)
      have h₂ : r₂ ≠ r := fun h => hc (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)
      have := (Operand.read_afterStep s length
        (fun t => writePairOutputs (dataAccess t "load") r₁ r₂ (v₁ t) (v₂ t) (f t) oracleUsed
          nextIP) (.reg r : Operand 64)).trans
        (Operand.read_writePairOutputs_of_ne (m := 64) _ h₁ h₂ _ _ _ _ _)
      simp only [Operand.read_reg64] at this
      exact this
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
  · simp only [fixedPart, afterStep, finishStep, writePairOutputs, Operand.write, setFlags,
      dataAccess, afterFetches, beforeFetch, resetStepFields, clearStatusFlags_store]

/-! ### Two registers, no flags -/

/-- Form-level write-back of an instruction with two register destinations and no flags (XCHG):
`s` with `Next_IP` set, register `r₁` set to `v₁` and then register `r₂` to `v₂` (each `n` bits,
merged as `Operand.write` does). -/
def writeResultPair {σ : Type} [PhysicalMemory σ] {n : Nat} (s : X86.State σ) (r₁ r₂ : BitVec 5)
    (v₁ v₂ : BitVec n) (nextIP : BitVec 64) : X86.State σ :=
  (Operand.reg r₂ : Operand n).write
    ((Operand.reg r₁ : Operand n).write { s with Next_IP := nextIP } v₁) v₂

/-- After `writeResultPair`, the full register `r₁` is `v₁` merged into its old value. -/
theorem Operand.read_writeResultPair_fst {σ : Type} [PhysicalMemory σ] {n : Nat}
    (s : X86.State σ) {r₁ r₂ : BitVec 5} (hne : r₁ ≠ r₂) (v₁ v₂ : BitVec n) (nextIP : BitVec 64) :
    (Operand.reg r₁ : Operand 64).read (writeResultPair s r₁ r₂ v₁ v₂ nextIP) =
      mergeGPR n v₁ ((Operand.reg r₁ : Operand 64).read s) := by
  simp [writeResultPair, Operand.write, Operand.read, Fin.val_ne_of_ne (gprIndex_ne hne.symm)]

/-- After `writeResultPair`, the full register `r₂` is `v₂` merged into its old value. -/
theorem Operand.read_writeResultPair_snd {σ : Type} [PhysicalMemory σ] {n : Nat}
    (s : X86.State σ) {r₁ r₂ : BitVec 5} (hne : r₁ ≠ r₂) (v₁ v₂ : BitVec n) (nextIP : BitVec 64) :
    (Operand.reg r₂ : Operand 64).read (writeResultPair s r₁ r₂ v₁ v₂ nextIP) =
      mergeGPR n v₂ ((Operand.reg r₂ : Operand 64).read s) := by
  simp [writeResultPair, Operand.write, Operand.read, Fin.val_ne_of_ne (gprIndex_ne hne)]

/-- After `writeResultPair` to one register twice, the full register is the second value merged
into its old value. -/
theorem Operand.read_writeResultPair_same {σ : Type} [PhysicalMemory σ] {n : Nat}
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (s : X86.State σ) (r : BitVec 5) (v₁ v₂ : BitVec n)
    (nextIP : BitVec 64) :
    (Operand.reg r : Operand 64).read (writeResultPair s r r v₁ v₂ nextIP) =
      mergeGPR n v₂ ((Operand.reg r : Operand 64).read s) := by
  simp [writeResultPair, Operand.write, Operand.read, mergeGPR_mergeGPR n hn]

/-- After `writeResultPair`, a register other than the two reads as before. -/
theorem Operand.read_writeResultPair_of_ne {σ : Type} [PhysicalMemory σ] {n m : Nat}
    (s : X86.State σ) {r₁ r₂ r : BitVec 5} (h₁ : r₁ ≠ r) (h₂ : r₂ ≠ r) (v₁ v₂ : BitVec n)
    (nextIP : BitVec 64) :
    (Operand.reg r : Operand m).read (writeResultPair s r₁ r₂ v₁ v₂ nextIP) =
      (Operand.reg r : Operand m).read s := by
  simp [writeResultPair, Operand.write, Operand.read, Fin.val_ne_of_ne (gprIndex_ne h₁),
    Fin.val_ne_of_ne (gprIndex_ne h₂)]

/-- After a form that ends in `writeResultPair … nextIP`, RIP is `nextIP`. -/
theorem afterStep_writeResultPair_rip [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (r₁ r₂ : BitVec 5) (v₁ v₂ : RamState → BitVec n)
    (nextIP : BitVec 64) :
    (afterStep s length fun t => writeResultPair t r₁ r₂ (v₁ t) (v₂ t) nextIP).RIP = nextIP := by
  simp [afterStep, finishStep, writeResultPair, Operand.write, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- Preservation: after a form that ends in `writeResultPair`, the state is ready to step again
(only two registers, `Next_IP`, RIP and per-step bookkeeping change). -/
theorem ReadyToStep.afterStep_writeResultPair [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (r₁ r₂ : BitVec 5) (v₁ v₂ : RamState → BitVec n)
    (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t => writeResultPair t r₁ r₂ (v₁ t) (v₂ t) nextIP) := by
  have hst : SameControls s (afterStep s length fun t =>
      writeResultPair t r₁ r₂ (v₁ t) (v₂ t) nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass,
      hc.debug, hc.aet⟩,
    ⟨h.memory.cr3, h.memory.tables⟩,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, hr.tf, hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-- A step whose form ends in `writeResultPair` to registers `r₁` and `r₂` changes only those
registers and RIP (besides the per-step bookkeeping). -/
theorem AgreesExcept.afterStep_writeResultPair (s : RamState) (length : Nat) {n : Nat}
    (r₁ r₂ : BitVec 5) (v₁ v₂ : RamState → BitVec n) (nextIP : BitVec 64) :
    AgreesExcept [.reg r₁, .reg r₂, .rip] s
      (afterStep s length fun t => writeResultPair t r₁ r₂ (v₁ t) (v₂ t) nextIP) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r =>
      have h₁ : r₁ ≠ r := fun h => hc (h ▸ List.mem_cons_self)
      have h₂ : r₂ ≠ r := fun h => hc (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)
      have := (Operand.read_afterStep s length
        (fun t => writeResultPair t r₁ r₂ (v₁ t) (v₂ t) nextIP) (.reg r : Operand 64)).trans
        (Operand.read_writeResultPair_of_ne (m := 64) _ h₁ h₂ _ _ _)
      simp only [Operand.read_reg64] at this
      exact this
    | flags => rfl
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
    | df => rfl
  · simp only [fixedPart, afterStep, finishStep, writeResultPair, Operand.write, afterFetches,
      beforeFetch, resetStepFields]

/-! ### Two byte-register destinations, AH–BH included -/

/-- `writeResultPair` for two byte-register operands (`Operand.gpr8`, lean-x86's `Write_GPR8`
twice, AH–BH included): `s` with `Next_IP` set, `d₁` set to `v₁` and then `d₂` to `v₂`. -/
def writeResultPair8 {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (d₁ d₂ : Operand 8)
    (v₁ v₂ : BitVec 8) (nextIP : BitVec 64) : X86.State σ :=
  d₂.write (d₁.write { s with Next_IP := nextIP } v₁) v₂

/-- `writePairOutputs` for two byte-register operands: `s` with `Next_IP` set, `oracleUsed`
oracle bits used up, the flags `f` stored, `d₁` set to `v₁` and then `d₂` to `v₂`. -/
def writePairOutputs8 {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (d₁ d₂ : Operand 8)
    (v₁ v₂ : BitVec 8) (f : StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) : X86.State σ :=
  d₂.write
    (d₁.write (setFlags { s with Next_IP := nextIP, oracle := oracleSkip s.oracle oracleUsed } f)
      v₁) v₂

/-- Register `byteRegGpr b` after no-REX byte register `a` is set to `v₁` and then `b` to `v₂`,
from the old values `x` of `a`'s register and `y` of `b`'s: when both bytes live in one register
(AL and AH), `b`'s byte is merged into the result of the first write. -/
def mergeByteRegPair (a b : BitVec 3) (v₁ v₂ : BitVec 8) (x y : BitVec 64) : BitVec 64 :=
  mergeByteReg b v₂ (if byteRegGpr a = byteRegGpr b then mergeByteReg a v₁ x else y)

private theorem read_reg64_write_reg64 {σ : Type} [PhysicalMemory σ] (s : X86.State σ)
    (r r' : BitVec 5) (v : BitVec 64) :
    (Operand.reg r' : Operand 64).read ((Operand.reg r : Operand 64).write s v) =
      if r = r' then v else (Operand.reg r' : Operand 64).read s := by
  split
  · subst r'
    simp [Operand.read, Operand.write_reg64]
  · rename_i hne
    exact Operand.read_write_reg_of_ne s hne v

/-- `writeResultPair8` of two no-REX byte registers is `writeResultPair` of their registers at 64
bits: the first register with its byte merged in, the second with `mergeByteRegPair`. -/
theorem writeResultPair8_byteReg {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (a b : BitVec 3)
    (v₁ v₂ : BitVec 8) (nextIP : BitVec 64) :
    writeResultPair8 s (Operand.byteReg a) (Operand.byteReg b) v₁ v₂ nextIP =
      writeResultPair s (byteRegGpr a) (byteRegGpr b)
        (mergeByteReg a v₁ ((Operand.reg (byteRegGpr a) : Operand 64).read s))
        (mergeByteRegPair a b v₁ v₂ ((Operand.reg (byteRegGpr a) : Operand 64).read s)
          ((Operand.reg (byteRegGpr b) : Operand 64).read s)) nextIP := by
  simp only [writeResultPair8, writeResultPair, Operand.write_byteReg_eq_reg64,
    read_reg64_write_reg64, mergeByteRegPair]
  rfl

/-- `writePairOutputs8` of two no-REX byte registers is `writePairOutputs` of their registers at
64 bits (as `writeResultPair8_byteReg`). -/
theorem writePairOutputs8_byteReg {σ : Type} [PhysicalMemory σ] (s : X86.State σ)
    (a b : BitVec 3) (v₁ v₂ : BitVec 8) (f : StatusFlags) (oracleUsed : Nat)
    (nextIP : BitVec 64) :
    writePairOutputs8 s (Operand.byteReg a) (Operand.byteReg b) v₁ v₂ f oracleUsed nextIP =
      writePairOutputs s (byteRegGpr a) (byteRegGpr b)
        (mergeByteReg a v₁ ((Operand.reg (byteRegGpr a) : Operand 64).read s))
        (mergeByteRegPair a b v₁ v₂ ((Operand.reg (byteRegGpr a) : Operand 64).read s)
          ((Operand.reg (byteRegGpr b) : Operand 64).read s)) f oracleUsed nextIP := by
  simp only [writePairOutputs8, writePairOutputs, Operand.write_byteReg_eq_reg64,
    read_reg64_write_reg64, mergeByteRegPair]
  rfl

/-- An operand write leaves the code segment alone. -/
theorem Operand.write_CS {σ : Type} [PhysicalMemory σ] {n : Nat} (s : X86.State σ)
    (op : Operand n) (v : BitVec n) : (op.write s v).CS = s.CS := by
  cases op <;> rfl

/-- An operand write leaves `IA32_EFER` alone. -/
theorem Operand.write_IA32_EFER {σ : Type} [PhysicalMemory σ] {n : Nat} (s : X86.State σ)
    (op : Operand n) (v : BitVec n) : (op.write s v).IA32_EFER = s.IA32_EFER := by
  cases op <;> rfl

/-- `writeResultPair8` leaves the code segment and `IA32_EFER` alone, so 64-bit mode stays. -/
theorem In64BitMode.writeResultPair8 {σ : Type} [PhysicalMemory σ] {s : X86.State σ}
    (h : In64BitMode s) (d₁ d₂ : Operand 8) (v₁ v₂ : BitVec 8) (nextIP : BitVec 64) :
    In64BitMode (X86Proofs.writeResultPair8 s d₁ d₂ v₁ v₂ nextIP) :=
  h.of_cs_lma_eq (by simp only [X86Proofs.writeResultPair8, Operand.write_CS])
    (by simp only [X86Proofs.writeResultPair8, Operand.write_IA32_EFER])

/-- `writePairOutputs8` leaves the code segment and `IA32_EFER` alone, so 64-bit mode stays. -/
theorem In64BitMode.writePairOutputs8 {σ : Type} [PhysicalMemory σ] {s : X86.State σ}
    (h : In64BitMode s) (d₁ d₂ : Operand 8) (v₁ v₂ : BitVec 8) (f : StatusFlags)
    (oracleUsed : Nat) (nextIP : BitVec 64) :
    In64BitMode (X86Proofs.writePairOutputs8 s d₁ d₂ v₁ v₂ f oracleUsed nextIP) :=
  h.of_cs_lma_eq (by simp only [X86Proofs.writePairOutputs8, Operand.write_CS]; rfl)
    (by simp only [X86Proofs.writePairOutputs8, Operand.write_IA32_EFER]; rfl)

end X86Proofs
