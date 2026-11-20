import X86Proofs.Program.Agrees

/-!
# Write-back without flags

`writeResult s dst v nextIP` is the form-level result of an instruction with one destination and
no flags (MOV, NOT; later MOVZX, LEA, loads): `s` with `Next_IP` set and the destination `dst` set to `v`. The
status flags and the oracle are untouched. It is `writeOutputs` without the flags.

For a step whose form ends in `writeResult` to a register, the same facts as for `writeOutputs`:
- `afterStep_writeResult_rip`: RIP after the step is `nextIP`;
- `ReadyToStep.afterStep_writeResult`: the state after the step is ready to step again;
- `AgreesExcept.afterStep_writeResult`: only the register and RIP change.

Generic (not specific to MOV). Used by MOV (hand-written) and by the
generated unary family's `flags = "none"` rows (NOT).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- Form-level write-back for an instruction with one destination and no flags: `s` with
`Next_IP` set (RIP itself is advanced later, by `step`) and the destination `dst` set to `v`. -/
def writeResult {σ : Type} [PhysicalMemory σ] {n : Nat} (s : X86.State σ) (dst : Operand n)
    (v : BitVec n) (nextIP : BitVec 64) : X86.State σ :=
  dst.write { s with Next_IP := nextIP } v

/-- After a 64-bit `writeResult` to register `r`, reading `r` gives the written value. -/
@[simp] theorem Operand.read_writeResult_self {σ : Type} [PhysicalMemory σ] (s : X86.State σ)
    (r : BitVec 5) (v : BitVec 64) (nextIP : BitVec 64) :
    (Operand.reg r : Operand 64).read (writeResult s (.reg r) v nextIP) = v := by
  simp [writeResult]

/-- After a 32-bit `writeResult` to register `r`, the full 64-bit register `r` is the written
value zero-extended: the upper half is zero. -/
@[simp] theorem Operand.read_writeResult_self32 {σ : Type} [PhysicalMemory σ] (s : X86.State σ)
    (r : BitVec 5) (v : BitVec 32) (nextIP : BitVec 64) :
    (Operand.reg r : Operand 64).read (writeResult s (.reg r : Operand 32) v nextIP) =
      v.setWidth 64 := by
  simp [writeResult]

/-- After an `n`-bit `writeResult` to register `r`, the full 64-bit register `r` is the written
value merged into its old value (`mergeGPR`: the low `n` bits replaced; at 32 bits,
zero-extended). -/
theorem Operand.read_writeResult_self_merge {σ : Type} [PhysicalMemory σ] {n : Nat}
    (s : X86.State σ) (r : BitVec 5) (v : BitVec n) (nextIP : BitVec 64) :
    (Operand.reg r : Operand 64).read (writeResult s (.reg r : Operand n) v nextIP) =
      mergeGPR n v ((Operand.reg r : Operand 64).read s) := by
  simp [writeResult, Operand.write]

/-- After a `writeResult` (of any size) to register `r`, a register with a different number reads
as before (at any size). -/
theorem Operand.read_writeResult_of_ne {σ : Type} [PhysicalMemory σ] {n m : Nat}
    (s : X86.State σ) {r r' : BitVec 5} (hne : r ≠ r') (v : BitVec n) (nextIP : BitVec 64) :
    (Operand.reg r' : Operand m).read (writeResult s (.reg r) v nextIP) =
      (Operand.reg r' : Operand m).read s := by
  have hi : gprIndex r ≠ gprIndex r' := fun h => hne (BitVec.eq_of_toNat_eq (Fin.mk.inj_iff.mp h))
  simp [writeResult, Operand.write, Operand.read, Fin.val_ne_of_ne hi]

/-- `writeResult` to no-REX byte register `r` (AL–BL, AH–BH) is a 64-bit `writeResult` of register
`byteRegGpr r`, the byte merged into its old value (`mergeByteReg`). -/
theorem writeResult_byteReg {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 3)
    (v : BitVec 8) (nextIP : BitVec 64) :
    writeResult s (Operand.byteReg r) v nextIP =
      writeResult s (Operand.reg (byteRegGpr r) : Operand 64)
        (mergeByteReg r v ((Operand.reg (byteRegGpr r) : Operand 64).read s)) nextIP := by
  simp only [writeResult, Operand.write_byteReg_eq_reg64]
  rfl

/-- After a form that ends in `writeResult … nextIP`, RIP is `nextIP`. -/
theorem afterStep_writeResult_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    {n : Nat} (dst : Operand n) (v : RamState → BitVec n) (nextIP : BitVec 64) :
    (afterStep s length fun t => writeResult t dst (v t) nextIP).RIP = nextIP := by
  cases dst <;>
  simp [afterStep, finishStep, writeResult, Operand.write, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

/--
Preservation. If `s` is ready to step and the instruction's form ends in `writeResult` to a
register, the state after the step is ready to step again: only a general-purpose register, the
oracle, `Next_IP`, RIP and per-step bookkeeping change.
-/
theorem ReadyToStep.afterStep_writeResult [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (r : BitVec 5) (v : RamState → BitVec n) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t => writeResult t (.reg r) (v t) nextIP) := by
  have hst : SameControls s (afterStep s length fun t => writeResult t (.reg r) (v t) nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass, hc.debug,
      hc.aet⟩,
    ⟨h.memory.cr3, h.memory.tables⟩,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, hr.tf, hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-- A step whose form ends in `writeResult` to register `r` changes only `r` and RIP (besides the
per-step bookkeeping). -/
theorem AgreesExcept.afterStep_writeResult (s : RamState) (length : Nat) {n : Nat} (r : BitVec 5)
    (v : RamState → BitVec n) (nextIP : BitVec 64) :
    AgreesExcept [.reg r, .rip] s
      (afterStep s length fun t => writeResult t (.reg r) (v t) nextIP) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r' =>
      have hne : r ≠ r' := fun h => hc (h ▸ List.mem_cons_self)
      have := (Operand.read_afterStep s length
        (fun t => writeResult t (.reg r) (v t) nextIP) (.reg r' : Operand 64)).trans
        (Operand.read_writeResult_of_ne (m := 64) _ hne _ _)
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
  · simp only [fixedPart, afterStep, finishStep, writeResult, Operand.write, afterFetches,
      beforeFetch, resetStepFields]

/-! ### No-REX byte registers (AL–BL, AH–BH) -/

/-- Preservation for a form that ends in `writeResult` to a no-REX byte register. -/
theorem ReadyToStep.afterStep_writeResult_byteReg [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (r : BitVec 3) (v : RamState → BitVec 8) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t => writeResult t (Operand.byteReg r) (v t) nextIP) := by
  simp only [writeResult_byteReg]
  exact ReadyToStep.afterStep_writeResult h length _ _ nextIP

/-- `writeResult` (to any operand) leaves the code segment alone. -/
theorem writeResult_CS {σ : Type} [PhysicalMemory σ] {n : Nat} (s : X86.State σ) (dst : Operand n)
    (v : BitVec n) (nextIP : BitVec 64) : (writeResult s dst v nextIP).CS = s.CS := by
  cases dst <;> rfl

/-- `writeResult` (to any operand) leaves `IA32_EFER` alone. -/
theorem writeResult_IA32_EFER {σ : Type} [PhysicalMemory σ] {n : Nat} (s : X86.State σ)
    (dst : Operand n) (v : BitVec n) (nextIP : BitVec 64) :
    (writeResult s dst v nextIP).IA32_EFER = s.IA32_EFER := by
  cases dst <;> rfl

/-- In 64-bit mode after a `writeResult` (to any operand) if in 64-bit mode before it. -/
theorem In64BitMode.writeResult {σ : Type} [PhysicalMemory σ] {n : Nat} {s : X86.State σ}
    (h : In64BitMode s) (dst : Operand n) (v : BitVec n) (nextIP : BitVec 64) :
    In64BitMode (writeResult s dst v nextIP) :=
  h.of_cs_lma_eq (writeResult_CS s dst v nextIP) (by rw [writeResult_IA32_EFER])

/-- `writeOutputs` (to any operand) leaves the code segment alone. -/
theorem writeOutputs_CS {σ : Type} [PhysicalMemory σ] {n : Nat} (s : X86.State σ)
    (dst : Operand n) (out : BitVec n × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    (writeOutputs s dst out oracleUsed nextIP).CS = s.CS := by
  cases dst <;> rfl

/-- `writeOutputs` (to any operand) leaves `IA32_EFER` alone. -/
theorem writeOutputs_IA32_EFER {σ : Type} [PhysicalMemory σ] {n : Nat} (s : X86.State σ)
    (dst : Operand n) (out : BitVec n × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    (writeOutputs s dst out oracleUsed nextIP).IA32_EFER = s.IA32_EFER := by
  cases dst <;> rfl

end X86Proofs
