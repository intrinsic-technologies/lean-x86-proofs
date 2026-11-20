import X86Proofs.Program.ReadWrite.Load
import X86Proofs.Step.AfterStep
import X86Proofs.Step.Address
import X86Proofs.Program.Effect

/-!
# Loads with flags: a memory read, then `writeOutputs` to a register

For the forms that read a memory operand and combine it with a register into a register and the
status flags (`xor r, m`; later `add r, m`, …): their form result is
`writeOutputs (dataAccess t "load") (.reg r) out oracleUsed nextIP`, the read's bookkeeping followed
by the write-back. The step facts are those of `writeOutputs` (`Step/AfterStep.lean`,
`Program/Agrees.lean`) with the load's bookkeeping in front:

- `afterStep_loadWriteOutputs_rip`: RIP after the step is `nextIP`;
- `ReadyToStep.afterStep_loadWriteOutputs`: the state after the step is ready to step again;
- `AgreesExcept.afterStep_loadWriteOutputs`: only the register, the flags and RIP change.

`movLoadLen_low`: the length bound of an `AddrMode` instruction with a one-byte prefix, from its
bytes placed in memory.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- After a load form ending in `writeOutputs … nextIP`, RIP is `nextIP`. -/
theorem afterStep_loadWriteOutputs_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    {n : Nat} (dst : Operand n) (out : RamState → BitVec n × StatusFlags) (oracleUsed : Nat)
    (nextIP : BitVec 64) :
    (afterStep s length fun t =>
      writeOutputs (dataAccess t "load") dst (out t) oracleUsed nextIP).RIP = nextIP := by
  cases dst <;>
  simp [afterStep, finishStep, writeOutputs, Operand.write, setFlags, dataAccess, afterFetches,
    beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- Preservation for a load into a register with flags: only that register, the status flags,
the oracle, the trace, `Next_IP`, RIP and per-step bookkeeping change. -/
theorem ReadyToStep.afterStep_loadWriteOutputs [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (r : BitVec 5) (out : RamState → BitVec n × StatusFlags)
    (oracleUsed : Nat) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t =>
      writeOutputs (dataAccess t "load") (.reg r) (out t) oracleUsed nextIP) := by
  have hst : SameControls s (afterStep s length fun t =>
      writeOutputs (dataAccess t "load") (.reg r) (out t) oracleUsed nextIP) :=
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

/-- A load into register `r` with flags changes only `r`, the status flags and RIP (besides the
per-step bookkeeping). -/
theorem AgreesExcept.afterStep_loadWriteOutputs (s : RamState) (length : Nat) {n : Nat} (r : BitVec 5)
    (out : RamState → BitVec n × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    AgreesExcept [.reg r, .flags, .rip] s
      (afterStep s length fun t =>
        writeOutputs (dataAccess t "load") (.reg r) (out t) oracleUsed nextIP) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r' =>
      have hne : r ≠ r' := fun h => hc (h ▸ List.mem_cons_self)
      have := (Operand.read_afterStep s length
        (fun t => writeOutputs (dataAccess t "load") (.reg r) (out t) oracleUsed nextIP)
        (.reg r' : Operand 64)).trans
        (Operand.read_writeOutputs_of_ne (m := 64) _ hne _ _ _)
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
  · simp only [fixedPart, afterStep, finishStep, writeOutputs, Operand.write, setFlags, dataAccess,
      afterFetches, beforeFetch, resetStepFields, clearStatusFlags_store]

/-- The length bound a load triple needs, from the code being in memory below 4 GiB. -/
theorem movLoadLen_low {s : RamState} {p : BitVec 64} {b0 op modrm : UInt8}
    (hp : s.RIP = p) (am : AddrMode) (hcode : CodeIn (codeRange p (b0 :: op :: modrm :: am.tail)) s) :
    s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
  subst hp
  have := am.tail_length_le
  have := hcode.low (by simp) (by simp; omega)
  simp only [List.length_cons] at this
  omega

end X86Proofs
