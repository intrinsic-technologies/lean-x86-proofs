import X86Proofs.Program.ReadWrite.Stack
import X86Proofs.Program.ReadWrite.WriteResult

/-!
# The direction flag and the other non-status bits of RFLAGS

A form that ends in `writeResult` of the direction flag (`Operand.df`, CLD and STD): what the step
leaves (`Operand.read_afterStep_writeResult_df`, `afterStep_writeResult_rip`), its frame
(`AgreesExcept.afterStep_writeResult_df`: only DF and RIP change) and preservation of
`ReadyToStep` (`ReadyToStep.afterStep_writeResult_df`: TF and RF are not DF).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- After a form that ends in `writeResult` of DF, DF is the value written. -/
theorem Operand.read_afterStep_writeResult_df (s : RamState) (length : Nat) (v : BitVec 1)
    (nextIP : BitVec 64) :
    (Operand.df : Operand 1).read
      (afterStep s length fun t => writeResult t (Operand.df : Operand 1) v nextIP) = v := by
  simp only [Operand.read_df, afterStep, finishStep, writeResult, Operand.write_df,
    dfBit_setSlice_df]

/-- A step whose form ends in `writeResult` of DF changes only DF and RIP (besides the per-step
bookkeeping). -/
theorem AgreesExcept.afterStep_writeResult_df (s : RamState) (length : Nat) (v : BitVec 1)
    (nextIP : BitVec 64) :
    AgreesExcept [.df, .rip] s
      (afterStep s length fun t => writeResult t (Operand.df : Operand 1) v nextIP) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r =>
      show _ = _
      simp only [afterStep, finishStep, writeResult, Operand.write_df, afterFetches, beforeFetch,
        resetStepFields]
    | flags =>
      show _ = _
      simp only [afterStep, finishStep, writeResult, Operand.write_df, afterFetches_RFLAGS,
        beforeFetch_RFLAGS, StatusFlags.ofRFLAGS_setSlice_df]
    | df => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem addr len => exact fun _ _ => rfl
    | xmm x =>
      exact Component.agrees_xmm_of_zmm (by
        simp only [afterStep, finishStep, writeResult, Operand.write_df, afterFetches, beforeFetch,
          resetStepFields]) x
    | mxcsr =>
      show _ = _
      simp only [afterStep, finishStep, writeResult, Operand.write_df, afterFetches, beforeFetch,
        resetStepFields]
    | _ =>
      simp only [Component.Agrees, afterStep, finishStep, writeResult, Operand.write_df,
        afterFetches, beforeFetch, resetStepFields, fpuPtrOf]
  · simp only [fixedPart, afterStep, finishStep, writeResult, Operand.write_df, afterFetches,
      beforeFetch, resetStepFields, clearDirectionFlag_clearStatusFlags_setSlice_df]

/-- Preservation for a form that ends in `writeResult` of DF. -/
theorem ReadyToStep.afterStep_writeResult_df [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (v : BitVec 1) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t => writeResult t (Operand.df : Operand 1) v nextIP) :=
  h.of_agreesExcept (AgreesExcept.afterStep_writeResult_df s length v nextIP) h.memory.tables

end X86Proofs
