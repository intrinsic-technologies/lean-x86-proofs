import X86Proofs.Instructions.Fnop.Operation
import X86.Instructions.FSTCW

/-!
# FNSTCW specification

`FNSTCW m16`: the control word is stored, without checking for a pending exception. lean-x86's
`Operations.FNSTCW` draws all four condition codes from its oracle (the SDM leaves them undefined)
and returns the control word.
-/

namespace X86Proofs

open X86 X86.Helpers X86.Runtime

theorem fnstcw_operation {σ : Type} (s : X86.State σ) :
    (X86.Instructions.Operations.FNSTCW : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok s.FP87_Control, { s with
        oracle := oracleSkip s.oracle 4
        FP87_Status := fswCCOracle s.FP87_Status s.oracle }) := by
  unfold X86.Instructions.Operations.FNSTCW
  spec_run [MonadState.get => specM_get_run _, X86.UNSPECIFIED => unspecified1_run _]

end X86Proofs
