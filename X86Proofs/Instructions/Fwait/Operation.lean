import X86Proofs.Instructions.Fnop.Operation

/-!
# FWAIT specification

`FWAIT` (`WAIT`): checks for a pending unmasked x87 exception; lean-x86's `Operations.FWAIT` then
draws all four condition codes from its oracle (the SDM leaves them undefined).
-/

namespace X86Proofs

open X86 X86.Helpers X86.Runtime

theorem fwait_operation {σ : Type} [X86.Helpers.Unimplemented_Feature.Binding σ]
    (s : X86.State σ) (hes : fswES s.FP87_Status = 0) :
    (X86.Instructions.Operations.FWAIT : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (), { s with
        oracle := oracleSkip s.oracle 4
        FP87_Status := fswCCOracle s.FP87_Status s.oracle }) := by
  unfold X86.Instructions.Operations.FWAIT
  spec_run [FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
    X86.UNSPECIFIED => unspecified1_run _]

end X86Proofs
