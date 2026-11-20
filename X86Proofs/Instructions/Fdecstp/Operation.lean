import X86Proofs.Core.X87

/-!
# FDECSTP specification

`FDECSTP`: TOP := TOP − 1; the tags and registers are unchanged. lean-x86's
`Operations.FDECSTP` leaves C1 := 0 and draws C0, C2, C3 from its oracle.
-/

namespace X86Proofs

open X86 X86.Helpers X86.Runtime

theorem fdecstp_operation {σ : Type} (s : X86.State σ) :
    (X86.Instructions.Operations.FDECSTP : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (), { s with
        oracle := oracleSkip s.oracle 3
        FP87_Status := fswSetTop (fswC1Zero s.FP87_Status s.oracle)
          (fswTop (fswC1Zero s.FP87_Status s.oracle) - 1) }) := by
  unfold X86.Instructions.Operations.FDECSTP
  spec_run [X86.UNSPECIFIED => unspecified1_run _, X86.FP87_Status.TOP => fp87StatusTOP_run _,
    liftM => liftM_run_of_ok (subInt3_one _) _]

end X86Proofs
