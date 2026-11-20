import X86Proofs.Core.X87

/-!
# FNOP specification

`FNOP`: no operation; lean-x86's `Operations.FNOP` checks for a pending exception and draws all
four condition codes from its oracle (the SDM leaves them undefined).
-/

namespace X86Proofs

open X86 X86.Helpers X86.Runtime

/-- The status word with all four condition codes from the oracle `o` (C0, C1, C2, C3 in that
order). -/
def fswCCOracle (fsw : BitVec 16) (o : X86.Runtime.Oracle) : BitVec 16 :=
  fswSetC fsw (oBit o 0) (oBit o 1) (oBit o 2) (oBit o 3)

@[simp] theorem fswTop_fswCCOracle (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswTop (fswCCOracle fsw o) = fswTop fsw := fswTop_fswSetC _ _ _ _ _

@[simp] theorem fswES_fswCCOracle (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswES (fswCCOracle fsw o) = fswES fsw := fswES_fswSetC _ _ _ _ _

@[simp] theorem fswRest_fswCCOracle (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswRest (fswCCOracle fsw o) = fswRest fsw := fswRest_fswSetC _ _ _ _ _

theorem fnop_operation {σ : Type} [X86.Helpers.Unimplemented_Feature.Binding σ]
    (s : X86.State σ) (hes : fswES s.FP87_Status = 0) :
    (X86.Instructions.Operations.FNOP : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (), { s with
        oracle := oracleSkip s.oracle 4
        FP87_Status := fswCCOracle s.FP87_Status s.oracle }) := by
  unfold X86.Instructions.Operations.FNOP
  spec_run [FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
    X86.UNSPECIFIED => unspecified1_run _]

end X86Proofs
