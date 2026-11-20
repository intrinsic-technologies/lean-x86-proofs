import X86Proofs.Core.X87

/-!
# FXCH specification

`FXCH ST(i)`: exchange ST(0) and ST(i). lean-x86's `Operations.FXCH` leaves C1 := 0 and draws C0,
C2, C3 from its oracle; with ST(0) and ST(i) not empty there is no exception.
-/

namespace X86Proofs

open X86 X86.Helpers X86.Runtime

/-- The status word `Operations.FXCH` leaves. -/
def fxchStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) : BitVec 16 :=
  fswOrFlags (fswC1Zero fsw o) 0

@[simp] theorem fswTop_fxchStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswTop (fxchStatus fsw o) = fswTop fsw := by
  simp [fxchStatus]

@[simp] theorem fswES_fxchStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswES (fxchStatus fsw o) = fswES fsw := by
  simp [fxchStatus]

theorem fswRest_fxchStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswRest (fxchStatus fsw o) = fswRest fsw := by
  simp [fxchStatus]

theorem fswCC_fxchStatus_c1 (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswCC (fxchStatus fsw o) &&& 2 = 0 := by
  simp only [fxchStatus, fswCC_fswOrFlags]
  exact fswCC_fswC1Zero fsw o

theorem fxch_operation {σ : Type} (s : X86.State σ) (src1 src2 : BitVec 80) (i : BitVec 3)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (hi : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + i) ≠ 3)
    (hm : FcwMasked s.FP87_Control) :
    (X86.Instructions.Operations.FXCH src1 src2 i : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (src2, src1, true), { s with
        oracle := oracleSkip s.oracle 3
        FP87_Status := fxchStatus s.FP87_Status s.oracle }) := by
  unfold X86.Instructions.Operations.FXCH
  spec_run
      [FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by first | decide | exact unsigned_range _ rfl),
    X86.UNSPECIFIED => unspecified1_run _]
  have h0' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3) = false := by simpa using h0
  have hi' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + i) == 3) = false := by
    simpa using hi
  x87_cond [h0', hi']
  spec_run [FP87.Is_Unmasked_Pre_Computation_Exception => isUnmaskedPre_masked _ _ (by exact hm),
    FP87.Process_Exceptions => processExceptions_run _ _ (by exact hm)]

end X86Proofs
