import X86Proofs.Core.X87

/-!
# FCHS specification

`FCHS`: ST(0) := −ST(0), the sign bit (79) inverted. lean-x86's `Operations.FCHS` computes the
status word from the current one, C1 := 0 and C0, C2, C3 from its oracle; with ST(0) not empty
there is no exception.
-/

namespace X86Proofs

open X86 X86.Helpers X86.Runtime

/-- The value with its sign inverted. -/
def fchsSpec (x : BitVec 80) : BitVec 80 := fprSetSign x (~~~ fprSign x)

theorem fp87Negate_eq (x : BitVec 80) : FP87.Negate x = .ok (fchsSpec x) := rfl

theorem fchs_operation {σ : Type} (s : X86.State σ) (src : BitVec 80)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3) :
    (X86.Instructions.Operations.FCHS src : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (fchsSpec src, fswC1Zero s.FP87_Status s.oracle),
        { s with oracle := oracleSkip s.oracle 3 }) := by
  unfold X86.Instructions.Operations.FCHS
  spec_run [MonadState.get => specM_get_run _, FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by decide),
    X86.UNSPECIFIED => unspecified1_run _]
  have h0' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3) = false := by simpa using h0
  x87_cond [h0']
  spec_run [liftM => liftM_run_of_ok (fp87Negate_eq _) _]

end X86Proofs
