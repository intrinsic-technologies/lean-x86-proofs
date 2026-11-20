import X86Proofs.Core.X87Trans

/-!
# F2XM1 specification

lean-x86's `Operations.F2XM1 x`, with ST(0) not empty: 2^x − 1 by the numerical binding
(`FP87.Power2Minus_One`, stated relative to the binding: `x87BindVal`, `X87BindOk`) and the status
word `x87OpStatus` (C0, C2, C3 from the oracle, C1 := rounded up, the flags).
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers X86.Runtime

theorem f2xm1_operation [Bindings] (s : RamState) (x : BitVec 80)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (hok : X87BindOk (FP87.Power2Minus_One x) s.FP87_Control) :
    (X86.Instructions.Operations.F2XM1 x : PartialSpecM X86.Exception RamState _).run s =
      some (.ok ((x87BindVal (FP87.Power2Minus_One x) s.FP87_Control).1,
        x87OpStatus s.FP87_Status s.oracle (x87BindVal (FP87.Power2Minus_One x) s.FP87_Control).2.1
          (x87BindVal (FP87.Power2Minus_One x) s.FP87_Control).2.2),
        { s with oracle := oracleSkip s.oracle 3 }) := by
  unfold X86.Instructions.Operations.F2XM1
  pspec_run_until [X86.UNSPECIFIED => unspecified1_run _,
    FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by decide)]
  have h0' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3) = false := by simpa using h0
  x87_cond [h0']
  pspec_run [FP87.Power2Minus_One => X87BindOk.run (by exact hok),
    X86.Helpers.Bit => partialSpecM_liftM_run_of_ok (bit_eq _) _]
  simp only [Int.reduceToNat, extractLsb'_zero_self, oracleSkip_oracleSkip]
  rfl

end X86Proofs
