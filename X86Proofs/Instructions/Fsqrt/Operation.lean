import X86Proofs.Core.X87Arith

/-!
# FSQRT specification

lean-x86's `Operations.FSQRT x`, with ST(0) not empty and every exception masked: the square root
of `x` (`x87Sqrt`, lean-x86's `FP87.Sqrt` at the control word) and the status word `x87OpStatus`
(C0, C2, C3 from the oracle, C1 := rounded up, the flags).
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers X86.Runtime

theorem fsqrt_operation (s : RamState) (x : BitVec 80)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (hm : FcwMasked s.FP87_Control) (hok : X87SqrtOk s.FP87_Control x) :
    (X86.Instructions.Operations.FSQRT x : SpecM X86.Exception RamState _).run s =
      (.ok ((x87Sqrt s.FP87_Control x).1, x87OpStatus s.FP87_Status s.oracle
        (x87Sqrt s.FP87_Control x).2.1 (x87Sqrt s.FP87_Control x).2.2),
        { s with oracle := oracleSkip s.oracle 3 }) := by
  unfold X86.Instructions.Operations.FSQRT
  spec_run_until [MonadState.get => specM_get_run _, X86.UNSPECIFIED => unspecified1_run _,
    FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by decide)]
  have h0' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3) = false := by simpa using h0
  x87_cond [h0']
  spec_run_until [FP87.Sqrt => fp87Sqrt_run x _ (by exact hm) (by exact hok),
    FP87.Is_Unmasked_Pre_Computation_Exception => isUnmaskedPre_masked _ _ (by exact hm)]
  simp only [Int.reduceToNat, extractLsb'_zero_self, oracleSkip_oracleSkip, Bool.not_false,
    Bool.and_true]
  rfl

end X86Proofs
