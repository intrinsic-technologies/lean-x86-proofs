import X86Proofs.Core.X87Trans

/-!
# FYL2XP1 specification

lean-x86's `Operations.FYL2XP1 x y` (`x` = ST(0), `y` = ST(1)), with both not empty and every
exception masked: ST(1) × log₂(ST(0) + 1) by the numerical binding (`FP87.Log2_Add_Multiply`, stated
relative to the
binding: `x87BindVal`, `X87BindOk`) and the status word `x87OpStatus` (C0, C2, C3 from the
oracle, C1 := rounded up, the flags).
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers X86.Runtime

theorem fyl2xp1_operation [Bindings] (s : RamState) (x y : BitVec 80)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (h1 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 1) ≠ 3)
    (hm : FcwMasked s.FP87_Control) (hok : X87BindOk (FP87.Log2_Add_Multiply x y) s.FP87_Control) :
    (X86.Instructions.Operations.FYL2XP1 x y : PartialSpecM X86.Exception RamState _).run s =
      some (.ok ((x87BindVal (FP87.Log2_Add_Multiply x y) s.FP87_Control).1,
        x87OpStatus s.FP87_Status s.oracle
            (x87BindVal (FP87.Log2_Add_Multiply x y) s.FP87_Control).2.1
          (x87BindVal (FP87.Log2_Add_Multiply x y) s.FP87_Control).2.2),
        { s with oracle := oracleSkip s.oracle 3 }) := by
  unfold X86.Instructions.Operations.FYL2XP1
  pspec_run_until [X86.UNSPECIFIED => unspecified1_run _,
    FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by decide)]
  have h0' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3) = false := by simpa using h0
  have h1' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 1) == 3) = false := by simpa using h1
  x87_cond [h0', h1', show BitVec.ofInt 3 1 = 1 from rfl]
  pspec_run [FP87.Log2_Add_Multiply => X87BindOk.run (by exact hok),
    FP87.Is_Unmasked_Pre_Computation_Exception => isUnmaskedPre_masked _ _ (by exact hm)]
  simp only [Int.reduceToNat, extractLsb'_zero_self, oracleSkip_oracleSkip, Bool.not_false,
    Bool.and_true]
  rfl

end X86Proofs
