import X86Proofs.Core.X87Trans

/-!
# FPATAN specification

lean-x86's `Operations.FPATAN x y` (`x` = ST(0), `y` = ST(1)), with both not empty and every
exception masked: arctan(ST(1) / ST(0)) by the numerical binding (`FP87.Atan`, stated relative to
the binding: `x87BindVal`, `X87BindOk`); the status word `x87PatanFsw` (C0, C2, C3 from the oracle,
C1 := rounded up, the flags ORed in).
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers X86.Runtime

theorem fpatan_operation [Bindings] (s : RamState) (x y : BitVec 80)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (h1 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 1) ≠ 3)
    (hm : FcwMasked s.FP87_Control) (hok : X87BindOk (FP87.Atan x y) s.FP87_Control) :
    (X86.Instructions.Operations.FPATAN x y : PartialSpecM X86.Exception RamState _).run s =
      some (.ok ((x87BindVal (FP87.Atan x y) s.FP87_Control).1, true), { s with
        oracle := oracleSkip s.oracle 3
        FP87_Status := x87PatanFsw s.FP87_Status s.oracle
          (x87BindVal (FP87.Atan x y) s.FP87_Control).2.1
          (x87BindVal (FP87.Atan x y) s.FP87_Control).2.2 }) := by
  unfold X86.Instructions.Operations.FPATAN
  pspec_run_until [X86.UNSPECIFIED => unspecified1_run _,
    FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by decide)]
  have h0' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3) = false := by simpa using h0
  have h1' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 1) == 3) = false := by simpa using h1
  x87_cond [h0', h1', show BitVec.ofInt 3 1 = 1 from rfl]
  pspec_run [FP87.Atan => X87BindOk.run (by exact hok),
    FP87.Is_Unmasked_Pre_Computation_Exception => isUnmaskedPre_masked _ _ (by exact hm),
    FP87.Process_Exceptions => processExceptions_run _ _ (by exact hm)]
  simp only [Int.reduceToNat, extractLsb'_zero_self, oracleSkip_oracleSkip, Bool.not_false,
    Bool.and_true]
  rfl

end X86Proofs
