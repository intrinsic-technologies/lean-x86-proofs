import X86Proofs.Core.X87Trans

/-!
# FCOS specification

lean-x86's `Operations.FCOS x` (`x` = ST(0)), with ST(0) not empty and every exception masked:
cos ST(0) by the numerical binding (`FP87.Cos`, stated relative to the binding: `x87BindVal`,
`X87BindOk`): the result, whether it was rounded up, whether `x` was out of range (then the
result is not written, and C1 is the oracle's next bit) and the flags; the status word
`x87CosFsw` (C0, C3 from the oracle, C2 := out of range, C1 := rounded up, the flags ORed in).
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers X86.Runtime

theorem fcos_operation [Bindings] (s : RamState) (x : BitVec 80)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (hm : FcwMasked s.FP87_Control) (hok : X87BindOk (FP87.Cos x) s.FP87_Control) :
    (X86.Instructions.Operations.FCOS x : PartialSpecM X86.Exception RamState _).run s =
      some (.ok ((x87BindVal (FP87.Cos x) s.FP87_Control).1,
        !(x87BindVal (FP87.Cos x) s.FP87_Control).2.2.1), { s with
        oracle := oracleSkip s.oracle
          (if (x87BindVal (FP87.Cos x) s.FP87_Control).2.2.1 = true then 3 else 2)
        FP87_Status := x87CosFsw s.FP87_Status s.oracle
          (x87BindVal (FP87.Cos x) s.FP87_Control).2.1
          (x87BindVal (FP87.Cos x) s.FP87_Control).2.2.1
          (x87BindVal (FP87.Cos x) s.FP87_Control).2.2.2 }) := by
  unfold X86.Instructions.Operations.FCOS
  pspec_run_until [X86.UNSPECIFIED => unspecified1_run _,
    FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by decide)]
  have h0' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3) = false := by simpa using h0
  x87_cond [h0']
  pspec_run_until [FP87.Cos => X87BindOk.run (by exact hok),
    X86.Helpers.Bit => partialSpecM_liftM_run_of_ok (bit_eq _) _]
  cases (x87BindVal (FP87.Cos x) s.FP87_Control).2.2.1 <;>
  · pspec_run [X86.UNSPECIFIED => unspecified1_run _,
      X86.Helpers.Bit => partialSpecM_liftM_run_of_ok (bit_eq _) _,
      FP87.Is_Unmasked_Pre_Computation_Exception => isUnmaskedPre_masked _ _ (by exact hm),
      FP87.Process_Exceptions => processExceptions_run _ _ (by exact hm)]
    simp only [Int.reduceToNat, extractLsb'_zero_self, oracleSkip_oracleSkip, Bool.not_false,
      Bool.and_true, extractLsb'_setSlice_one_ne (n := 16) _ 9 10 _ (by decide) (by decide),
      extractLsb'_setSlice_one _ 10 _ (by decide : 10 < 16)]
    rfl

end X86Proofs
