import X86Proofs.Core.X87Trans

/-!
# FSIN specification

lean-x86's `Operations.FSIN x` (`x` = ST(0)), with ST(0) not empty and every exception masked:
sin ST(0) by the numerical binding (`FP87.Sin`, stated relative to the binding: `x87BindVal`,
`X87BindOk`): the result, whether it was rounded up, whether `x` was out of range (then the
result is not written) and the flags; the status word `x87SinFsw` (C0, C3 from the oracle, C1 :=
rounded up, C2 := out of range, the flags ORed in).
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers X86.Runtime

theorem fsin_operation [Bindings] (s : RamState) (x : BitVec 80)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (hm : FcwMasked s.FP87_Control) (hok : X87BindOk (FP87.Sin x) s.FP87_Control) :
    (X86.Instructions.Operations.FSIN x : PartialSpecM X86.Exception RamState _).run s =
      some (.ok ((x87BindVal (FP87.Sin x) s.FP87_Control).1,
        !(x87BindVal (FP87.Sin x) s.FP87_Control).2.2.1), { s with
        oracle := oracleSkip s.oracle 2
        FP87_Status := x87SinFsw s.FP87_Status s.oracle
          (x87BindVal (FP87.Sin x) s.FP87_Control).2.1
          (x87BindVal (FP87.Sin x) s.FP87_Control).2.2.1
          (x87BindVal (FP87.Sin x) s.FP87_Control).2.2.2 }) := by
  unfold X86.Instructions.Operations.FSIN
  pspec_run_until [X86.UNSPECIFIED => unspecified1_run _,
    FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by decide)]
  have h0' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3) = false := by simpa using h0
  x87_cond [h0']
  pspec_run [FP87.Sin => X87BindOk.run (by exact hok),
    FP87.Is_Unmasked_Pre_Computation_Exception => isUnmaskedPre_masked _ _ (by exact hm),
    X86.Helpers.Bit => partialSpecM_liftM_run_of_ok (bit_eq _) _,
    FP87.Process_Exceptions => processExceptions_run _ _ (by exact hm)]
  simp only [Int.reduceToNat, extractLsb'_zero_self, oracleSkip_oracleSkip, Bool.not_false,
    Bool.and_true, extractLsb'_setSlice_one _ 10 _ (by decide : 10 < 16)]
  cases (x87BindVal (FP87.Sin x) s.FP87_Control).2.2.1 <;> rfl

end X86Proofs
