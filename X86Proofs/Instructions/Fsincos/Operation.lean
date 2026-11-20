import X86Proofs.Core.X87Trans

/-!
# FSINCOS specification

lean-x86's `Operations.FSINCOS x` (`x` = ST(0)), with ST(0) not empty, ST(7) empty (the push does
not overflow) and every exception masked: sin ST(0) and cos ST(0) by the numerical binding
(`FP87.Sin_Cos`,
stated relative to the binding: `x87BindVal`, `X87BindOk`): the new ST(0) and ST(1), whether the
result was rounded up, whether `x` was out of range (then nothing is written) and the flags; the
status word `x87CosFsw`, as for FCOS (C0, C3 from the oracle, C2 := out of range, C1 := rounded up,
or the oracle's next bit when the operand is out of range: lean-x86 leaves C1 undefined then;
the flags ORed in).
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers X86.Runtime

theorem fsincos_operation [Bindings] (s : RamState) (x : BitVec 80)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (h7 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 7) = 3)
    (hm : FcwMasked s.FP87_Control) (hok : X87BindOk (FP87.Sin_Cos x) s.FP87_Control) :
    (X86.Instructions.Operations.FSINCOS x : PartialSpecM X86.Exception RamState _).run s =
      some (.ok ((x87BindVal (FP87.Sin_Cos x) s.FP87_Control).1,
        (x87BindVal (FP87.Sin_Cos x) s.FP87_Control).2.1,
        !(x87BindVal (FP87.Sin_Cos x) s.FP87_Control).2.2.2.1), { s with
        oracle := oracleSkip s.oracle
          (if (x87BindVal (FP87.Sin_Cos x) s.FP87_Control).2.2.2.1 = true then 3 else 2)
        FP87_Status := x87CosFsw s.FP87_Status s.oracle
          (x87BindVal (FP87.Sin_Cos x) s.FP87_Control).2.2.1
          (x87BindVal (FP87.Sin_Cos x) s.FP87_Control).2.2.2.1
          (x87BindVal (FP87.Sin_Cos x) s.FP87_Control).2.2.2.2 }) := by
  have h7' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 7) == 3) = true := by simpa using h7
  have h0' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3) = false := by simpa using h0
  rcases hoor : (x87BindVal (FP87.Sin_Cos x) s.FP87_Control).2.2.2.1 with _ | _ <;>
  · unfold X86.Instructions.Operations.FSINCOS
    pspec_run_until [X86.UNSPECIFIED => unspecified1_run _,
      FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by decide)]
    x87_cond [h7']
    pspec_run_until [FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by decide)]
    x87_cond [h0']
    pspec_run_until [FP87.Sin_Cos => X87BindOk.run (by exact hok),
      X86.Helpers.Bit => partialSpecM_liftM_run_of_ok (bit_eq _) _]
    simp only [hoor, Bool.false_eq_true, ↓reduceIte]
    pspec_run [X86.UNSPECIFIED => unspecified1_run _,
      FP87.Is_Unmasked_Pre_Computation_Exception => isUnmaskedPre_masked _ _ (by exact hm),
      FP87.Process_Exceptions => processExceptions_run _ _ (by exact hm)]
    simp only [Int.reduceToNat, extractLsb'_zero_self, oracleSkip_oracleSkip, Bool.not_false,
      Bool.and_true, extractLsb'_setSlice_one_ne (n := 16) _ 9 10 _ (by decide) (by decide),
      extractLsb'_setSlice_one _ 10 _ (by decide : 10 < 16), ofValue_eq_mk]
    rfl

end X86Proofs
