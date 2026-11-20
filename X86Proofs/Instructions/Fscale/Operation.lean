import X86Proofs.Core.X87Trans

/-!
# FSCALE specification

lean-x86's `Operations.FSCALE x y` (`x` = ST(0), `y` = ST(1)), with both not empty and every
exception masked: ST(0) scaled by 2 to the integer part of ST(1) (`FP87.Scale`) and the status
word `x87OpStatus` (C0, C2, C3 from the oracle, C1 := rounded up, the flags). `FP87.Scale` is
lean-x86's own code, not a binding, and total (`FP87.Scale_Number` does not
loop), so `Operations.FSCALE` is a `SpecM`. The library still states it as the transcendentals
are stated, on its lift (`liftTotal`): its value at the control word (`x87BindVal`), its
independence of the rest of the state assumed (`X87BindOk`) rather than proved.
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers X86.Runtime

theorem fscale_operation [Bindings] (s : RamState) (x y : BitVec 80)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (h1 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 1) ≠ 3)
    (hm : FcwMasked s.FP87_Control)
    (hok : X87BindOk (liftTotal (FP87.Scale x y)) s.FP87_Control) :
    (X86.Instructions.Operations.FSCALE x y : SpecM X86.Exception RamState _).run s =
      (.ok ((x87BindVal (liftTotal (FP87.Scale x y)) s.FP87_Control).1,
        x87OpStatus s.FP87_Status s.oracle
          (x87BindVal (liftTotal (FP87.Scale x y)) s.FP87_Control).2.1
          (x87BindVal (liftTotal (FP87.Scale x y)) s.FP87_Control).2.2),
        { s with oracle := oracleSkip s.oracle 3 }) := by
  unfold X86.Instructions.Operations.FSCALE
  spec_run_until [MonadState.get => specM_get_run _, X86.UNSPECIFIED => unspecified1_run _,
    FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by decide)]
  have h0' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3) = false := by simpa using h0
  have h1' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 1) == 3) = false := by simpa using h1
  x87_cond [h0', h1', show BitVec.ofInt 3 1 = 1 from rfl]
  spec_run [FP87.Scale => X87BindOk.run_total (by exact hok),
    FP87.Is_Unmasked_Pre_Computation_Exception => isUnmaskedPre_masked _ _ (by exact hm)]
  simp only [Int.reduceToNat, extractLsb'_zero_self, oracleSkip_oracleSkip, Bool.not_false,
    Bool.and_true]
  rfl

end X86Proofs
