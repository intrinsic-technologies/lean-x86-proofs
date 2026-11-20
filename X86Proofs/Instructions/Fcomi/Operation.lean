import X86Proofs.Core.X87Arith

/-!
# FCOMI, FUCOMI specification

lean-x86's `Operations.FCOMI x y j ordered` (FCOMI: ordered; FUCOMI: unordered), with ST(0) and
ST(`j`) not empty and every exception masked: ZF, PF, CF := the comparison of `x` with `y`
(`x87Compare`, as COMISS sets them: `fpCompareFlags`), OF, SF, AF := 0, C1 := 0 and the exception
flags ORed into the status word (`x87ComiFsw`). C0, C2, C3 are kept.
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers X86.Runtime

theorem fcomi_operation (s : RamState) (x y : BitVec 80) (j : BitVec 3) (ordered : Bool)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (hj : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + j) ≠ 3)
    (hm : FcwMasked s.FP87_Control) (hok : X87CompareOk ordered x y) :
    (X86.Instructions.Operations.FCOMI x y j ordered : SpecM X86.Exception RamState _).run s =
      (.ok true, { s with
        FP87_Status := x87ComiFsw s.FP87_Status (x87Compare ordered x y).2
        RFLAGS := (fpCompareFlags (x87Compare ordered x y).1).store s.RFLAGS }) := by
  unfold X86.Instructions.Operations.FCOMI
  spec_run_until []
  refine (specM_bind_run _ _ (isSTiEmpty_run _ 0 (by decide))).trans ?_
  spec_run_until []
  refine (specM_bind_run _ _ (isSTiEmpty_run _ _ (unsigned_range j rfl))).trans ?_
  have h0' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3) = false := by simpa using h0
  have hj' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + j) == 3) = false := by simpa using hj
  x87_cond [h0', hj']
  spec_run_until [liftM => liftM_run_of_ok hok.eq _]
  x87_cond [fcwMasked_im hm, Int.reduceToNat, show ((1#1 : BitVec 1) == 1) = true from rfl]
  spec_run [FP87.Is_Unmasked_Pre_Computation_Exception => isUnmaskedPre_masked _ _ (by exact hm),
    FP87.Process_Exceptions => processExceptions_run _ _ (by exact hm)]
  have hr : (fpCompareFlags (x87Compare ordered x y).1).store s.RFLAGS =
      setSlice (setSlice (setSlice (setSlice (setSlice (setSlice s.RFLAGS 11 1 0) 7 1 0) 4 1 0) 6 1
        ((x87Compare ordered x y).1.extractLsb' 2 1)) 2 1
        ((x87Compare ordered x y).1.extractLsb' 1 1)) 0 1
        ((x87Compare ordered x y).1.extractLsb' 0 1) := by
    unfold fpCompareFlags
    rflags_ext
  rw [hr]
  rfl

end X86Proofs
