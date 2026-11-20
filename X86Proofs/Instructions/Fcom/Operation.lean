import X86Proofs.Core.X87Mem

/-!
# FCOM, FUCOM specification (register operands)

lean-x86's `Operations.FCOM x y j ordered` (FCOM: ordered; FUCOM: unordered, a quiet NaN raises
no invalid exception), with ST(0) and ST(`j`) not empty and every exception masked: C0, C2, C3 :=
the comparison of `x` with `y` (`x87Compare`), C1 := 0, its exception flags ORed into the status
word (`x87CmpFsw`). No condition code is left undefined.

With a memory operand (`FCOM m32fp`, `m64fp` and their popping forms), lean-x86's
`Operations.FCOM_Convert x y d`: ST(0) = `x` not empty, `y` the converted memory operand, `d`
whether it was a denormal: the ordered comparison with that denormal flag (`x87CompareD`) and the
same status word.
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers X86.Runtime

theorem fcom_operation (s : RamState) (x y : BitVec 80) (j : BitVec 3) (ordered : Bool)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (hj : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + j) ≠ 3)
    (hm : FcwMasked s.FP87_Control) (hok : X87CompareOk ordered x y) :
    (X86.Instructions.Operations.FCOM x y j ordered : SpecM X86.Exception RamState _).run s =
      (.ok true, { s with
        FP87_Status := x87CmpFsw s.FP87_Status (x87Compare ordered x y).1
          (x87Compare ordered x y).2 }) := by
  unfold X86.Instructions.Operations.FCOM
  spec_run_until []
  refine (specM_bind_run _ _ (isSTiEmpty_run _ 0 (by decide))).trans ?_
  spec_run_until []
  refine (specM_bind_run _ _ (isSTiEmpty_run _ _ (unsigned_range j rfl))).trans ?_
  have h0' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3) = false := by simpa using h0
  have hj' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + j) == 3) = false := by simpa using hj
  x87_cond [h0', hj']
  spec_run [liftM => liftM_run_of_ok hok.eq _,
    FP87.Is_Unmasked_Pre_Computation_Exception => isUnmaskedPre_masked _ _ (by exact hm),
    FP87.Process_Exceptions => processExceptions_run _ _ (by exact hm)]

theorem fcom_convert_operation (s : RamState) (x y : BitVec 80) (d : Bool)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (hm : FcwMasked s.FP87_Control) (hok : X87CompareDOk true d x y) :
    (X86.Instructions.Operations.FCOM_Convert x y d : SpecM X86.Exception RamState _).run s =
      (.ok true, { s with
        FP87_Status := x87CmpFsw s.FP87_Status (x87CompareD true d x y).1
          (x87CompareD true d x y).2 }) := by
  unfold X86.Instructions.Operations.FCOM_Convert
  spec_run_until []
  refine (specM_bind_run _ _ (isSTiEmpty_run _ 0 (by decide))).trans ?_
  have h0' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3) = false := by simpa using h0
  x87_cond [h0']
  spec_run [liftM => liftM_run_of_ok hok.eq _,
    FP87.Is_Unmasked_Pre_Computation_Exception => isUnmaskedPre_masked _ _ (by exact hm),
    FP87.Process_Exceptions => processExceptions_run _ _ (by exact hm)]

end X86Proofs
