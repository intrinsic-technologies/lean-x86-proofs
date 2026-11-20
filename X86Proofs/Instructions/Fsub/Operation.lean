import X86Proofs.Core.X87Mem

/-!
# FSUB specification (register operands)

lean-x86's `Operations.FSUB x y i j mod`, with `x` = ST(`i`) and `y` = ST(`j`) not empty and every
exception masked: the result x − y (`x87Arith .sub`, lean-x86's `FP87.Subtract` at the control word)
and the status word `x87OpStatus` (C0, C2, C3 from the oracle, C1 := rounded up, the flags).

With a memory operand (`FSUB m32fp`, `m64fp`), lean-x86's `Operations.FSUB_Convert x y d`: `y` is
the converted memory operand, `d` whether it was a denormal, ST(0) = `x` not empty: the result
x − y with that denormal flag (`x87ArithD`) and the same status word.
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers X86.Runtime

theorem fsub_operation (s : RamState) (x y : BitVec 80) (i j : BitVec 3) (mod : BitVec 2)
    (hi : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + i) ≠ 3)
    (hj : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + j) ≠ 3)
    (hm : FcwMasked s.FP87_Control) (hok : X87ArithOk .sub s.FP87_Control x y) :
    (X86.Instructions.Operations.FSUB x y i j mod : SpecM X86.Exception RamState _).run s =
      (.ok ((x87Arith .sub s.FP87_Control x y).1, x87OpStatus s.FP87_Status s.oracle
        (x87Arith .sub s.FP87_Control x y).2.1 (x87Arith .sub s.FP87_Control x y).2.2),
        { s with oracle := oracleSkip s.oracle 3 }) := by
  unfold X86.Instructions.Operations.FSUB
  spec_run_until [MonadState.get => specM_get_run _, X86.UNSPECIFIED => unspecified1_run _,
    FP87.Is_STi_Empty => isSTiEmpty_run _ _ (unsigned_range _ rfl)]
  have hi' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + i) == 3) = false := by simpa using hi
  have hj' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + j) == 3) = false := by simpa using hj
  x87_cond [hi', hj']
  spec_run_until [FP87.Subtract => x87OpM_run .sub x y _ (by exact hm) (by exact hok)]
  simp only [Int.reduceToNat, extractLsb'_zero_self, oracleSkip_oracleSkip]
  rfl

theorem fsub_convert_operation (s : RamState) (x y : BitVec 80) (d : Bool)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (hm : FcwMasked s.FP87_Control) (hok : X87ArithDOk .sub s.FP87_Control false d x y) :
    (X86.Instructions.Operations.FSUB_Convert x y d : SpecM X86.Exception RamState _).run s =
      (.ok ((x87ArithD .sub s.FP87_Control false d x y).1, x87OpStatus s.FP87_Status s.oracle
        (x87ArithD .sub s.FP87_Control false d x y).2.1
        (x87ArithD .sub s.FP87_Control false d x y).2.2),
        { s with oracle := oracleSkip s.oracle 3 }) := by
  unfold X86.Instructions.Operations.FSUB_Convert
  spec_run_until [MonadState.get => specM_get_run _, X86.UNSPECIFIED => unspecified1_run _,
    FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by decide)]
  have h0' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3) = false := by simpa using h0
  x87_cond [h0']
  spec_run_until [FP87.Subtract => x87OpMD_run .sub false d _ _ _ (by exact hm) (by exact hok)]
  simp only [Int.reduceToNat, extractLsb'_zero_self, oracleSkip_oracleSkip]
  rfl

end X86Proofs
