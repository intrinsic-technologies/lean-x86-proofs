import X86Proofs.Core.X87Arith

/-!
# FXTRACT specification

lean-x86's `Operations.FXTRACT x`, with ST(0) not empty and ST(7) empty (the push does not
overflow): the significand and the exponent of `x` (`x87Extract`, lean-x86's `FP87.Extract`) and
the status word `x87ExtractStatus` (C0, C2, C3 from the oracle, C1 := 0, the flags).
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers X86.Runtime

theorem fxtract_operation (s : RamState) (x : BitVec 80)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (h7 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 7) = 3) (hok : X87ExtractOk x) :
    (X86.Instructions.Operations.FXTRACT x : PartialSpecM X86.Exception RamState _).run s =
      some (.ok ((x87Extract x).1, (x87Extract x).2.1,
        x87ExtractStatus s.FP87_Status s.oracle (x87Extract x).2.2),
        { s with oracle := oracleSkip s.oracle 3 }) := by
  unfold X86.Instructions.Operations.FXTRACT
  pspec_run [X86.UNSPECIFIED => unspecified1_run _,
    FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by decide)]
  have h0' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3) = false := by simpa using h0
  have h7' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 7) == 3) = true := by simpa using h7
  x87_cond [h0']
  pspec_run [FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by decide)]
  x87_cond [h7']
  pspec_run [FP87.Extract => partialResult_lift_run (fp87Extract_eq hok) _]
  simp only [Int.reduceToNat, extractLsb'_zero_self, oracleSkip_oracleSkip]
  rfl

end X86Proofs
