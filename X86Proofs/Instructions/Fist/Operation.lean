import X86Proofs.Core.X87Mem
import X86Proofs.Core.X87Trans
import X86.Instructions.FIST

/-!
# FIST, FISTP specification

`FIST m16int`, `FIST m32int` and the popping forms (`FISTP`, also `m64int`): ST(0) rounded to a
signed integer by the rounding control and stored. lean-x86's `Operations.FIST x N`, with ST(0) =
`x` not empty and every exception masked: the integer `x87ToInt` (the integer indefinite if out of
range), and the status reported as a value (`x87ReportFsw`): C1 := whether it was rounded up, and the
conversion's exception flags but the denormal flag DE (`fistFlags`) ORed in. The form commits it
after the store (C0, C2, C3 from the oracle), which leaves `x87StoreStatus`
(`x87CommitFsw_store`).
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers X86.Runtime

/-- The exception flags FIST reports from its conversion's `ex`: those of `ex` but DE (bit 1). -/
def fistFlags (ex : BitVec 6) : BitVec 6 := setSlice ex 1 1 0

theorem fist_operation (s : RamState) (x : BitVec 80) (N : Nat) (hN : N = 16 ∨ N = 32 ∨ N = 64)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (hm : FcwMasked s.FP87_Control) (hok : X87ToIntOk (fcwRC s.FP87_Control) N x) :
    (X86.Instructions.Operations.FIST x N : SpecM X86.Exception RamState _).run s =
      (.ok ((x87ToInt (fcwRC s.FP87_Control) N x).1, true,
        x87ReportFsw s.FP87_Status
          (if (x87ToInt (fcwRC s.FP87_Control) N x).2.1 = true then 1 else 0)
          (fistFlags (x87ToInt (fcwRC s.FP87_Control) N x).2.2)), s) := by
  have h0' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3) = false := by simpa using h0
  rcases hN with rfl | rfl | rfl <;>
  · unfold X86.Instructions.Operations.FIST
    spec_run_until [MonadState.get => specM_get_run _,
      FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by decide)]
    x87_cond [h0']
    spec_bind_with (fp87ControlRC_run _)
    spec_bind_with (liftM_run_of_ok hok.eq _)
    simp only [setExceptionFlags_or]
    spec_bind_with (liftM_run_of_ok (bit_eq _) _)
    spec_run [FP87.Is_Unmasked_Pre_Computation_Exception => isUnmaskedPre_masked _ _ (by exact hm)]
    simp only [Int.reduceToNat, extractLsb'_zero_self]
    rfl

end X86Proofs
