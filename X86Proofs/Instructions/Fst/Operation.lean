import X86Proofs.Core.X87Mem
import X86Proofs.Core.X87Trans

/-!
# FST and FSTP specification (register destination)

`FST ST(i)`: ST(i) := ST(0); `FSTP ST(i)` then pops the stack (ST(0) tagged empty, TOP := TOP + 1).
lean-x86's `Operations.FST` reports the status as a value and leaves the state alone (C1 := 0;
with ST(0) not empty there is no exception and the value is stored unchanged); the form commits
it after the write (`x87CommitFsw`, C0, C2, C3 from the oracle), which leaves `fstStatus`
(`x87CommitFsw_fst`).

`FST m32fp`, `FST m64fp` and their popping forms (`Operations.FST_Convert x N`): ST(0) = `x` not
empty, rounded to a single or double at the control word (`x87ToFloat`); the status reported has
C1 := whether it was rounded up and its exception flags ORed in, and committing it leaves
`x87StoreStatus` (`x87CommitFsw_store`).
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers X86.Runtime

/-- The status word an FST form leaves: C1 := 0, C0, C2, C3 from the oracle, no exception
flag. -/
def fstStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) : BitVec 16 :=
  fswOrFlags (fswC1Zero fsw o) 0

@[simp] theorem fswTop_fstStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswTop (fstStatus fsw o) = fswTop fsw := by
  simp [fstStatus]

@[simp] theorem fswES_fstStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswES (fstStatus fsw o) = fswES fsw := by
  simp [fstStatus]

theorem fswRest_fstStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswRest (fstStatus fsw o) = fswRest fsw := by
  simp [fstStatus]

theorem fswCC_fstStatus_c1 (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswCC (fstStatus fsw o) &&& 2 = 0 := by
  simp only [fstStatus, fswCC_fswOrFlags]
  exact fswCC_fswC1Zero fsw o

/-- Committing FST's report (C1 := 0, no exception flag) leaves `fstStatus`. -/
theorem x87CommitFsw_fst (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    x87CommitFsw fsw (x87ReportFsw fsw 0 0) o = fstStatus fsw o := by
  simp only [x87CommitFsw_eq, fstStatus, fswC1Zero, x87ReportFsw, fswSetC1]
  fsw_bits
  all_goals simp [getElem_setSlice]

theorem fst_operation {σ : Type} (s : X86.State σ) (src : BitVec 80)
    (hsrc : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (hm : FcwMasked s.FP87_Control) :
    (X86.Instructions.Operations.FST src : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (src, true, x87ReportFsw s.FP87_Status 0 0), s) := by
  unfold X86.Instructions.Operations.FST
  spec_run_until [MonadState.get => specM_get_run _,
    FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by decide)]
  have hsrc' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3) = false := by
    simpa using hsrc
  x87_cond [hsrc']
  simp only [setExceptionFlags_or]
  spec_run [FP87.Is_Unmasked_Pre_Computation_Exception => isUnmaskedPre_masked _ _ (by exact hm)]

theorem fst_convert_operation (s : RamState) (x : BitVec 80) (N : Nat) (hN : N = 32 ∨ N = 64)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (hm : FcwMasked s.FP87_Control) (hok : X87ToFloatOk N s.FP87_Control x) :
    (X86.Instructions.Operations.FST_Convert x N : SpecM X86.Exception RamState _).run s =
      (.ok ((x87ToFloat N s.FP87_Control x).1, true,
        x87ReportFsw s.FP87_Status (if (x87ToFloat N s.FP87_Control x).2.1 = true then 1 else 0)
          (x87ToFloat N s.FP87_Control x).2.2), s) := by
  have h0' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3) = false := by simpa using h0
  rcases hN with rfl | rfl <;>
  · unfold X86.Instructions.Operations.FST_Convert
    spec_run_until [MonadState.get => specM_get_run _,
      FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by decide)]
    x87_cond [h0']
    spec_bind_with (convertToFloat_run _ (by decide) x _ (by exact hm) (by exact hok))
    simp only [setExceptionFlags_or]
    spec_bind_with (fp87ControlUM_run_masked _ (by exact hm))
    spec_bind_with (fp87ControlOM_run_masked _ (by exact hm))
    simp only [show ((1#1 : BitVec 1) == 0) = false from rfl, Bool.and_false, Bool.or_false,
      Bool.false_eq_true, ite_false]
    spec_bind_with (liftM_run_of_ok (bit_eq _) _)
    spec_run [FP87_Control.Exception_Masks => fp87ControlMasks_run _,
      liftM => liftM_run_of_ok (isUnmaskedException_fcwMasked _ hm) _]
    simp only [Int.reduceToNat, extractLsb'_zero_self]
    rfl

end X86Proofs
