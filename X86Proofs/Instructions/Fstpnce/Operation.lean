import X86Proofs.Core.X87

/-!
# FSTPNCE specification

`FSTPNCE ST(i)` (`D9 D8+i`, an undocumented alias of FSTP): ST(i) := ST(0), then pop. lean-x86's
`Operations.FSTPNCE` reads ST(0) and reports the status with C1 := 0 as a value, leaving the state
alone; with ST(0) not empty it raises no exception. The form commits the status (`x87CommitFsw`),
which leaves `fswC1Zero` (`x87CommitFsw_c1Zero`).
-/

namespace X86Proofs

open X86 X86.Helpers X86.Runtime

theorem fstpnce_operation {σ : Type} (s : X86.State σ)
    (hsrc : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3) :
    (X86.Instructions.Operations.FSTPNCE : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (fswSetC1 s.FP87_Status 0, s.FP87[fprIndex (fswTop s.FP87_Status)], true), s) := by
  unfold X86.Instructions.Operations.FSTPNCE
  spec_run_until [MonadState.get => specM_get_run _,
    FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by decide)]
  have hsrc' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3) = false := by
    simpa using hsrc
  x87_cond [hsrc']
  spec_run [X86.Helpers.ST => st_run _ _ 0 rfl (by simpa only [add_zero3'] using hsrc)]
  simp only [add_zero3']
  rfl

end X86Proofs
