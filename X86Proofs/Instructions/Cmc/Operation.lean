import X86Proofs.Core.Flags
import X86Proofs.Core.Run
import X86Proofs.Program.ComposeAttr

/-!
# CMC specification

`CMC` (`F5`): `CF ← NOT CF`. The OF, ZF, SF, AF and PF flags are unaffected (Intel SDM).
`cmcSpec f` is the status flags after CMC, from the flags `f` before it.
-/

namespace X86Proofs

/-- The flags after CMC: CF complemented, every other flag as in `f`. -/
def cmcSpec (f : StatusFlags) : StatusFlags := { f with CF := !f.CF }

open X86

theorem cmc_operation {σ : Type} (s : X86.State σ) :
    (X86.Instructions.Operations.CMC : Runtime.SpecM Exception (X86.State σ) Unit).run s =
      (.ok (), setFlags s (cmcSpec (StatusFlags.ofRFLAGS s.RFLAGS))) := by
  unfold X86.Instructions.Operations.CMC
  refine (specM_bind_run _ _ (rflagsCF_run s)).trans ?_
  rw [rflagsSetCF_run, setFlags, cmcSpec, StatusFlags.store_setCF]
  cases (StatusFlags.ofRFLAGS s.RFLAGS).CF <;> rfl

attribute [x86_compose] cmcSpec

end X86Proofs
