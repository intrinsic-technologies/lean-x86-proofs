import X86Proofs.Core.Flags
import X86Proofs.Program.ComposeAttr

/-!
# STC specification

`STC` (`F9`): `CF ← 1`. The OF, ZF, SF, AF and PF flags are unaffected (Intel SDM). `stcSpec f` is
the status flags after STC, from the flags `f` before it.
-/

namespace X86Proofs

/-- The flags after STC: CF set, every other flag as in `f`. -/
def stcSpec (f : StatusFlags) : StatusFlags := { f with CF := true }

open X86

theorem stc_operation {σ : Type} (s : X86.State σ) :
    (X86.Instructions.Operations.STC : Runtime.SpecM Exception (X86.State σ) Unit).run s =
      (.ok (), setFlags s (stcSpec (StatusFlags.ofRFLAGS s.RFLAGS))) := by
  unfold X86.Instructions.Operations.STC
  rw [rflagsSetCF_run, setFlags, stcSpec, StatusFlags.store_setCF]
  rfl

attribute [x86_compose] stcSpec

end X86Proofs
