import X86Proofs.Core.Flags
import X86Proofs.Program.ComposeAttr

/-!
# CLC specification

`CLC` (`F8`): `CF ← 0`. The OF, ZF, SF, AF and PF flags are unaffected (Intel SDM). `clcSpec f` is
the status flags after CLC, from the flags `f` before it.
-/

namespace X86Proofs

/-- The flags after CLC: CF cleared, every other flag as in `f`. -/
def clcSpec (f : StatusFlags) : StatusFlags := { f with CF := false }

open X86

theorem clc_operation {σ : Type} (s : X86.State σ) :
    (X86.Instructions.Operations.CLC : Runtime.SpecM Exception (X86.State σ) Unit).run s =
      (.ok (), setFlags s (clcSpec (StatusFlags.ofRFLAGS s.RFLAGS))) := by
  unfold X86.Instructions.Operations.CLC
  rw [rflagsSetCF_run, setFlags, clcSpec, StatusFlags.store_setCF]
  rfl

attribute [x86_compose] clcSpec

end X86Proofs
