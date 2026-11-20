import X86Proofs.Core.Run
import X86

/-!
# SLDT specification

`SLDT r/m` (`0F 00 /0`, Intel SDM): `DEST ← LDTR(SegmentSelector)`. A register destination gets the
selector zero-extended to the operand size; a memory destination is always 16 bits. No flags.
`sldtSpec n sel` is the value at size `n`.
-/

namespace X86Proofs

/-- The value `SLDT` writes at operand size `n`: the LDTR selector `sel` zero-extended. -/
def sldtSpec (n : Nat) (sel : BitVec 16) : BitVec n := sel.setWidth n

open X86 X86.Helpers

theorem sldt_operation {σ : Type} (s : X86.State σ) (n : Nat) (hn : n = 64 ∨ n = 32 ∨ n = 16) :
    (X86.Instructions.Operations.SLDT n).run s = (.ok (sldtSpec n s.LDTR.selector), s) := by
  rcases hn with rfl | rfl | rfl <;>
  simp [X86.Instructions.Operations.SLDT, x86_runtime, sldtSpec, bind, pure, get, getThe,
    MonadStateOf.get, ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.pure, ExceptT.lift,
    StateT.bind, StateT.pure, liftM, monadLift, MonadLift.monadLift] <;> rfl

end X86Proofs
