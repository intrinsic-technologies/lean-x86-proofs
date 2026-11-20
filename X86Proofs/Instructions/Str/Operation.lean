import X86Proofs.Core.Run
import X86

/-!
# STR specification

`STR r/m` (`0F 00 /1`, Intel SDM): `DEST ← TR(SegmentSelector)`. A register destination gets the
selector zero-extended to the operand size; a memory destination is always 16 bits. No flags.
`strSpec n sel` is the value at size `n`.
-/

namespace X86Proofs

/-- The value `STR` writes at operand size `n`: the task-register selector `sel` zero-extended. -/
def strSpec (n : Nat) (sel : BitVec 16) : BitVec n := sel.setWidth n

open X86 X86.Helpers

theorem str_operation {σ : Type} (s : X86.State σ) (n : Nat) (hn : n = 64 ∨ n = 32 ∨ n = 16) :
    (X86.Instructions.Operations.STR n).run s = (.ok (strSpec n s.TR.selector), s) := by
  rcases hn with rfl | rfl | rfl <;>
  simp [X86.Instructions.Operations.STR, x86_runtime, strSpec, bind, pure, get, getThe,
    MonadStateOf.get, ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.pure, ExceptT.lift,
    StateT.bind, StateT.pure, liftM, monadLift, MonadLift.monadLift] <;> rfl

end X86Proofs
