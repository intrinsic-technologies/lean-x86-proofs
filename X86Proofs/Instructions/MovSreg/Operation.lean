import X86Proofs.Core.Run
import X86

/-!
# MOV from a segment register

`MOV r/m, Sreg` (`8C /r`, Intel SDM): `DEST ← SegmentRegister`. With a register destination the
selector is zero-extended to the operand size (lean-x86's `MOV_from_SEG`; at 16 bits the bits above
are kept, as every 16-bit register write); with a memory destination the 16-bit selector is stored
whatever the operand size. No flags are written. `movsregSpec n sel` is the value at the
destination's size `n`.
-/

namespace X86Proofs

/-- The value `MOV r/m, Sreg` writes at operand size `n`: the selector `sel` zero-extended. -/
def movsregSpec (n : Nat) (sel : BitVec 16) : BitVec n := sel.setWidth n

open X86 X86.Helpers

theorem movsreg_operation {σ : Type} (s : X86.State σ) (n : Nat) (hn : n = 64 ∨ n = 32 ∨ n = 16)
    (sel : BitVec 16) :
    (liftM (X86.Instructions.Operations.MOV_from_SEG n sel) :
      X86.Runtime.SpecM X86.Exception (X86.State σ) (BitVec n)).run s =
        (.ok (movsregSpec n sel), s) := by
  rcases hn with rfl | rfl | rfl <;>
  simp [X86.Instructions.Operations.MOV_from_SEG, x86_runtime, movsregSpec, bind, pure,
    Except.bind, Except.pure] <;> rfl

end X86Proofs
