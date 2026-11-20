import X86Proofs.Instructions.Movsx.Operation

/-!
# MOVSXD specification

`MOVSXD DEST, SRC` (`63 /r`): with REX.W, `DEST ← SignExtend(SRC)` for a doubleword source and a
64-bit register destination. Without REX.W the source has the operand size (32 or 16 bits) and the
instruction is a plain move (the SDM discourages this use). No flags are written.
`movsxdSpec n x` is the value at the destination's size `n`, `x.signExtend n` (the identity when
`x` already has `n` bits).
-/

namespace X86Proofs

/-- The result of `MOVSXD` to `n` bits: `x` sign-extended (a copy when `x` has `n` bits). No
flags, no oracle bits. -/
def movsxdSpec {m : Nat} (n : Nat) (x : BitVec m) : BitVec n := x.signExtend n

open X86 X86.Helpers

theorem movsxd_operation {σ : Type} (s : X86.State σ) (m n : Nat)
    (hmn : (n = 64 ∧ m = 32) ∨ (n = 32 ∧ m = 32) ∨ (n = 16 ∧ m = 16)) (x : BitVec m) :
    (liftM (X86.Instructions.Operations.MOVSX n m x) :
      X86.Runtime.SpecM X86.Exception (X86.State σ) (BitVec n)).run s =
        (.ok (movsxdSpec n x), s) := by
  rcases hmn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  exact movsx_operation s _ _ (by decide) (by decide) (by decide) x

end X86Proofs
