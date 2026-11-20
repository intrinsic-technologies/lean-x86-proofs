import X86Proofs.Core.Run
import X86

/-!
# MOVSX specification

`MOVSX DEST, SRC` (`0F BE /r`: a byte source; `0F BF /r`: a word source):
`DEST ← SignExtend(SRC)`. The destination is a 16-, 32- or 64-bit register; the bits above the
source are copies of its sign bit. No flags are written. `movsxSpec n x` is the value at the
destination's size `n`, `x.signExtend n`.
-/

namespace X86Proofs

/-- The result of `MOVSX` to `n` bits: `x` sign-extended. No flags, no oracle bits. -/
def movsxSpec {m : Nat} (n : Nat) (x : BitVec m) : BitVec n := x.signExtend n

open X86 X86.Helpers

theorem movsx_operation {σ : Type} (s : X86.State σ) (m n : Nat) (hm : m = 8 ∨ m = 16 ∨ m = 32)
    (hn : n = 64 ∨ n = 32 ∨ n = 16) (hmn : m ≤ n) (x : BitVec m) :
    (liftM (X86.Instructions.Operations.MOVSX n m x) :
      X86.Runtime.SpecM X86.Exception (X86.State σ) (BitVec n)).run s =
        (.ok (movsxSpec n x), s) := by
  rcases hm with rfl | rfl | rfl <;> rcases hn with rfl | rfl | rfl <;>
  first
  | exact absurd hmn (by decide)
  | simp [X86.Instructions.Operations.MOVSX, x86_runtime, movsxSpec, bind, pure, Except.bind,
      Except.pure] <;> rfl

end X86Proofs
