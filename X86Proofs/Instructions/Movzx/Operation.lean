import X86Proofs.Core.Run
import X86

/-!
# MOVZX specification

`MOVZX DEST, SRC` (`0F B6 /r`: a byte source; `0F B7 /r`: a word source):
`DEST ← ZeroExtend(SRC)`. The destination is a 16-, 32- or 64-bit register; the bits above the
source are zero. No flags are written. `movzxSpec n x` is the value at the destination's size
`n`, `x.setWidth n`.
-/

namespace X86Proofs

/-- The result of `MOVZX` to `n` bits: `x` zero-extended. No flags, no oracle bits. -/
def movzxSpec {m : Nat} (n : Nat) (x : BitVec m) : BitVec n := x.setWidth n

open X86 X86.Helpers

theorem movzx_operation_except (n : Nat) (hn : n = 64 ∨ n = 32) (x : BitVec 8) :
    X86.Instructions.Operations.MOVZX 8 n x = .ok (movzxSpec n x) := by
  rcases hn with rfl | rfl <;>
  simp [X86.Instructions.Operations.MOVZX, x86_runtime, movzxSpec, bind, pure, Except.bind,
    Except.pure]

theorem movzx_operation {σ : Type} (s : X86.State σ) (n : Nat) (hn : n = 64 ∨ n = 32)
    (x : BitVec 8) :
    (liftM (X86.Instructions.Operations.MOVZX 8 n x) :
      X86.Runtime.SpecM X86.Exception (X86.State σ) (BitVec n)).run s =
        (.ok (movzxSpec n x), s) := by
  rw [movzx_operation_except n hn]
  rfl

theorem movzx_operation_of_sizes {σ : Type} (s : X86.State σ) (m n : Nat) (hm : m = 8 ∨ m = 16)
    (hn : n = 64 ∨ n = 32 ∨ n = 16) (x : BitVec m) :
    (liftM (X86.Instructions.Operations.MOVZX m n x) :
      X86.Runtime.SpecM X86.Exception (X86.State σ) (BitVec n)).run s =
        (.ok (movzxSpec n x), s) := by
  rcases hm with rfl | rfl <;> rcases hn with rfl | rfl | rfl <;>
  simp [X86.Instructions.Operations.MOVZX, x86_runtime, movzxSpec, bind, pure, Except.bind,
    Except.pure] <;> rfl

end X86Proofs
