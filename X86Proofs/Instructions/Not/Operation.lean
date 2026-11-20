import X86Proofs.Core.Run
import X86Proofs.Core.Flags

/-!
# NOT specification

A pure function: no state, no failure, no oracle. NOT writes no flags, so unlike the other
one-operand specs (`incSpec`, `decSpec`) it takes no flags and returns only the result.
-/

namespace X86Proofs

/-- The result of NOT: `~~~x`. -/
def notSpec {n : Nat} (x : BitVec n) : BitVec n :=
  ~~~x

open X86 X86.Helpers

theorem not_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x : BitVec n) :
    (liftM (X86.Instructions.Operations.NOT n x) :
        X86.Runtime.SpecM X86.Exception (X86.State σ) (X86.Runtime.Bits n)).run s =
      (.ok (notSpec x), s) := by
  rcases hn with rfl | rfl | rfl | rfl <;> rfl

end X86Proofs
