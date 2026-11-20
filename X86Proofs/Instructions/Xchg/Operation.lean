import X86Proofs.Core.Run
import X86

/-!
# XCHG specification

`XCHG DEST, SRC` (Intel SDM): `TEMP ← DEST; DEST ← SRC; SRC ← TEMP`. The two operands swap their
values; no flags are written. `xchgSpec x y` is the new values of the two operands, `(y, x)`.
-/

namespace X86Proofs

/-- The values `XCHG` leaves in its two operands, first `x`'s then `y`'s: swapped. No flags, no
oracle bits. -/
def xchgSpec {n : Nat} (x y : BitVec n) : BitVec n × BitVec n := (y, x)

open X86 X86.Helpers

theorem xchg_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x y : BitVec n) :
    (liftM (X86.Instructions.Operations.XCHG n x y) :
      X86.Runtime.SpecM X86.Exception (X86.State σ) (BitVec n × BitVec n)).run s =
        (.ok (xchgSpec x y), s) := by
  rcases hn with rfl | rfl | rfl | rfl <;>
  simp [X86.Instructions.Operations.XCHG, x86_runtime, xchgSpec, bind, pure, Except.bind,
    Except.pure] <;> rfl

end X86Proofs
