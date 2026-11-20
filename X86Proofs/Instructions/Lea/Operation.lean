import X86Proofs.Core.Run
import X86

/-!
# LEA specification

`LEA DEST, SRC` (`8D /r`): `DEST ← EffectiveAddress(SRC)`, truncated to the operand size. With
address size 64 the address is computed in 64 bits; at operand size 32 or 16 its low 32 or 16
bits are the result (the SDM's table for operand size < address size). No memory is accessed and
no flags are written. `leaSpec n a` is that result, `a.setWidth n`.
-/

namespace X86Proofs

/-- The result of `LEA` at operand size `n` for the effective address `a`: its low `n` bits. -/
def leaSpec (n : Nat) (a : BitVec 64) : BitVec n := a.setWidth n

open X86 X86.Helpers

theorem lea_operation_except (n : Nat) (hn : n = 64 ∨ n = 32 ∨ n = 16) (a : BitVec 64) :
    X86.Instructions.Operations.LEA n a = .ok (leaSpec n a) := by
  rcases hn with rfl | rfl | rfl <;>
  simp [X86.Instructions.Operations.LEA, x86_runtime, leaSpec, bind, pure, Except.bind,
    Except.pure, X86.Runtime.CheckedSlice.read, ← BitVec.setWidth_eq_extractLsb']

theorem lea_operation {σ : Type} (s : X86.State σ) (n : Nat) (hn : n = 64 ∨ n = 32 ∨ n = 16)
    (a : BitVec 64) :
    (liftM (X86.Instructions.Operations.LEA n a) :
      X86.Runtime.SpecM X86.Exception (X86.State σ) (BitVec n)).run s =
        (.ok (leaSpec n a), s) := by
  rw [lea_operation_except n hn]
  rfl

end X86Proofs
