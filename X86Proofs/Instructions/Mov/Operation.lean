import X86Proofs.Core.Run
import X86Proofs.Core.Flags

/-!
# MOV specification

MOV copies its source to its destination and sets no flags, so its specification is the
identity: the result is the source. It is here so that MOV's forms read like every other
operation's (`<op>Spec` and `<op>_operation`).
-/

namespace X86Proofs

/-- The result of `MOV x`: `x`. MOV changes no flags and uses no oracle bits. -/
def movSpec {n : Nat} (x : BitVec n) : BitVec n := x

open X86 X86.Helpers

theorem mov_operation_except (n : Nat) (x : BitVec n) :
    X86.Instructions.Operations.MOV n x = .ok (movSpec x) := by
  simp [X86.Instructions.Operations.MOV, x86_runtime, movSpec, bind, pure, Except.bind, Except.pure]

theorem mov_operation {σ : Type} (s : X86.State σ) (n : Nat) (x : BitVec n) :
    (liftM (X86.Instructions.Operations.MOV n x) :
      X86.Runtime.SpecM X86.Exception (X86.State σ) (BitVec n)).run s = (.ok (movSpec x), s) := by
  rw [mov_operation_except]
  rfl

end X86Proofs
