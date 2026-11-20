import X86Proofs.Instructions.Branch.Cond

/-!
# CMOVcc specification

`CMOVcc DEST, SRC`: `IF condition TRUE THEN DEST ← SRC FI` (`temp ← SRC` first, so a memory source
is read, and may fault, whatever the condition). The condition `cc` is the low four bits of the
opcode (`0F 40+cc`), evaluated on the status flags as for `Jcc` (`condHolds`). The flags are not
written.

At 32 bits the SDM zero-extends the destination even when the condition is false; lean-x86 writes
the destination register at the operand size in both cases (`Write_GPR` of the source or of the
destination's own value), so its upper half is cleared either way. `cmovSpec c dst src` is the
value written at the operand size.
-/

namespace X86Proofs

/-- The value CMOVcc writes at the operand size: the source if the condition holds, else the
destination's old value. -/
def cmovSpec {n : Nat} (c : Bool) (dst src : BitVec n) : BitVec n :=
  if c then src else dst

open X86 X86.Helpers

theorem cmov_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (a b : BitVec n) (cc : BitVec 4) :
    (X86.Instructions.Operations.CMOVcc n a b cc).run s =
      (.ok (cmovSpec (condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS)) a b), s) := by
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.CMOVcc
    spec_bind_rfl
    refine (specM_bind_run _ _ (conditionHolds_run s cc)).trans ?_
    cases condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) <;> rfl

end X86Proofs
