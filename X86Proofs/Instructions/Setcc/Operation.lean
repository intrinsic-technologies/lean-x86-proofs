import X86Proofs.Instructions.Branch.Cond

/-!
# SETcc specification

`SETcc r/m8`: `IF condition THEN DEST ← 1; ELSE DEST ← 0; FI`. The condition `cc` is the low four
bits of the opcode (`0F 90+cc`), evaluated on the status flags as for `Jcc` (`condHolds`). The
destination is one byte (a register's low byte, or a byte of memory, written without being read);
the flags are not written.
-/

namespace X86Proofs

/-- The byte SETcc writes: 1 if the condition holds, else 0. -/
def setccSpec (c : Bool) : BitVec 8 :=
  if c then 1 else 0

open X86 X86.Helpers

theorem setcc_operation {σ : Type} (s : X86.State σ) (cc : BitVec 4) :
    (X86.Instructions.Operations.SETcc cc).run s =
      (.ok (setccSpec (condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS))), s) := by
  unfold X86.Instructions.Operations.SETcc
  refine (specM_bind_run _ _ (conditionHolds_run s cc)).trans ?_
  cases condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) <;> rfl

end X86Proofs
