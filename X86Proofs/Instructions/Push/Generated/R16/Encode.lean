import X86Proofs.Instructions.Push.Decode
import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodePushR16 (r : BitVec 4) : List UInt8 :=
  if r.toNat < 8 then [0x66, UInt8.ofNat (0x50 + r.toNat)]
  else [0x66, 0x41, UInt8.ofNat (0x50 + r.toNat % 8)]

theorem encodePushR16_spec (r : BitVec 4) :
    (∃ op, encodePushR16 r = [0x66, op] ∧ PushOpcode op ∧
      gprNumber 0 0 (opcodeReg op) = r.setWidth 5) ∨
    (∃ rex op, encodePushR16 r = [0x66, rex, op] ∧ RexNoWPrefix rex.toBitVec ∧ PushOpcode op ∧
      gprNumber 0 (rexB rex.toBitVec) (opcodeReg op) = r.setWidth 5) := by
  by_cases hlow : r.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert r
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert r
    decide

end X86Proofs
