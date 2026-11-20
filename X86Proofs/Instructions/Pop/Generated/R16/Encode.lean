import X86Proofs.Instructions.Pop.Decode
import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodePopR16 (r : BitVec 4) : List UInt8 :=
  if r.toNat < 8 then [0x66, UInt8.ofNat (0x58 + r.toNat)]
  else [0x66, 0x41, UInt8.ofNat (0x58 + r.toNat % 8)]

theorem encodePopR16_spec (r : BitVec 4) :
    (∃ op, encodePopR16 r = [0x66, op] ∧ PopOpcode op ∧
      gprNumber 0 0 (opcodeReg op) = r.setWidth 5) ∨
    (∃ rex op, encodePopR16 r = [0x66, rex, op] ∧ RexNoWPrefix rex.toBitVec ∧ PopOpcode op ∧
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
