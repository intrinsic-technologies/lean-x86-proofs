import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr
import X86Proofs.Instructions.Mov.Decode

namespace X86Proofs

def encodeMovR16Imm16 (dst : BitVec 4) (imm : BitVec 16) : List UInt8 :=
  if dst.toNat < 8 then 0x66 :: UInt8.ofNat (0xB8 + dst.toNat) :: immBytes 16 imm
  else 0x66 :: UInt8.ofNat (0x40 + dst.toNat / 8) :: UInt8.ofNat (0xB8 + dst.toNat % 8) ::
    immBytes 16 imm

theorem encodeMovR16Imm16_spec (dst : BitVec 4) (imm : BitVec 16) :
    (∃ op, encodeMovR16Imm16 dst imm = 0x66 :: op :: immBytes 16 imm ∧ MovImmOpcode op ∧
      gprNumber 0 0 (opcodeReg op) = dst.setWidth 5) ∨
    (∃ rex op, encodeMovR16Imm16 dst imm = 0x66 :: rex :: op :: immBytes 16 imm ∧
      RexNoWPrefix rex.toBitVec ∧ MovImmOpcode op ∧
      gprNumber 0 (rexB rex.toBitVec) (opcodeReg op) = dst.setWidth 5) := by
  by_cases hlow : dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst
    decide

end X86Proofs
