import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr
import X86Proofs.Instructions.Mov.Decode

namespace X86Proofs

def encodeMovR8Imm8 (dst : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  if dst.toNat < 4 then UInt8.ofNat (0xB0 + dst.toNat) :: immBytes 8 imm
  else UInt8.ofNat (0x40 + dst.toNat / 8) :: UInt8.ofNat (0xB0 + dst.toNat % 8) ::
    immBytes 8 imm

theorem encodeMovR8Imm8_spec (dst : BitVec 4) (imm : BitVec 8) :
    (∃ op, encodeMovR8Imm8 dst imm = op :: immBytes 8 imm ∧ op ∈ [0xB0, 0xB1, 0xB2, 0xB3] ∧
      gprNumber 0 0 (opcodeReg op) = dst.setWidth 5) ∨
    (∃ rex op, encodeMovR8Imm8 dst imm = rex :: op :: immBytes 8 imm ∧
      RexPrefix rex.toBitVec ∧ op ∈ [0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7] ∧
      gprNumber 0 (rexB rex.toBitVec) (opcodeReg op) = dst.setWidth 5) := by
  by_cases hlow : dst.toNat < 4
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexPrefix
    revert dst
    decide

def encodeMovR8Imm8NoRex (dst : BitVec 3) (imm : BitVec 8) : List UInt8 :=
  UInt8.ofNat (0xB0 + dst.toNat) :: immBytes 8 imm

theorem encodeMovR8Imm8NoRex_op : ∀ dst : BitVec 3,
    UInt8.ofNat (0xB0 + dst.toNat) ∈ [0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7] ∧
      opcodeReg (UInt8.ofNat (0xB0 + dst.toNat)) = dst := by
  decide

end X86Proofs
