import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeOrR8Imm8 (dst : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC8 + dst.toNat % 8)
  if dst.toNat < 4 then 0x80 :: modrm :: immBytes 8 imm
  else UInt8.ofNat (0x40 + dst.toNat / 8) :: 0x80 :: modrm :: immBytes 8 imm

theorem encodeOrR8Imm8_spec (dst : BitVec 4) (imm : BitVec 8) :
    (∃ modrm, encodeOrR8Imm8 dst imm = 0x80 :: modrm :: immBytes 8 imm ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 1 ∧ (modrmRm modrm).toNat < 4 ∧
      gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeOrR8Imm8 dst imm = rex :: 0x80 :: modrm :: immBytes 8 imm ∧
      RexPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 1 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5) := by
  by_cases hlow : dst.toNat < 4
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexPrefix
    revert dst
    decide

def encodeOrR8Imm8NoRex (dst : BitVec 3) (imm : BitVec 8) : List UInt8 :=
  0x80 :: modrmRegs 1 dst :: immBytes 8 imm

end X86Proofs
