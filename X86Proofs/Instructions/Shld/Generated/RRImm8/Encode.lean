import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeShldR64R64Imm8 (dst src : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (src.toNat % 8) + dst.toNat % 8)
  UInt8.ofNat (0x48 + 4 * (src.toNat / 8) + dst.toNat / 8) :: 0x0F :: 0xA4 :: modrm :: immBytes 8 imm

theorem encodeShldR64R64Imm8_spec (dst src : BitVec 4) (imm : BitVec 8) : ∃ rex modrm,
    encodeShldR64R64Imm8 dst src imm = rex :: 0x0F :: 0xA4 :: modrm :: immBytes 8 imm ∧
      RexWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 ∧
      gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = src.setWidth 5 := by
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst src
  decide

def encodeShldR32R32Imm8 (dst src : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (src.toNat % 8) + dst.toNat % 8)
  if src.toNat < 8 ∧ dst.toNat < 8 then 0x0F :: 0xA4 :: modrm :: immBytes 8 imm
  else UInt8.ofNat (0x40 + 4 * (src.toNat / 8) + dst.toNat / 8) :: 0x0F :: 0xA4 :: modrm :: immBytes 8 imm

theorem encodeShldR32R32Imm8_spec (dst src : BitVec 4) (imm : BitVec 8) :
    (∃ modrm, encodeShldR32R32Imm8 dst src imm = 0x0F :: 0xA4 :: modrm :: immBytes 8 imm ∧
      modrmMod modrm = 3 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5 ∧
      gprNumber 0 0 (modrmReg modrm) = src.setWidth 5) ∨
    (∃ rex modrm, encodeShldR32R32Imm8 dst src imm = rex :: 0x0F :: 0xA4 :: modrm :: immBytes 8 imm ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 ∧
      gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = src.setWidth 5) := by
  by_cases hlow : src.toNat < 8 ∧ dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst src
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst src
    decide

def encodeShldR16R16Imm8 (dst src : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (src.toNat % 8) + dst.toNat % 8)
  if src.toNat < 8 ∧ dst.toNat < 8 then 0x66 :: 0x0F :: 0xA4 :: modrm :: immBytes 8 imm
  else 0x66 :: UInt8.ofNat (0x40 + 4 * (src.toNat / 8) + dst.toNat / 8) :: 0x0F :: 0xA4 :: modrm :: immBytes 8 imm

theorem encodeShldR16R16Imm8_spec (dst src : BitVec 4) (imm : BitVec 8) :
    (∃ modrm, encodeShldR16R16Imm8 dst src imm = 0x66 :: 0x0F :: 0xA4 :: modrm :: immBytes 8 imm ∧
      modrmMod modrm = 3 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5 ∧
      gprNumber 0 0 (modrmReg modrm) = src.setWidth 5) ∨
    (∃ rex modrm, encodeShldR16R16Imm8 dst src imm = 0x66 :: rex :: 0x0F :: 0xA4 :: modrm :: immBytes 8 imm ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 ∧
      gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = src.setWidth 5) := by
  by_cases hlow : src.toNat < 8 ∧ dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst src
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst src
    decide

end X86Proofs
