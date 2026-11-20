import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeImulR64R64Imm32 (dst src : BitVec 4) (imm : BitVec 32) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat % 8)
  UInt8.ofNat (0x48 + 4 * (dst.toNat / 8) + src.toNat / 8) :: 0x69 :: modrm :: immBytes 32 imm

theorem encodeImulR64R64Imm32_spec : ∀ (dst src : BitVec 4) (imm : BitVec 32), ∃ rex modrm,
    encodeImulR64R64Imm32 dst src imm = rex :: 0x69 :: modrm :: immBytes 32 imm ∧ RexWPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = src.setWidth 5 := by
  intro dst src imm
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst src
  decide

def encodeImulR32R32Imm32 (dst src : BitVec 4) (imm : BitVec 32) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat % 8)
  if src.toNat < 8 ∧ dst.toNat < 8 then 0x69 :: modrm :: immBytes 32 imm
  else UInt8.ofNat (0x40 + 4 * (dst.toNat / 8) + src.toNat / 8) :: 0x69 :: modrm :: immBytes 32 imm

theorem encodeImulR32R32Imm32_spec : ∀ (dst src : BitVec 4) (imm : BitVec 32),
    (∃ modrm, encodeImulR32R32Imm32 dst src imm = 0x69 :: modrm :: immBytes 32 imm ∧ modrmMod modrm = 3 ∧
      gprNumber 0 0 (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 0 (modrmRm modrm) = src.setWidth 5) ∨
    (∃ rex modrm, encodeImulR32R32Imm32 dst src imm = rex :: 0x69 :: modrm :: immBytes 32 imm ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
      gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = src.setWidth 5) := by
  intro dst src imm
  by_cases hlow : src.toNat < 8 ∧ dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst src
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst src
    decide

def encodeImulR16R16Imm16 (dst src : BitVec 4) (imm : BitVec 16) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat % 8)
  if src.toNat < 8 ∧ dst.toNat < 8 then 0x66 :: 0x69 :: modrm :: immBytes 16 imm
  else 0x66 :: UInt8.ofNat (0x40 + 4 * (dst.toNat / 8) + src.toNat / 8) :: 0x69 :: modrm :: immBytes 16 imm

theorem encodeImulR16R16Imm16_spec : ∀ (dst src : BitVec 4) (imm : BitVec 16),
    (∃ modrm, encodeImulR16R16Imm16 dst src imm = 0x66 :: 0x69 :: modrm :: immBytes 16 imm ∧ modrmMod modrm = 3 ∧
      gprNumber 0 0 (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 0 (modrmRm modrm) = src.setWidth 5) ∨
    (∃ rex modrm, encodeImulR16R16Imm16 dst src imm = 0x66 :: rex :: 0x69 :: modrm :: immBytes 16 imm ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
      gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = src.setWidth 5) := by
  intro dst src imm
  by_cases hlow : src.toNat < 8 ∧ dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst src
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst src
    decide

end X86Proofs
