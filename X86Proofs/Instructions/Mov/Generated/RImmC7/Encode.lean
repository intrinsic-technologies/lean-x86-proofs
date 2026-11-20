import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeMovR32Imm32C7 (dst : BitVec 4) (imm : BitVec 32) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + dst.toNat % 8)
  if dst.toNat < 8 then 0xC7 :: modrm :: immBytes 32 imm
  else UInt8.ofNat (0x40 + dst.toNat / 8) :: 0xC7 :: modrm :: immBytes 32 imm

theorem encodeMovR32Imm32C7_spec (dst : BitVec 4) (imm : BitVec 32) :
    (∃ modrm, encodeMovR32Imm32C7 dst imm = 0xC7 :: modrm :: immBytes 32 imm ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 0 ∧
      gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm,
      encodeMovR32Imm32C7 dst imm = rex :: 0xC7 :: modrm :: immBytes 32 imm ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 0 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5) := by
  by_cases hlow : dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst
    decide

def encodeMovR16Imm16C7 (dst : BitVec 4) (imm : BitVec 16) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + dst.toNat % 8)
  if dst.toNat < 8 then 0x66 :: 0xC7 :: modrm :: immBytes 16 imm
  else 0x66 :: UInt8.ofNat (0x40 + dst.toNat / 8) :: 0xC7 :: modrm :: immBytes 16 imm

theorem encodeMovR16Imm16C7_spec (dst : BitVec 4) (imm : BitVec 16) :
    (∃ modrm, encodeMovR16Imm16C7 dst imm = 0x66 :: 0xC7 :: modrm :: immBytes 16 imm ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 0 ∧
      gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm,
      encodeMovR16Imm16C7 dst imm = 0x66 :: rex :: 0xC7 :: modrm :: immBytes 16 imm ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 0 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5) := by
  by_cases hlow : dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst
    decide

end X86Proofs
