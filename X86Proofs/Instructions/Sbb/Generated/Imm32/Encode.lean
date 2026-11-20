import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeSbbR64Imm32 (dst : BitVec 4) (imm : BitVec 32) : List UInt8 :=
  UInt8.ofNat (0x48 + dst.toNat / 8) :: 0x81 :: UInt8.ofNat (0xD8 + dst.toNat % 8) ::
    immBytes 32 imm

theorem encodeSbbR64Imm32_spec (dst : BitVec 4) (imm : BitVec 32) : ∃ rex modrm,
    encodeSbbR64Imm32 dst imm = rex :: 0x81 :: modrm :: immBytes 32 imm ∧ RexWPrefix rex.toBitVec ∧
    modrmMod modrm = 3 ∧ modrmReg modrm = 3 ∧
    gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 := by
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst
  decide

def encodeSbbR32Imm32 (dst : BitVec 4) (imm : BitVec 32) : List UInt8 :=
  let modrm := UInt8.ofNat (0xD8 + dst.toNat % 8)
  if dst.toNat < 8 then 0x81 :: modrm :: immBytes 32 imm
  else UInt8.ofNat (0x40 + dst.toNat / 8) :: 0x81 :: modrm :: immBytes 32 imm

theorem encodeSbbR32Imm32_spec (dst : BitVec 4) (imm : BitVec 32) :
    (∃ modrm, encodeSbbR32Imm32 dst imm = 0x81 :: modrm :: immBytes 32 imm ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 3 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeSbbR32Imm32 dst imm = rex :: 0x81 :: modrm :: immBytes 32 imm ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 3 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5) := by
  by_cases hlow : dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst
    decide

def encodeSbbR16Imm16 (dst : BitVec 4) (imm : BitVec 16) : List UInt8 :=
  let modrm := UInt8.ofNat (0xD8 + dst.toNat % 8)
  if dst.toNat < 8 then 0x66 :: 0x81 :: modrm :: immBytes 16 imm
  else 0x66 :: UInt8.ofNat (0x40 + dst.toNat / 8) :: 0x81 :: modrm :: immBytes 16 imm

theorem encodeSbbR16Imm16_spec (dst : BitVec 4) (imm : BitVec 16) :
    (∃ modrm, encodeSbbR16Imm16 dst imm = 0x66 :: 0x81 :: modrm :: immBytes 16 imm ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 3 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeSbbR16Imm16 dst imm = 0x66 :: rex :: 0x81 :: modrm :: immBytes 16 imm ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 3 ∧
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
