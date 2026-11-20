import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeBtcR64Imm8 (dst : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  UInt8.ofNat (0x48 + dst.toNat / 8) :: 0x0F :: 0xBA :: UInt8.ofNat (0xF8 + dst.toNat % 8) ::
    immBytes 8 imm

theorem encodeBtcR64Imm8_spec (dst : BitVec 4) (imm : BitVec 8) : ∃ rex modrm,
    encodeBtcR64Imm8 dst imm = rex :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm ∧
    RexWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 7 ∧
    gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 := by
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst
  decide

def encodeBtcR32Imm8 (dst : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  let modrm := UInt8.ofNat (0xF8 + dst.toNat % 8)
  if dst.toNat < 8 then 0x0F :: 0xBA :: modrm :: immBytes 8 imm
  else UInt8.ofNat (0x40 + dst.toNat / 8) :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm

theorem encodeBtcR32Imm8_spec (dst : BitVec 4) (imm : BitVec 8) :
    (∃ modrm, encodeBtcR32Imm8 dst imm = 0x0F :: 0xBA :: modrm :: immBytes 8 imm ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 7 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm,
      encodeBtcR32Imm8 dst imm = rex :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 7 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5) := by
  by_cases hlow : dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst
    decide

def encodeBtcR16Imm8 (dst : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  let modrm := UInt8.ofNat (0xF8 + dst.toNat % 8)
  if dst.toNat < 8 then 0x66 :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm
  else 0x66 :: UInt8.ofNat (0x40 + dst.toNat / 8) :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm

theorem encodeBtcR16Imm8_spec (dst : BitVec 4) (imm : BitVec 8) :
    (∃ modrm, encodeBtcR16Imm8 dst imm = 0x66 :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 7 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm,
      encodeBtcR16Imm8 dst imm = 0x66 :: rex :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 7 ∧
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
