import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeOrR64Imm8 (dst : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  UInt8.ofNat (0x48 + dst.toNat / 8) :: 0x83 :: UInt8.ofNat (0xC8 + dst.toNat % 8) ::
    immBytes 8 imm

theorem encodeOrR64Imm8_spec (dst : BitVec 4) (imm : BitVec 8) : ∃ rex modrm,
    encodeOrR64Imm8 dst imm = rex :: 0x83 :: modrm :: immBytes 8 imm ∧ RexWPrefix rex.toBitVec ∧
    modrmMod modrm = 3 ∧ modrmReg modrm = 1 ∧
    gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 := by
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst
  decide

def encodeOrR32Imm8 (dst : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC8 + dst.toNat % 8)
  if dst.toNat < 8 then 0x83 :: modrm :: immBytes 8 imm
  else UInt8.ofNat (0x40 + dst.toNat / 8) :: 0x83 :: modrm :: immBytes 8 imm

theorem encodeOrR32Imm8_spec (dst : BitVec 4) (imm : BitVec 8) :
    (∃ modrm, encodeOrR32Imm8 dst imm = 0x83 :: modrm :: immBytes 8 imm ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 1 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeOrR32Imm8 dst imm = rex :: 0x83 :: modrm :: immBytes 8 imm ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 1 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5) := by
  by_cases hlow : dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst
    decide

def encodeOrR16Imm8 (dst : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC8 + dst.toNat % 8)
  if dst.toNat < 8 then 0x66 :: 0x83 :: modrm :: immBytes 8 imm
  else 0x66 :: UInt8.ofNat (0x40 + dst.toNat / 8) :: 0x83 :: modrm :: immBytes 8 imm

theorem encodeOrR16Imm8_spec (dst : BitVec 4) (imm : BitVec 8) :
    (∃ modrm, encodeOrR16Imm8 dst imm = 0x66 :: 0x83 :: modrm :: immBytes 8 imm ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 1 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeOrR16Imm8 dst imm = 0x66 :: rex :: 0x83 :: modrm :: immBytes 8 imm ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 1 ∧
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
