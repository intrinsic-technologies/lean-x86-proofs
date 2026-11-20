import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeSmswR64 (dst : BitVec 4) : List UInt8 :=
  [UInt8.ofNat (0x48 + dst.toNat / 8), 0x0F, 0x01, UInt8.ofNat (0xE0 + dst.toNat % 8)]

theorem encodeSmswR64_spec : ∀ (dst : BitVec 4), ∃ rex modrm,
    encodeSmswR64 dst = [rex, 0x0F, 0x01, modrm] ∧ RexWPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 4 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 := by
  intro dst
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst
  decide

def encodeSmswR32 (dst : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xE0 + dst.toNat % 8)
  if dst.toNat < 8 then [0x0F, 0x01, modrm]
  else [UInt8.ofNat (0x40 + dst.toNat / 8), 0x0F, 0x01, modrm]

theorem encodeSmswR32_spec : ∀ (dst : BitVec 4),
    (∃ modrm, encodeSmswR32 dst = [0x0F, 0x01, modrm] ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = 4 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeSmswR32 dst = [rex, 0x0F, 0x01, modrm] ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 4 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5) := by
  intro dst
  by_cases hlow : dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst
    decide

def encodeSmswR16 (dst : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xE0 + dst.toNat % 8)
  if dst.toNat < 8 then [0x66, 0x0F, 0x01, modrm]
  else [0x66, UInt8.ofNat (0x40 + dst.toNat / 8), 0x0F, 0x01, modrm]

theorem encodeSmswR16_spec : ∀ (dst : BitVec 4),
    (∃ modrm, encodeSmswR16 dst = [0x66, 0x0F, 0x01, modrm] ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = 4 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeSmswR16 dst = [0x66, rex, 0x0F, 0x01, modrm] ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 4 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5) := by
  intro dst
  by_cases hlow : dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst
    decide

end X86Proofs
