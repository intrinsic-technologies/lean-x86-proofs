import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.Escape
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeCmovR64R64 (cc : BitVec 4) (dst src : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat % 8)
  [UInt8.ofNat (0x48 + 4 * (dst.toNat / 8) + src.toNat / 8), 0x0F, cmovOpcode cc, modrm]

theorem encodeCmovR64R64_spec (cc : BitVec 4) : ∀ (dst src : BitVec 4), ∃ rex modrm,
    encodeCmovR64R64 cc dst src = [rex, 0x0F, cmovOpcode cc, modrm] ∧ RexWPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = src.setWidth 5 := by
  intro dst src
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst src
  decide

def encodeCmovR32R32 (cc : BitVec 4) (dst src : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat % 8)
  if src.toNat < 8 ∧ dst.toNat < 8 then [0x0F, cmovOpcode cc, modrm]
  else [UInt8.ofNat (0x40 + 4 * (dst.toNat / 8) + src.toNat / 8), 0x0F, cmovOpcode cc, modrm]

theorem encodeCmovR32R32_spec (cc : BitVec 4) : ∀ (dst src : BitVec 4),
    (∃ modrm, encodeCmovR32R32 cc dst src = [0x0F, cmovOpcode cc, modrm] ∧
      modrmMod modrm = 3 ∧ gprNumber 0 0 (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 0 (modrmRm modrm) = src.setWidth 5) ∨
    (∃ rex modrm, encodeCmovR32R32 cc dst src = [rex, 0x0F, cmovOpcode cc, modrm] ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
      gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = src.setWidth 5) := by
  intro dst src
  by_cases hlow : src.toNat < 8 ∧ dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst src
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst src
    decide

def encodeCmovR16R16 (cc : BitVec 4) (dst src : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat % 8)
  if src.toNat < 8 ∧ dst.toNat < 8 then [0x66, 0x0F, cmovOpcode cc, modrm]
  else [0x66, UInt8.ofNat (0x40 + 4 * (dst.toNat / 8) + src.toNat / 8), 0x0F, cmovOpcode cc, modrm]

theorem encodeCmovR16R16_spec (cc : BitVec 4) : ∀ (dst src : BitVec 4),
    (∃ modrm, encodeCmovR16R16 cc dst src = [0x66, 0x0F, cmovOpcode cc, modrm] ∧
      modrmMod modrm = 3 ∧ gprNumber 0 0 (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 0 (modrmRm modrm) = src.setWidth 5) ∨
    (∃ rex modrm, encodeCmovR16R16 cc dst src = [0x66, rex, 0x0F, cmovOpcode cc, modrm] ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
      gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = src.setWidth 5) := by
  intro dst src
  by_cases hlow : src.toNat < 8 ∧ dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst src
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst src
    decide

end X86Proofs
