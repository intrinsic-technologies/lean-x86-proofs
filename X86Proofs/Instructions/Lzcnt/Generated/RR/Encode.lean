import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeLzcntR64R64 (dst src : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat % 8)
  [0xF3, UInt8.ofNat (0x48 + 4 * (dst.toNat / 8) + src.toNat / 8), 0x0F, 0xBD, modrm]

theorem encodeLzcntR64R64_spec : ∀ (dst src : BitVec 4), ∃ rex modrm,
    encodeLzcntR64R64 dst src = [0xF3, rex, 0x0F, 0xBD, modrm] ∧ RexWPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = src.setWidth 5 := by
  intro dst src
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst src
  decide

def encodeLzcntR32R32 (dst src : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat % 8)
  if src.toNat < 8 ∧ dst.toNat < 8 then [0xF3, 0x0F, 0xBD, modrm]
  else [0xF3, UInt8.ofNat (0x40 + 4 * (dst.toNat / 8) + src.toNat / 8), 0x0F, 0xBD, modrm]

theorem encodeLzcntR32R32_spec : ∀ (dst src : BitVec 4),
    (∃ modrm, encodeLzcntR32R32 dst src = [0xF3, 0x0F, 0xBD, modrm] ∧ modrmMod modrm = 3 ∧
      gprNumber 0 0 (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 0 (modrmRm modrm) = src.setWidth 5) ∨
    (∃ rex modrm, encodeLzcntR32R32 dst src = [0xF3, rex, 0x0F, 0xBD, modrm] ∧
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

def encodeLzcntR16R16 (dst src : BitVec 3) : List UInt8 :=
  [0x66, 0xF3, 0x0F, 0xBD, UInt8.ofNat (0xC0 + 8 * dst.toNat + src.toNat)]

theorem encodeLzcntR16R16_spec : ∀ (dst src : BitVec 3), ∃ modrm,
    encodeLzcntR16R16 dst src = [0x66, 0xF3, 0x0F, 0xBD, modrm] ∧ modrmMod modrm = 3 ∧
      gprNumber 0 0 (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 0 (modrmRm modrm) = src.setWidth 5 := by
  intro dst src
  refine ⟨_, rfl, ?_⟩
  revert dst src
  decide

end X86Proofs
