import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeSbbR64R64Rev (dst src : BitVec 4) : List UInt8 :=
  [UInt8.ofNat (0x48 + 4 * (dst.toNat / 8) + src.toNat / 8), 0x1B,
    UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat % 8)]

theorem encodeSbbR64R64Rev_spec : ∀ dst src : BitVec 4, ∃ rex modrm,
    encodeSbbR64R64Rev dst src = [rex, 0x1B, modrm] ∧ RexWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
    gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = dst.setWidth 5 ∧
    gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = src.setWidth 5 := by
  intro dst src
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst src
  decide

def encodeSbbR32R32Rev (dst src : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat % 8)
  if src.toNat < 8 ∧ dst.toNat < 8 then [0x1B, modrm]
  else [UInt8.ofNat (0x40 + 4 * (dst.toNat / 8) + src.toNat / 8), 0x1B, modrm]

theorem encodeSbbR32R32Rev_spec : ∀ dst src : BitVec 4,
    (∃ modrm, encodeSbbR32R32Rev dst src = [0x1B, modrm] ∧ modrmMod modrm = 3 ∧
      gprNumber 0 0 (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 0 (modrmRm modrm) = src.setWidth 5) ∨
    (∃ rex modrm, encodeSbbR32R32Rev dst src = [rex, 0x1B, modrm] ∧ RexNoWPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = dst.setWidth 5 ∧
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

def encodeSbbR16R16Rev (dst src : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat % 8)
  if src.toNat < 8 ∧ dst.toNat < 8 then [0x66, 0x1B, modrm]
  else [0x66, UInt8.ofNat (0x40 + 4 * (dst.toNat / 8) + src.toNat / 8), 0x1B, modrm]

theorem encodeSbbR16R16Rev_spec : ∀ dst src : BitVec 4,
    (∃ modrm, encodeSbbR16R16Rev dst src = [0x66, 0x1B, modrm] ∧ modrmMod modrm = 3 ∧
      gprNumber 0 0 (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 0 (modrmRm modrm) = src.setWidth 5) ∨
    (∃ rex modrm, encodeSbbR16R16Rev dst src = [0x66, rex, 0x1B, modrm] ∧
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
