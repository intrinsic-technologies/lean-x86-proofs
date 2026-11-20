import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeSbbR64R64 (dst src : BitVec 4) : List UInt8 :=
  [UInt8.ofNat (0x48 + 4 * (src.toNat / 8) + dst.toNat / 8), 0x19,
    UInt8.ofNat (0xC0 + 8 * (src.toNat % 8) + dst.toNat % 8)]

theorem encodeSbbR64R64_spec : ∀ dst src : BitVec 4, ∃ rex modrm,
    encodeSbbR64R64 dst src = [rex, 0x19, modrm] ∧ RexWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
    gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 ∧
    gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = src.setWidth 5 := by
  intro dst src
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst src
  decide

def encodeSbbR32R32 (dst src : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (src.toNat % 8) + dst.toNat % 8)
  if src.toNat < 8 ∧ dst.toNat < 8 then [0x19, modrm]
  else [UInt8.ofNat (0x40 + 4 * (src.toNat / 8) + dst.toNat / 8), 0x19, modrm]

theorem encodeSbbR32R32_spec : ∀ dst src : BitVec 4,
    (∃ modrm, encodeSbbR32R32 dst src = [0x19, modrm] ∧ modrmMod modrm = 3 ∧
      gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5 ∧
      gprNumber 0 0 (modrmReg modrm) = src.setWidth 5) ∨
    (∃ rex modrm, encodeSbbR32R32 dst src = [rex, 0x19, modrm] ∧ RexNoWPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 ∧
      gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = src.setWidth 5) := by
  intro dst src
  by_cases hlow : src.toNat < 8 ∧ dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst src
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst src
    decide

def encodeSbbR16R16 (dst src : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (src.toNat % 8) + dst.toNat % 8)
  if src.toNat < 8 ∧ dst.toNat < 8 then [0x66, 0x19, modrm]
  else [0x66, UInt8.ofNat (0x40 + 4 * (src.toNat / 8) + dst.toNat / 8), 0x19, modrm]

theorem encodeSbbR16R16_spec : ∀ dst src : BitVec 4,
    (∃ modrm, encodeSbbR16R16 dst src = [0x66, 0x19, modrm] ∧ modrmMod modrm = 3 ∧
      gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5 ∧
      gprNumber 0 0 (modrmReg modrm) = src.setWidth 5) ∨
    (∃ rex modrm, encodeSbbR16R16 dst src = [0x66, rex, 0x19, modrm] ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 ∧
      gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = src.setWidth 5) := by
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
