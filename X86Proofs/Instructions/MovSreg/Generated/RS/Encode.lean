import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeMovR64Sreg (dst : BitVec 4) (sreg : BitVec 3) : List UInt8 :=
  [UInt8.ofNat (0x48 + dst.toNat / 8), 0x8C, UInt8.ofNat (0xC0 + 8 * sreg.toNat + dst.toNat % 8)]

theorem encodeMovR64Sreg_spec : ∀ (dst : BitVec 4) (sreg : BitVec 3), ∃ rex modrm,
    encodeMovR64Sreg dst sreg = [rex, 0x8C, modrm] ∧ RexWPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = sreg ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 := by
  intro dst sreg
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst sreg
  decide

def encodeMovR32Sreg (dst : BitVec 4) (sreg : BitVec 3) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * sreg.toNat + dst.toNat % 8)
  if dst.toNat < 8 then [0x8C, modrm]
  else [UInt8.ofNat (0x40 + dst.toNat / 8), 0x8C, modrm]

theorem encodeMovR32Sreg_spec : ∀ (dst : BitVec 4) (sreg : BitVec 3),
    (∃ modrm, encodeMovR32Sreg dst sreg = [0x8C, modrm] ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = sreg ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeMovR32Sreg dst sreg = [rex, 0x8C, modrm] ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = sreg ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5) := by
  intro dst sreg
  by_cases hlow : dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst sreg
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst sreg
    decide

def encodeMovR16Sreg (dst : BitVec 4) (sreg : BitVec 3) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * sreg.toNat + dst.toNat % 8)
  if dst.toNat < 8 then [0x66, 0x8C, modrm]
  else [0x66, UInt8.ofNat (0x40 + dst.toNat / 8), 0x8C, modrm]

theorem encodeMovR16Sreg_spec : ∀ (dst : BitVec 4) (sreg : BitVec 3),
    (∃ modrm, encodeMovR16Sreg dst sreg = [0x66, 0x8C, modrm] ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = sreg ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeMovR16Sreg dst sreg = [0x66, rex, 0x8C, modrm] ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = sreg ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5) := by
  intro dst sreg
  by_cases hlow : dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst sreg
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst sreg
    decide

end X86Proofs
