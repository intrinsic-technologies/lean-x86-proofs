import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeMovsxR64R8 (dst src : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat % 8)
  [UInt8.ofNat (0x48 + 4 * (dst.toNat / 8) + src.toNat / 8), 0x0F, 0xBE, modrm]

theorem encodeMovsxR64R8_spec : ∀ (dst src : BitVec 4), ∃ rex modrm,
    encodeMovsxR64R8 dst src = [rex, 0x0F, 0xBE, modrm] ∧ RexWPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = src.setWidth 5 := by
  intro dst src
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst src
  decide

def encodeMovsxR32R8 (dst src : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat % 8)
  if src.toNat < 4 ∧ dst.toNat < 8 then [0x0F, 0xBE, modrm]
  else [UInt8.ofNat (0x40 + 4 * (dst.toNat / 8) + src.toNat / 8), 0x0F, 0xBE, modrm]

theorem encodeMovsxR32R8_spec : ∀ (dst src : BitVec 4),
    (∃ modrm, encodeMovsxR32R8 dst src = [0x0F, 0xBE, modrm] ∧ modrmMod modrm = 3 ∧
      (modrmRm modrm).toNat < 4 ∧
      gprNumber 0 0 (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 0 (modrmRm modrm) = src.setWidth 5) ∨
    (∃ rex modrm, encodeMovsxR32R8 dst src = [rex, 0x0F, 0xBE, modrm] ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
      gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = src.setWidth 5) := by
  intro dst src
  by_cases hlow : src.toNat < 4 ∧ dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst src
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst src
    decide

def encodeMovsxR16R8 (dst src : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat % 8)
  if src.toNat < 4 ∧ dst.toNat < 8 then [0x66, 0x0F, 0xBE, modrm]
  else [0x66, UInt8.ofNat (0x40 + 4 * (dst.toNat / 8) + src.toNat / 8), 0x0F, 0xBE, modrm]

theorem encodeMovsxR16R8_spec : ∀ (dst src : BitVec 4),
    (∃ modrm, encodeMovsxR16R8 dst src = [0x66, 0x0F, 0xBE, modrm] ∧ modrmMod modrm = 3 ∧
      (modrmRm modrm).toNat < 4 ∧
      gprNumber 0 0 (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 0 (modrmRm modrm) = src.setWidth 5) ∨
    (∃ rex modrm, encodeMovsxR16R8 dst src = [0x66, rex, 0x0F, 0xBE, modrm] ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
      gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = src.setWidth 5) := by
  intro dst src
  by_cases hlow : src.toNat < 4 ∧ dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst src
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst src
    decide

def encodeMovsxR32R8NoRex (dst src : BitVec 3) : List UInt8 :=
  [0x0F, 0xBE, modrmRegs dst src]

def encodeMovsxR16R8NoRex (dst src : BitVec 3) : List UInt8 :=
  [0x66, 0x0F, 0xBE, modrmRegs dst src]

end X86Proofs
