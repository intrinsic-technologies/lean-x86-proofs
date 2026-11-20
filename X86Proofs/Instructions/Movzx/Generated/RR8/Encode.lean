import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeMovzxR64R8 (dst src : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat % 8)
  [UInt8.ofNat (0x48 + 4 * (dst.toNat / 8) + src.toNat / 8), 0x0F, 0xB6, modrm]

theorem encodeMovzxR64R8_spec : ∀ (dst src : BitVec 4), ∃ rex modrm,
    encodeMovzxR64R8 dst src = [rex, 0x0F, 0xB6, modrm] ∧ RexWPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = src.setWidth 5 := by
  intro dst src
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst src
  decide

def encodeMovzxR32R8 (dst src : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat % 8)
  if src.toNat < 4 ∧ dst.toNat < 8 then [0x0F, 0xB6, modrm]
  else [UInt8.ofNat (0x40 + 4 * (dst.toNat / 8) + src.toNat / 8), 0x0F, 0xB6, modrm]

theorem encodeMovzxR32R8_spec : ∀ (dst src : BitVec 4),
    (∃ modrm, encodeMovzxR32R8 dst src = [0x0F, 0xB6, modrm] ∧ modrmMod modrm = 3 ∧
      (modrmRm modrm).toNat < 4 ∧
      gprNumber 0 0 (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 0 (modrmRm modrm) = src.setWidth 5) ∨
    (∃ rex modrm, encodeMovzxR32R8 dst src = [rex, 0x0F, 0xB6, modrm] ∧
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

def encodeMovzxR16R8 (dst src : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat % 8)
  if src.toNat < 4 ∧ dst.toNat < 8 then [0x66, 0x0F, 0xB6, modrm]
  else [0x66, UInt8.ofNat (0x40 + 4 * (dst.toNat / 8) + src.toNat / 8), 0x0F, 0xB6, modrm]

theorem encodeMovzxR16R8_spec : ∀ (dst src : BitVec 4),
    (∃ modrm, encodeMovzxR16R8 dst src = [0x66, 0x0F, 0xB6, modrm] ∧ modrmMod modrm = 3 ∧
      (modrmRm modrm).toNat < 4 ∧
      gprNumber 0 0 (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 0 (modrmRm modrm) = src.setWidth 5) ∨
    (∃ rex modrm, encodeMovzxR16R8 dst src = [0x66, rex, 0x0F, 0xB6, modrm] ∧
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

def encodeMovzxR32R8NoRex (dst src : BitVec 3) : List UInt8 :=
  [0x0F, 0xB6, modrmRegs dst src]

def encodeMovzxR16R8NoRex (dst src : BitVec 3) : List UInt8 :=
  [0x66, 0x0F, 0xB6, modrmRegs dst src]

end X86Proofs
