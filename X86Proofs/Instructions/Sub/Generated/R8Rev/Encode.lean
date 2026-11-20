import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeSubR8R8Rev (dst src : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat % 8)
  if src.toNat < 4 ∧ dst.toNat < 4 then [0x2A, modrm]
  else [UInt8.ofNat (0x40 + 4 * (dst.toNat / 8) + src.toNat / 8), 0x2A, modrm]

theorem encodeSubR8R8Rev_spec : ∀ dst src : BitVec 4,
    (∃ modrm, encodeSubR8R8Rev dst src = [0x2A, modrm] ∧ modrmMod modrm = 3 ∧
      (modrmReg modrm).toNat < 4 ∧ (modrmRm modrm).toNat < 4 ∧
      gprNumber 0 0 (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 0 (modrmRm modrm) = src.setWidth 5) ∨
    (∃ rex modrm, encodeSubR8R8Rev dst src = [rex, 0x2A, modrm] ∧ RexPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = src.setWidth 5) := by
  intro dst src
  by_cases hlow : src.toNat < 4 ∧ dst.toNat < 4
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst src
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexPrefix
    revert dst src
    decide

def encodeSubR8R8RevNoRex (dst src : BitVec 3) : List UInt8 :=
  [0x2A, modrmRegs dst src]

end X86Proofs
