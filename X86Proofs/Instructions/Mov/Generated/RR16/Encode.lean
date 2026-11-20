import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeMovR16R16 (dst src : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (src.toNat % 8) + dst.toNat % 8)
  if src.toNat < 8 ∧ dst.toNat < 8 then [0x66, 0x89, modrm]
  else [0x66, UInt8.ofNat (0x40 + 4 * (src.toNat / 8) + dst.toNat / 8), 0x89, modrm]

theorem encodeMovR16R16_spec : ∀ (dst src : BitVec 4),
    (∃ modrm, encodeMovR16R16 dst src = [0x66, 0x89, modrm] ∧ modrmMod modrm = 3 ∧
      gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5 ∧
      gprNumber 0 0 (modrmReg modrm) = src.setWidth 5) ∨
    (∃ rex modrm, encodeMovR16R16 dst src = [0x66, rex, 0x89, modrm] ∧
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
