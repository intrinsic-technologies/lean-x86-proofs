import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeMulR8 (dst : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xE0 + dst.toNat % 8)
  if dst.toNat < 4 then [0xF6, modrm]
  else [UInt8.ofNat (0x40 + dst.toNat / 8), 0xF6, modrm]

theorem encodeMulR8_spec : ∀ dst : BitVec 4,
    (∃ modrm, encodeMulR8 dst = [0xF6, modrm] ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = 4 ∧ (modrmRm modrm).toNat < 4 ∧
      gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeMulR8 dst = [rex, 0xF6, modrm] ∧ RexPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 4 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5) := by
  intro dst
  by_cases hlow : dst.toNat < 4
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexPrefix
    revert dst
    decide

def encodeMulR8NoRex (dst : BitVec 3) : List UInt8 :=
  [0xF6, modrmRegs 4 dst]

end X86Proofs
