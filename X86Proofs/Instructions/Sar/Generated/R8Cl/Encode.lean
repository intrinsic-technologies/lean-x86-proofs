import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeSarR8Cl (dst : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xF8 + dst.toNat % 8)
  if dst.toNat < 4 then [0xD2, modrm]
  else [UInt8.ofNat (0x40 + dst.toNat / 8), 0xD2, modrm]

theorem encodeSarR8Cl_spec : ∀ dst : BitVec 4,
    (∃ modrm, encodeSarR8Cl dst = [0xD2, modrm] ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = 7 ∧ (modrmRm modrm).toNat < 4 ∧
      gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeSarR8Cl dst = [rex, 0xD2, modrm] ∧ RexPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 7 ∧
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

def encodeSarR8ClNoRex (dst : BitVec 3) : List UInt8 :=
  [0xD2, modrmRegs 7 dst]


end X86Proofs
