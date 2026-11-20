import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeSalR8Imm8 (dst : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  let modrm := UInt8.ofNat (0xF0 + dst.toNat % 8)
  if dst.toNat < 4 then [0xC0, modrm] ++ immBytes 8 imm
  else [UInt8.ofNat (0x40 + dst.toNat / 8), 0xC0, modrm] ++ immBytes 8 imm

theorem encodeSalR8Imm8_spec (imm : BitVec 8) : ∀ dst : BitVec 4,
    (∃ modrm, encodeSalR8Imm8 dst imm = [0xC0, modrm] ++ immBytes 8 imm ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = 6 ∧ (modrmRm modrm).toNat < 4 ∧
      gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeSalR8Imm8 dst imm = [rex, 0xC0, modrm] ++ immBytes 8 imm ∧ RexPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 6 ∧
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

def encodeSalR8One (dst : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xF0 + dst.toNat % 8)
  if dst.toNat < 4 then [0xD0, modrm]
  else [UInt8.ofNat (0x40 + dst.toNat / 8), 0xD0, modrm]

theorem encodeSalR8One_spec : ∀ dst : BitVec 4,
    (∃ modrm, encodeSalR8One dst = [0xD0, modrm] ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = 6 ∧ (modrmRm modrm).toNat < 4 ∧
      gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeSalR8One dst = [rex, 0xD0, modrm] ∧ RexPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 6 ∧
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

def encodeSalR8Imm8NoRex (dst : BitVec 3) (imm : BitVec 8) : List UInt8 :=
  [0xC0, modrmRegs 6 dst] ++ immBytes 8 imm


def encodeSalR8OneNoRex (dst : BitVec 3) : List UInt8 :=
  [0xD0, modrmRegs 6 dst]


end X86Proofs
