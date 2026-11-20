import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeRclR8Imm8 (dst : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  let modrm := UInt8.ofNat (0xD0 + dst.toNat % 8)
  if dst.toNat < 4 then [0xC0, modrm] ++ immBytes 8 imm
  else [UInt8.ofNat (0x40 + dst.toNat / 8), 0xC0, modrm] ++ immBytes 8 imm

theorem encodeRclR8Imm8_spec (imm : BitVec 8) : ∀ dst : BitVec 4,
    (∃ modrm, encodeRclR8Imm8 dst imm = [0xC0, modrm] ++ immBytes 8 imm ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = 2 ∧ (modrmRm modrm).toNat < 4 ∧
      gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeRclR8Imm8 dst imm = [rex, 0xC0, modrm] ++ immBytes 8 imm ∧ RexPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 2 ∧
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

def encodeRclR8One (dst : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xD0 + dst.toNat % 8)
  if dst.toNat < 4 then [0xD0, modrm]
  else [UInt8.ofNat (0x40 + dst.toNat / 8), 0xD0, modrm]

theorem encodeRclR8One_spec : ∀ dst : BitVec 4,
    (∃ modrm, encodeRclR8One dst = [0xD0, modrm] ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = 2 ∧ (modrmRm modrm).toNat < 4 ∧
      gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeRclR8One dst = [rex, 0xD0, modrm] ∧ RexPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 2 ∧
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

def encodeRclR8Imm8NoRex (dst : BitVec 3) (imm : BitVec 8) : List UInt8 :=
  [0xC0, modrmRegs 2 dst] ++ immBytes 8 imm


def encodeRclR8OneNoRex (dst : BitVec 3) : List UInt8 :=
  [0xD0, modrmRegs 2 dst]


end X86Proofs
