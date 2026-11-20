import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeMovR8Imm8C6 (dst : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + dst.toNat % 8)
  if dst.toNat < 4 then 0xC6 :: modrm :: immBytes 8 imm
  else UInt8.ofNat (0x40 + dst.toNat / 8) :: 0xC6 :: modrm :: immBytes 8 imm

theorem encodeMovR8Imm8C6_spec (dst : BitVec 4) (imm : BitVec 8) :
    (∃ modrm, encodeMovR8Imm8C6 dst imm = 0xC6 :: modrm :: immBytes 8 imm ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 0 ∧
      (modrmRm modrm).toNat < 4 ∧
      gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm,
      encodeMovR8Imm8C6 dst imm = rex :: 0xC6 :: modrm :: immBytes 8 imm ∧
      RexPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 0 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5) := by
  by_cases hlow : dst.toNat < 4
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexPrefix
    revert dst
    decide

def encodeMovR8Imm8C6NoRex (dst : BitVec 3) (imm : BitVec 8) : List UInt8 :=
  0xC6 :: modrmRegs 0 dst :: immBytes 8 imm

end X86Proofs
