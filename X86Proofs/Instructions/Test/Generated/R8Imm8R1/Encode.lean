import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeTestR1R8Imm8 (dst : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  UInt8.ofNat (0x40 + dst.toNat / 8) :: 0xF6 :: UInt8.ofNat (0xC8 + dst.toNat % 8) ::
    immBytes 8 imm

theorem encodeTestR1R8Imm8_spec (dst : BitVec 4) (imm : BitVec 8) : ∃ rex modrm,
    encodeTestR1R8Imm8 dst imm = rex :: 0xF6 :: modrm :: immBytes 8 imm ∧ RexPrefix rex.toBitVec ∧
    modrmMod modrm = 3 ∧ modrmReg modrm = 1 ∧
    gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 := by
  refine ⟨_, _, rfl, ?_⟩
  unfold RexPrefix
  revert dst
  decide

def encodeTestR1R8Imm8Low (dst : BitVec 2) (imm : BitVec 8) : List UInt8 :=
  0xF6 :: UInt8.ofNat (0xC8 + dst.toNat) :: immBytes 8 imm

theorem encodeTestR1R8Imm8Low_spec (dst : BitVec 2) (imm : BitVec 8) : ∃ modrm,
    encodeTestR1R8Imm8Low dst imm = 0xF6 :: modrm :: immBytes 8 imm ∧
    modrmMod modrm = 3 ∧ modrmReg modrm = 1 ∧ (modrmRm modrm).toNat < 4 ∧
    gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5 := by
  refine ⟨_, rfl, ?_⟩
  revert dst
  decide

def encodeTestR1R8Imm8NoRex (dst : BitVec 3) (imm : BitVec 8) : List UInt8 :=
  0xF6 :: modrmRegs 1 dst :: immBytes 8 imm

end X86Proofs
