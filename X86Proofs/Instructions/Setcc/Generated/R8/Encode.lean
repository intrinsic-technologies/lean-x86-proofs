import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.Escape
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeSetccR8 (cc : BitVec 4) (dst : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + dst.toNat % 8)
  if dst.toNat < 4 then [0x0F, setccOpcode cc, modrm]
  else [UInt8.ofNat (0x40 + dst.toNat / 8), 0x0F, setccOpcode cc, modrm]

theorem encodeSetccR8_spec (cc : BitVec 4) : ∀ dst : BitVec 4,
    (∃ modrm, encodeSetccR8 cc dst = [0x0F, setccOpcode cc, modrm] ∧ modrmMod modrm = 3 ∧
      (modrmRm modrm).toNat < 4 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeSetccR8 cc dst = [rex, 0x0F, setccOpcode cc, modrm] ∧
      RexPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
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

def encodeSetccR8NoRex (cc : BitVec 4) (dst : BitVec 3) : List UInt8 :=
  [0x0F, setccOpcode cc, modrmRegs 0 dst]

end X86Proofs
