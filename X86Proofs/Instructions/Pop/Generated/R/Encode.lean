import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodePop8FR64 (r : BitVec 4) : List UInt8 :=
  if r.toNat < 8 then [0x8F, UInt8.ofNat (0xC0 + r.toNat)]
  else [0x41, 0x8F, UInt8.ofNat (0xC0 + r.toNat % 8)]

theorem encodePop8FR64_spec (r : BitVec 4) :
    (∃ modrm, encodePop8FR64 r = [0x8F, modrm] ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 0 ∧
      gprNumber 0 0 (modrmRm modrm) = r.setWidth 5) ∨
    (∃ rex modrm, encodePop8FR64 r = [rex, 0x8F, modrm] ∧ RexPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 0 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = r.setWidth 5) := by
  by_cases hlow : r.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert r
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexPrefix
    revert r
    decide

def encodePop8FR16 (r : BitVec 4) : List UInt8 :=
  if r.toNat < 8 then [0x66, 0x8F, UInt8.ofNat (0xC0 + r.toNat)]
  else [0x66, 0x41, 0x8F, UInt8.ofNat (0xC0 + r.toNat % 8)]

theorem encodePop8FR16_spec (r : BitVec 4) :
    (∃ modrm, encodePop8FR16 r = [0x66, 0x8F, modrm] ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = 0 ∧ gprNumber 0 0 (modrmRm modrm) = r.setWidth 5) ∨
    (∃ rex modrm, encodePop8FR16 r = [0x66, rex, 0x8F, modrm] ∧ RexNoWPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 0 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = r.setWidth 5) := by
  by_cases hlow : r.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert r
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert r
    decide

end X86Proofs
