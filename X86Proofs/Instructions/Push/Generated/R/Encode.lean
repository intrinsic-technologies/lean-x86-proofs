import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodePushFFR64 (r : BitVec 4) : List UInt8 :=
  if r.toNat < 8 then [0xFF, UInt8.ofNat (0xF0 + r.toNat)]
  else [0x41, 0xFF, UInt8.ofNat (0xF0 + r.toNat % 8)]

theorem encodePushFFR64_spec (r : BitVec 4) :
    (∃ modrm, encodePushFFR64 r = [0xFF, modrm] ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 6 ∧
      gprNumber 0 0 (modrmRm modrm) = r.setWidth 5) ∨
    (∃ rex modrm, encodePushFFR64 r = [rex, 0xFF, modrm] ∧ RexPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 6 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = r.setWidth 5) := by
  by_cases hlow : r.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert r
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexPrefix
    revert r
    decide

def encodePushFFR16 (r : BitVec 4) : List UInt8 :=
  if r.toNat < 8 then [0x66, 0xFF, UInt8.ofNat (0xF0 + r.toNat)]
  else [0x66, 0x41, 0xFF, UInt8.ofNat (0xF0 + r.toNat % 8)]

theorem encodePushFFR16_spec (r : BitVec 4) :
    (∃ modrm, encodePushFFR16 r = [0x66, 0xFF, modrm] ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = 6 ∧ gprNumber 0 0 (modrmRm modrm) = r.setWidth 5) ∨
    (∃ rex modrm, encodePushFFR16 r = [0x66, rex, 0xFF, modrm] ∧ RexNoWPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 6 ∧
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
