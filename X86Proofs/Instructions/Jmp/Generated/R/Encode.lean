import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeJmpR64 (r : BitVec 4) : List UInt8 :=
  if r.toNat < 8 then [0xFF, UInt8.ofNat (0xE0 + r.toNat)]
  else [0x41, 0xFF, UInt8.ofNat (0xE0 + r.toNat % 8)]

theorem encodeJmpR64_spec (r : BitVec 4) :
    (∃ modrm, encodeJmpR64 r = [0xFF, modrm] ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 4 ∧
      gprNumber 0 0 (modrmRm modrm) = r.setWidth 5) ∨
    (∃ rex modrm, encodeJmpR64 r = [rex, 0xFF, modrm] ∧ RexPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 4 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = r.setWidth 5) := by
  by_cases hlow : r.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert r
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexPrefix
    revert r
    decide

end X86Proofs
