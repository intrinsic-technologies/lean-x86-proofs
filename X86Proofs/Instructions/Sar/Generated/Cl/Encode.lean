import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeSarR64Cl (dst : BitVec 4) : List UInt8 :=
  [UInt8.ofNat (0x48 + dst.toNat / 8), 0xD3, UInt8.ofNat (0xF8 + dst.toNat % 8)]

theorem encodeSarR64Cl_spec : ∀ dst : BitVec 4, ∃ rex modrm,
    encodeSarR64Cl dst = [rex, 0xD3, modrm] ∧ RexWPrefix rex.toBitVec ∧
    modrmMod modrm = 3 ∧ modrmReg modrm = 7 ∧
    gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 := by
  intro dst
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst
  decide

def encodeSarR32Cl (dst : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xF8 + dst.toNat % 8)
  if dst.toNat < 8 then [0xD3, modrm]
  else [UInt8.ofNat (0x40 + dst.toNat / 8), 0xD3, modrm]

theorem encodeSarR32Cl_spec : ∀ dst : BitVec 4,
    (∃ modrm, encodeSarR32Cl dst = [0xD3, modrm] ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = 7 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeSarR32Cl dst = [rex, 0xD3, modrm] ∧ RexNoWPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 7 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5) := by
  intro dst
  by_cases hlow : dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst
    decide

def encodeSarR16Cl (dst : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xF8 + dst.toNat % 8)
  if dst.toNat < 8 then [0x66, 0xD3, modrm]
  else [0x66, UInt8.ofNat (0x40 + dst.toNat / 8), 0xD3, modrm]

theorem encodeSarR16Cl_spec : ∀ dst : BitVec 4,
    (∃ modrm, encodeSarR16Cl dst = [0x66, 0xD3, modrm] ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = 7 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeSarR16Cl dst = [0x66, rex, 0xD3, modrm] ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 7 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5) := by
  intro dst
  by_cases hlow : dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst
    decide

end X86Proofs
