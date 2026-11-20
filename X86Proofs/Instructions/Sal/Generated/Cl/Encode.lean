import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeSalR64Cl (dst : BitVec 4) : List UInt8 :=
  [UInt8.ofNat (0x48 + dst.toNat / 8), 0xD3, UInt8.ofNat (0xF0 + dst.toNat % 8)]

theorem encodeSalR64Cl_spec : ∀ dst : BitVec 4, ∃ rex modrm,
    encodeSalR64Cl dst = [rex, 0xD3, modrm] ∧ RexWPrefix rex.toBitVec ∧
    modrmMod modrm = 3 ∧ modrmReg modrm = 6 ∧
    gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 := by
  intro dst
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst
  decide

def encodeSalR32Cl (dst : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xF0 + dst.toNat % 8)
  if dst.toNat < 8 then [0xD3, modrm]
  else [UInt8.ofNat (0x40 + dst.toNat / 8), 0xD3, modrm]

theorem encodeSalR32Cl_spec : ∀ dst : BitVec 4,
    (∃ modrm, encodeSalR32Cl dst = [0xD3, modrm] ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = 6 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeSalR32Cl dst = [rex, 0xD3, modrm] ∧ RexNoWPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 6 ∧
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

def encodeSalR16Cl (dst : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xF0 + dst.toNat % 8)
  if dst.toNat < 8 then [0x66, 0xD3, modrm]
  else [0x66, UInt8.ofNat (0x40 + dst.toNat / 8), 0xD3, modrm]

theorem encodeSalR16Cl_spec : ∀ dst : BitVec 4,
    (∃ modrm, encodeSalR16Cl dst = [0x66, 0xD3, modrm] ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = 6 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeSalR16Cl dst = [0x66, rex, 0xD3, modrm] ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 6 ∧
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
