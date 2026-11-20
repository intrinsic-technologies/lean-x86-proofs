import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeDecR64 (dst : BitVec 4) : List UInt8 :=
  [UInt8.ofNat (0x48 + dst.toNat / 8), 0xFF, UInt8.ofNat (0xC8 + dst.toNat % 8)]

theorem encodeDecR64_spec : ∀ dst : BitVec 4, ∃ rex modrm,
    encodeDecR64 dst = [rex, 0xFF, modrm] ∧ RexWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
    modrmReg modrm = 1 ∧ gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 := by
  intro dst
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst
  decide

def encodeDecR32 (dst : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC8 + dst.toNat % 8)
  if dst.toNat < 8 then [0xFF, modrm] else [0x41, 0xFF, modrm]

theorem encodeDecR32_spec : ∀ dst : BitVec 4,
    (∃ modrm, encodeDecR32 dst = [0xFF, modrm] ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 1 ∧
      gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeDecR32 dst = [rex, 0xFF, modrm] ∧ RexNoWPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 1 ∧
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

def encodeDecR16 (dst : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC8 + dst.toNat % 8)
  if dst.toNat < 8 then [0x66, 0xFF, modrm] else [0x66, 0x41, 0xFF, modrm]

theorem encodeDecR16_spec : ∀ dst : BitVec 4,
    (∃ modrm, encodeDecR16 dst = [0x66, 0xFF, modrm] ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = 1 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeDecR16 dst = [0x66, rex, 0xFF, modrm] ∧ RexNoWPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 1 ∧
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
