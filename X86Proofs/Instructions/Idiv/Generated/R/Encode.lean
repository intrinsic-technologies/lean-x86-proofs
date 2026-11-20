import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeIdivR64 (dst : BitVec 4) : List UInt8 :=
  [UInt8.ofNat (0x48 + dst.toNat / 8), 0xF7, UInt8.ofNat (0xF8 + dst.toNat % 8)]

theorem encodeIdivR64_spec : ∀ dst : BitVec 4, ∃ rex modrm,
    encodeIdivR64 dst = [rex, 0xF7, modrm] ∧ RexWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
    modrmReg modrm = 7 ∧ gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 := by
  intro dst
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst
  decide

def encodeIdivR32 (dst : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xF8 + dst.toNat % 8)
  if dst.toNat < 8 then [0xF7, modrm] else [0x41, 0xF7, modrm]

theorem encodeIdivR32_spec : ∀ dst : BitVec 4,
    (∃ modrm, encodeIdivR32 dst = [0xF7, modrm] ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 7 ∧
      gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeIdivR32 dst = [rex, 0xF7, modrm] ∧ RexNoWPrefix rex.toBitVec ∧
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

def encodeIdivR16 (dst : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xF8 + dst.toNat % 8)
  if dst.toNat < 8 then [0x66, 0xF7, modrm] else [0x66, 0x41, 0xF7, modrm]

theorem encodeIdivR16_spec : ∀ dst : BitVec 4,
    (∃ modrm, encodeIdivR16 dst = [0x66, 0xF7, modrm] ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = 7 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeIdivR16 dst = [0x66, rex, 0xF7, modrm] ∧ RexNoWPrefix rex.toBitVec ∧
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

end X86Proofs
