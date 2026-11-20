import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeShlR64Imm8 (dst : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  [UInt8.ofNat (0x48 + dst.toNat / 8), 0xC1, UInt8.ofNat (0xE0 + dst.toNat % 8)] ++ immBytes 8 imm

theorem encodeShlR64Imm8_spec (imm : BitVec 8) : ∀ dst : BitVec 4, ∃ rex modrm,
    encodeShlR64Imm8 dst imm = [rex, 0xC1, modrm] ++ immBytes 8 imm ∧ RexWPrefix rex.toBitVec ∧
    modrmMod modrm = 3 ∧ modrmReg modrm = 4 ∧
    gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 := by
  intro dst
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst
  decide

def encodeShlR32Imm8 (dst : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  let modrm := UInt8.ofNat (0xE0 + dst.toNat % 8)
  if dst.toNat < 8 then [0xC1, modrm] ++ immBytes 8 imm
  else [UInt8.ofNat (0x40 + dst.toNat / 8), 0xC1, modrm] ++ immBytes 8 imm

theorem encodeShlR32Imm8_spec (imm : BitVec 8) : ∀ dst : BitVec 4,
    (∃ modrm, encodeShlR32Imm8 dst imm = [0xC1, modrm] ++ immBytes 8 imm ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = 4 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeShlR32Imm8 dst imm = [rex, 0xC1, modrm] ++ immBytes 8 imm ∧ RexNoWPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 4 ∧
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

def encodeShlR16Imm8 (dst : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  let modrm := UInt8.ofNat (0xE0 + dst.toNat % 8)
  if dst.toNat < 8 then [0x66, 0xC1, modrm] ++ immBytes 8 imm
  else [0x66, UInt8.ofNat (0x40 + dst.toNat / 8), 0xC1, modrm] ++ immBytes 8 imm

theorem encodeShlR16Imm8_spec (imm : BitVec 8) : ∀ dst : BitVec 4,
    (∃ modrm, encodeShlR16Imm8 dst imm = [0x66, 0xC1, modrm] ++ immBytes 8 imm ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = 4 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeShlR16Imm8 dst imm = [0x66, rex, 0xC1, modrm] ++ immBytes 8 imm ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 4 ∧
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

def encodeShlR64One (dst : BitVec 4) : List UInt8 :=
  [UInt8.ofNat (0x48 + dst.toNat / 8), 0xD1, UInt8.ofNat (0xE0 + dst.toNat % 8)]

theorem encodeShlR64One_spec : ∀ dst : BitVec 4, ∃ rex modrm,
    encodeShlR64One dst = [rex, 0xD1, modrm] ∧ RexWPrefix rex.toBitVec ∧
    modrmMod modrm = 3 ∧ modrmReg modrm = 4 ∧
    gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 := by
  intro dst
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst
  decide

def encodeShlR32One (dst : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xE0 + dst.toNat % 8)
  if dst.toNat < 8 then [0xD1, modrm]
  else [UInt8.ofNat (0x40 + dst.toNat / 8), 0xD1, modrm]

theorem encodeShlR32One_spec : ∀ dst : BitVec 4,
    (∃ modrm, encodeShlR32One dst = [0xD1, modrm] ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = 4 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeShlR32One dst = [rex, 0xD1, modrm] ∧ RexNoWPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 4 ∧
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

def encodeShlR16One (dst : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xE0 + dst.toNat % 8)
  if dst.toNat < 8 then [0x66, 0xD1, modrm]
  else [0x66, UInt8.ofNat (0x40 + dst.toNat / 8), 0xD1, modrm]

theorem encodeShlR16One_spec : ∀ dst : BitVec 4,
    (∃ modrm, encodeShlR16One dst = [0x66, 0xD1, modrm] ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = 4 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeShlR16One dst = [0x66, rex, 0xD1, modrm] ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 4 ∧
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
