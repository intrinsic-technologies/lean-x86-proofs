import X86Proofs.Step.Prefix
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeXchgR64Rax (r : BitVec 4) : List UInt8 :=
  [UInt8.ofNat (0x48 + r.toNat / 8), UInt8.ofNat (0x90 + r.toNat % 8)]

theorem encodeXchgR64Rax_spec : ∀ r : BitVec 4, r ≠ 0 →
    ∃ rex op, encodeXchgR64Rax r = [rex, op] ∧ RexWPrefix rex.toBitVec ∧
      op ∈ [0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97] ∧ (op = 0x90 → rexB rex.toBitVec = 1) ∧
      gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3) = r.setWidth 5 := by
  intro r hr
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert r
  decide

def encodeXchgR32Eax (r : BitVec 4) : List UInt8 :=
  if r.toNat < 8 then [UInt8.ofNat (0x90 + r.toNat)]
  else [0x41, UInt8.ofNat (0x90 + r.toNat % 8)]

theorem encodeXchgR32Eax_spec : ∀ r : BitVec 4, r ≠ 0 →
    (∃ op, encodeXchgR32Eax r = [op] ∧ op ∈ [0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97] ∧
      gprNumber 0 0 (op.toBitVec.extractLsb' 0 3) = r.setWidth 5) ∨
    (∃ rex op, encodeXchgR32Eax r = [rex, op] ∧ RexNoWPrefix rex.toBitVec ∧
      op ∈ [0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97] ∧ (op = 0x90 → rexB rex.toBitVec = 1) ∧
      gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3) = r.setWidth 5) := by
  intro r hr
  by_cases hlow : r.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert r
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert r
    decide

def encodeXchgR16Ax (r : BitVec 4) : List UInt8 :=
  if r.toNat < 8 then [0x66, UInt8.ofNat (0x90 + r.toNat)]
  else [0x66, 0x41, UInt8.ofNat (0x90 + r.toNat % 8)]

theorem encodeXchgR16Ax_spec : ∀ r : BitVec 4, r ≠ 0 →
    (∃ op, encodeXchgR16Ax r = [0x66, op] ∧ op ∈ [0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97] ∧
      gprNumber 0 0 (op.toBitVec.extractLsb' 0 3) = r.setWidth 5) ∨
    (∃ rex op, encodeXchgR16Ax r = [0x66, rex, op] ∧ RexNoWPrefix rex.toBitVec ∧
      op ∈ [0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97] ∧ (op = 0x90 → rexB rex.toBitVec = 1) ∧
      gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3) = r.setWidth 5) := by
  intro r hr
  by_cases hlow : r.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert r
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert r
    decide

end X86Proofs
