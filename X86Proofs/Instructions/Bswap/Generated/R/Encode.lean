import X86Proofs.Step.Prefix
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeBswapR64 (r : BitVec 4) : List UInt8 :=
  [UInt8.ofNat (0x48 + r.toNat / 8), 0x0F, UInt8.ofNat (0xC8 + r.toNat % 8)]

theorem encodeBswapR64_spec : ∀ r : BitVec 4,
    ∃ rex op, encodeBswapR64 r = [rex, 0x0F, op] ∧ RexWPrefix rex.toBitVec ∧
      op ∈ [0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF] ∧
      gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3) = r.setWidth 5 := by
  intro r
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert r
  decide

def encodeBswapR32 (r : BitVec 4) : List UInt8 :=
  if r.toNat < 8 then [0x0F, UInt8.ofNat (0xC8 + r.toNat)]
  else [0x41, 0x0F, UInt8.ofNat (0xC8 + r.toNat % 8)]

theorem encodeBswapR32_spec : ∀ r : BitVec 4,
    (∃ op, encodeBswapR32 r = [0x0F, op] ∧
      op ∈ [0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF] ∧
      gprNumber 0 0 (op.toBitVec.extractLsb' 0 3) = r.setWidth 5) ∨
    (∃ rex op, encodeBswapR32 r = [rex, 0x0F, op] ∧ RexNoWPrefix rex.toBitVec ∧
      op ∈ [0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF] ∧
      gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3) = r.setWidth 5) := by
  intro r
  by_cases hlow : r.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert r
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert r
    decide

end X86Proofs
