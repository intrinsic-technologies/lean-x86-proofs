import X86Proofs.Core.Lanes

/-!
# PSHUFHW specification

`PSHUFHW xmm1, xmm2/m128, imm8` (`F3 0F 70 /r ib`): copy the low quadword of the source and
shuffle its high words by the immediate, `DEST[63:0] ← SRC[63:0]; DEST[79:64] ← (SRC >>
(imm[1:0] * 16))[79:64]; DEST[95:80] ← (SRC >> (imm[3:2] * 16))[79:64]; …`: word `4 + j` of the
result is word `4 + imm[2j+1:2j]` of the source. `pshufhwSpec` is the result; lean-x86 computes
it with `Operations.SHUFH_lanes 16 128`. No flags.
-/

namespace X86Proofs

/-- Words 0–3 of `a`, then for `i = 4 … 7` word `4 + imm[2(i-4)+1 : 2(i-4)]` of `a`. -/
def pshufhwSpec (a : BitVec 128) (imm : BitVec 8) : BitVec 128 :=
  ofLanes 128 16 fun i =>
    if i < 4 then lane 16 a i else lane 16 a (4 + (imm.extractLsb' ((i - 4) * 2) 2).toNat)

open X86

theorem pshufhw_operation (a : BitVec 128) (imm : BitVec 8) :
    X86.Instructions.Operations.SHUFH_lanes 16 128 a imm = .ok (pshufhwSpec a imm) := by
  rw [← ofLanes_full (by decide) (pshufhwSpec a imm)]
  unfold X86.Instructions.Operations.SHUFH_lanes
  simp only [x86_runtime, pure_bind, bind_pure, Int.reduceDiv]
  refine forIn_ofLanes _ _ _ (by rfl) _ _ (fun l hl r => ?_)
  obtain rfl : l = 0 := by omega
  simp (disch := lanes_disch) only [x86_runtime, pure_bind, Nat.zero_mul, Int.zero_mul,
    Int.cast_ofNat_Int, BitVec.extractLsb'_eq_self, setSlice_full]
  refine forIn_ofLanes_yield _ _ _ (by rfl) _ _ (fun i hi r => ?_)
  simp (disch := lanes_disch) only [x86_runtime, pure_bind, Int.toNat_mul,
    Int.toNat_natCast, Int.reduceToNat]
  have htd : (i : Int).tdiv 8 = 0 := by rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]; omega
  rw [htd]
  by_cases h4 : i < 4
  · rw [ite_eq_right (by omega), ite_eq_left h4]; rfl
  · have hv := (BitVec.extractLsb' ((i - 4) * 2) 2 imm).isLt
    simp only [Nat.reducePow] at hv
    have hm : ((i : Int) % 4).toNat = i - 4 := by omega
    rw [ite_eq_left (by omega), ite_eq_right h4, hm]
    simp (disch := lanes_disch) only [x86_runtime, pure_bind]
    rw [show ((4 + ((BitVec.extractLsb' ((i - 4) * 2) 2 imm).toNat : Int)) * 16).toNat =
      (4 + (BitVec.extractLsb' ((i - 4) * 2) 2 imm).toNat) * 16 by omega]
    rfl

end X86Proofs
