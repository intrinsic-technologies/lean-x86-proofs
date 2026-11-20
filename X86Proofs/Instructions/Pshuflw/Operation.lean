import X86Proofs.Core.Lanes

/-!
# PSHUFLW specification

`PSHUFLW xmm1, xmm2/m128, imm8` (`F2 0F 70 /r ib`): shuffle the low words of the source by the
immediate and copy its high quadword, `DEST[15:0] ← (SRC >> (imm[1:0] * 16))[15:0]; DEST[31:16] ←
(SRC >> (imm[3:2] * 16))[15:0]; …; DEST[127:64] ← SRC[127:64]`: word `j` (`j < 4`) of the result is
word `imm[2j+1:2j]` of the source. `pshuflwSpec` is the result; lean-x86 computes it with
`Operations.SHUFL_lanes 16 128`. No flags.
-/

namespace X86Proofs

/-- For `i = 0 … 3` word `imm[2i+1 : 2i]` of `a`, then words 4–7 of `a`. -/
def pshuflwSpec (a : BitVec 128) (imm : BitVec 8) : BitVec 128 :=
  ofLanes 128 16 fun i =>
    if i < 4 then lane 16 a (imm.extractLsb' (i * 2) 2).toNat else lane 16 a i

open X86

theorem pshuflw_operation (a : BitVec 128) (imm : BitVec 8) :
    X86.Instructions.Operations.SHUFL_lanes 16 128 a imm = .ok (pshuflwSpec a imm) := by
  rw [← ofLanes_full (by decide) (pshuflwSpec a imm)]
  unfold X86.Instructions.Operations.SHUFL_lanes
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
  · have hv := (BitVec.extractLsb' (i * 2) 2 imm).isLt
    simp only [Nat.reducePow] at hv
    have hm : ((i : Int) % 4).toNat = i := by omega
    rw [ite_eq_left (by omega), ite_eq_left h4, hm]
    simp (disch := lanes_disch) only [x86_runtime, pure_bind]
    rw [show ((0 + ((BitVec.extractLsb' (i * 2) 2 imm).toNat : Int)) * 16).toNat =
      (BitVec.extractLsb' (i * 2) 2 imm).toNat * 16 by omega]
    rfl
  · rw [ite_eq_right (by omega), ite_eq_right h4]; rfl

end X86Proofs
