import X86Proofs.Core.Lanes
import X86Proofs.Core.Run

/-!
# SHUFPS, SHUFPD specification

`SHUFPS xmm1, xmm2/m128, imm8` (`0F C6 /r ib`): the low two doublewords of the result are
doublewords of the destination and the high two of the source, each selected by two bits of the
immediate, `DEST[31:0] ← Select4(SRC1, imm8[1:0]); DEST[63:32] ← Select4(SRC1, imm8[3:2]);
DEST[95:64] ← Select4(SRC2, imm8[5:4]); DEST[127:96] ← Select4(SRC2, imm8[7:6])`.
`SHUFPD xmm1, xmm2/m128, imm8` (`66 0F C6 /r ib`): `DEST[63:0] ← SRC1[63:0]` or `SRC1[127:64]` as
`imm8[0]` is 0 or 1, `DEST[127:64] ← SRC2[63:0]` or `SRC2[127:64]` as `imm8[1]` is. `shufpsSpec`,
`shufpdSpec` are the results; lean-x86 computes them with `Operations.SHUFP_lanes 32 128` and
`SHUFP_lanes 64 128`, `PartialResult`s (`Std.Integer.Log2`). No flags.
-/

namespace X86Proofs

/-- Doubleword `i` of the result is doubleword `imm[2i+1 : 2i]` of `a` for `i < 2`, of `b`
otherwise. -/
def shufpsSpec (a b : BitVec 128) (imm : BitVec 8) : BitVec 128 :=
  ofLanes 128 32 fun i =>
    if i < 2 then lane 32 a (imm.extractLsb' (i * 2) 2).toNat
    else lane 32 b (imm.extractLsb' (i * 2) 2).toNat

/-- Quadword 0 of the result is quadword `imm[0]` of `a`, quadword 1 is quadword `imm[1]` of
`b`. -/
def shufpdSpec (a b : BitVec 128) (imm : BitVec 8) : BitVec 128 :=
  ofLanes 128 64 fun i =>
    if i < 1 then lane 64 a (imm.extractLsb' i 1).toNat else lane 64 b (imm.extractLsb' i 1).toNat

open X86

theorem shufps_operation (a b : BitVec 128) (imm : BitVec 8) :
    X86.Instructions.Operations.SHUFP_lanes 32 128 a b imm =
      (pure (shufpsSpec a b imm) : X86.Runtime.PartialResult Empty (BitVec 128)) := by
  rw [← ofLanes_full (by decide) (shufpsSpec a b imm)]
  unfold X86.Instructions.Operations.SHUFP_lanes
  simp only [x86_runtime, pure_bind, bind_pure, Int.reduceDiv, stdLog2_four]
  refine forIn_ofLanesM _ _ _ (by rfl) _ _ (fun l hl r => ?_)
  obtain rfl : l = 0 := by omega
  simp (disch := lanes_disch) only [x86_runtime, pure_bind, Nat.zero_mul, Int.zero_mul,
    Int.cast_ofNat_Int, BitVec.extractLsb'_eq_self, setSlice_full]
  refine forIn_ofLanes_yieldM _ _ _ (by rfl) _ _ (fun i hi r => ?_)
  simp (disch := lanes_disch) only [x86_runtime, pure_bind, Int.toNat_mul,
    Int.toNat_natCast, Int.reduceToNat, Int.add_zero]
  have hm : ((i : Int) % 4).toNat = i := by omega
  rw [hm, Int.pow_zero, Int.ediv_one]
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  all_goals rfl

theorem shufpd_operation (a b : BitVec 128) (imm : BitVec 8) :
    X86.Instructions.Operations.SHUFP_lanes 64 128 a b imm =
      (pure (shufpdSpec a b imm) : X86.Runtime.PartialResult Empty (BitVec 128)) := by
  rw [← ofLanes_full (by decide) (shufpdSpec a b imm)]
  unfold X86.Instructions.Operations.SHUFP_lanes
  simp only [x86_runtime, pure_bind, bind_pure, Int.reduceDiv, stdLog2_two]
  refine forIn_ofLanesM _ _ _ (by rfl) _ _ (fun l hl r => ?_)
  obtain rfl : l = 0 := by omega
  simp (disch := lanes_disch) only [x86_runtime, pure_bind, Nat.zero_mul, Int.zero_mul,
    Int.cast_ofNat_Int, BitVec.extractLsb'_eq_self, setSlice_full]
  refine forIn_ofLanes_yieldM _ _ _ (by rfl) _ _ (fun i hi r => ?_)
  simp (disch := lanes_disch) only [x86_runtime, pure_bind, Int.toNat_mul,
    Int.toNat_natCast, Int.reduceToNat, Int.add_zero]
  have hm : ((i : Int) % 8).toNat = i := by omega
  rw [hm, Int.pow_zero, Int.ediv_one]
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  all_goals rfl

end X86Proofs
