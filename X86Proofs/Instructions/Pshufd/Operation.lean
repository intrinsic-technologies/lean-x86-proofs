import X86Proofs.Core.Lanes
import X86Proofs.Core.Run

/-!
# PSHUFD specification

`PSHUFD xmm1, xmm2/m128, imm8` (`66 0F 70 /r ib`): each doubleword of the result is the source
doubleword the immediate selects for it, `DEST[31:0] ← (SRC >> (ORDER[1:0] * 32))[31:0];
DEST[63:32] ← (SRC >> (ORDER[3:2] * 32))[31:0]; …`. `pshufdSpec` is the result; lean-x86
computes it with `Operations.SHUF_lanes 32 128`, a `PartialResult` (its index width comes from
`Std.Integer.Log2`, which may diverge in general). No flags.
-/

namespace X86Proofs

/-- Doubleword `i` of the result is doubleword `imm[2i+1 : 2i]` of `a`. -/
def pshufdSpec (a : BitVec 128) (imm : BitVec 8) : BitVec 128 :=
  ofLanes 128 32 fun i => lane 32 a (imm.extractLsb' (i * 2) 2).toNat

open X86

theorem pshufd_operation (a : BitVec 128) (imm : BitVec 8) :
    X86.Instructions.Operations.SHUF_lanes 32 128 a imm =
      (pure (pshufdSpec a imm) : X86.Runtime.PartialResult Empty (BitVec 128)) := by
  rw [← ofLanes_full (by decide) (pshufdSpec a imm)]
  unfold X86.Instructions.Operations.SHUF_lanes
  simp only [x86_runtime, pure_bind, bind_pure, Int.reduceDiv, stdLog2_four]
  refine forIn_ofLanesM _ _ _ (by rfl) _ _ (fun l hl r => ?_)
  obtain rfl : l = 0 := by omega
  simp (disch := lanes_disch) only [x86_runtime, pure_bind, Nat.zero_mul, Int.zero_mul,
    Int.cast_ofNat_Int, BitVec.extractLsb'_eq_self, setSlice_full]
  refine forIn_ofLanes_yieldM _ _ _ (by rfl) _ _ (fun i hi r => ?_)
  simp (disch := lanes_disch) only [x86_runtime, pure_bind, Int.toNat_mul,
    Int.toNat_natCast, Int.reduceToNat]
  have htd : (i : Int).tdiv 4 = 0 := by rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]; omega
  have hm : ((i : Int) % 4).toNat = i := by omega
  have hv := (BitVec.extractLsb' (i * 2) 2 imm).isLt
  simp only [Nat.reducePow] at hv
  rw [htd, hm]
  simp (disch := lanes_disch) only [x86_runtime, pure_bind, Int.mul_zero, Int.zero_add]
  rw [show (((BitVec.extractLsb' (i * 2) 2 imm).toNat : Int) * 32).toNat =
    (BitVec.extractLsb' (i * 2) 2 imm).toNat * 32 by omega]
  rfl

end X86Proofs
