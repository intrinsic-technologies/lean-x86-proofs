import X86Proofs.Core.Lanes
import X86Proofs.Core.Run

/-!
# PSHUFW specification

`PSHUFW mm1, mm2/m64, imm8` (`NP 0F 70 /r ib`): word `i` of the destination is the source word
that bits `2i + 1 : 2i` of the immediate select, `DEST[15:0] ← (SRC >> (ORDER[1:0] * 16))[15:0]`
and so on for the four words. `pshufwSpec` is the result; lean-x86 computes it with
`Operations.SHUF 16 64`, which uses `Std.Integer.Log2` (a `partial_fixpoint` loop), so the operation
is a `PartialResult`. No flags.
-/

namespace X86Proofs

/-- Word `i` of the result is word `imm[2i+1 : 2i]` of `a`. -/
def pshufwSpec (a : BitVec 64) (imm : BitVec 8) : BitVec 64 :=
  ofLanes 64 16 fun i => lane 16 a (imm.extractLsb' (i * 2) 2).toNat

open X86

theorem pshufw_operation (a : BitVec 64) (imm : BitVec 8) :
    X86.Instructions.Operations.SHUF 16 64 a imm =
      (pure (pshufwSpec a imm) : X86.Runtime.PartialResult Empty (BitVec 64)) := by
  unfold X86.Instructions.Operations.SHUF
  simp only [x86_runtime, pure_bind, bind_pure, Int.reduceDiv, stdLog2_four]
  refine forIn_ofLanesM _ _ _ (by rfl) _ _ (fun i hi r => ?_)
  simp (disch := lanes_disch) only [x86_runtime, pure_bind, Int.toNat_mul,
    Int.toNat_natCast, Int.reduceToNat]
  have htd : (i : Int).tdiv 4 = 0 := by rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]; omega
  have hm : ((i : Int) % 4).toNat = i := by omega
  have hv := (BitVec.extractLsb' (i * 2) 2 imm).isLt
  simp only [Nat.reducePow] at hv
  rw [htd, hm]
  simp (disch := lanes_disch) only [x86_runtime, pure_bind, Int.mul_zero, Int.zero_add]
  rw [show (((BitVec.extractLsb' (i * 2) 2 imm).toNat : Int) * 16).toNat =
    (BitVec.extractLsb' (i * 2) 2 imm).toNat * 16 by omega]
  rfl

end X86Proofs
