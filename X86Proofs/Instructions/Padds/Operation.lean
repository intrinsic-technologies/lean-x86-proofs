import X86Proofs.Core.Lanes

/-!
# PADDSB, PADDSW specification

`PADDSB`/`PADDSW xmm1, xmm2/m128` (`66 0F EC`/`ED /r`): add the packed signed bytes or words with
signed saturation, `DEST[7:0] ← SaturateToSignedByte(DEST[7:0] + SRC[7:0])` and so on: a sum
above the largest signed value of the lane gives that value, one below the smallest gives the
smallest (`saturateSigned`). `paddsSpec w` is the result for lanes of `w` bits
(`Operations.PADDS w 128`). No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits: `paddsMmxSpec`.
-/

namespace X86Proofs

/-- Each `w`-bit lane of the result is the signed sum of the lanes of `a` and `b`, saturated. -/
def paddsSpec (w : Nat) (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 w fun i => saturateSigned w ((lane w a i).toInt + (lane w b i).toInt)

/-- `paddsSpec` at 64 bits, for the MMX forms. -/
def paddsMmxSpec (w : Nat) (a b : BitVec 64) : BitVec 64 :=
  ofLanes 64 w fun i => saturateSigned w ((lane w a i).toInt + (lane w b i).toInt)

open X86

theorem padds_operation (w : Nat) (hw : w = 8 ∨ w = 16) (a b : BitVec 128) :
    X86.Instructions.Operations.PADDS w 128 a b = .ok (paddsSpec w a b) := by
  rcases hw with rfl | rfl <;>
  · unfold X86.Instructions.Operations.PADDS
    lanes_loop
    simp (disch := decide) only [stdSignedSaturate_eq_ok, Int.reduceToNat]
    rfl

theorem padds_mmx_operation (w : Nat) (hw : w = 8 ∨ w = 16) (a b : BitVec 64) :
    X86.Instructions.Operations.PADDS w 64 a b = .ok (paddsMmxSpec w a b) := by
  rcases hw with rfl | rfl <;>
  · unfold X86.Instructions.Operations.PADDS
    lanes_loop
    simp (disch := decide) only [stdSignedSaturate_eq_ok, Int.reduceToNat]
    rfl

end X86Proofs
