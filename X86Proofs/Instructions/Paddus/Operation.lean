import X86Proofs.Core.Lanes

/-!
# PADDUSB, PADDUSW specification

`PADDUSB`/`PADDUSW xmm1, xmm2/m128` (`66 0F DC`/`DD /r`): add the packed unsigned bytes or words
with unsigned saturation, `DEST[7:0] ← SaturateToUnsignedByte(DEST[7:0] + SRC[7:0])` and so on: a
sum above the largest value of the lane gives that value (`saturateUnsigned`). `paddusSpec w` is
the result for lanes of `w` bits (`Operations.PADDUS w 128`). No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits: `paddusMmxSpec`.
-/

namespace X86Proofs

/-- Each `w`-bit lane of the result is the unsigned sum of the lanes of `a` and `b`, saturated. -/
def paddusSpec (w : Nat) (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 w fun i => saturateUnsigned w ((lane w a i).toNat + (lane w b i).toNat)

/-- `paddusSpec` at 64 bits, for the MMX forms. -/
def paddusMmxSpec (w : Nat) (a b : BitVec 64) : BitVec 64 :=
  ofLanes 64 w fun i => saturateUnsigned w ((lane w a i).toNat + (lane w b i).toNat)

open X86

theorem paddus_operation (w : Nat) (hw : w = 8 ∨ w = 16) (a b : BitVec 128) :
    X86.Instructions.Operations.PADDUS w 128 a b = .ok (paddusSpec w a b) := by
  rcases hw with rfl | rfl <;>
  · unfold X86.Instructions.Operations.PADDUS
    lanes_loop
    simp (disch := decide) only [stdUnsignedSaturate_eq_ok, Int.reduceToNat]
    rfl

theorem paddus_mmx_operation (w : Nat) (hw : w = 8 ∨ w = 16) (a b : BitVec 64) :
    X86.Instructions.Operations.PADDUS w 64 a b = .ok (paddusMmxSpec w a b) := by
  rcases hw with rfl | rfl <;>
  · unfold X86.Instructions.Operations.PADDUS
    lanes_loop
    simp (disch := decide) only [stdUnsignedSaturate_eq_ok, Int.reduceToNat]
    rfl

end X86Proofs
