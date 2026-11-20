import X86Proofs.Core.Lanes

/-!
# PSUBUSB, PSUBUSW specification

`PSUBUSB`/`PSUBUSW xmm1, xmm2/m128` (`66 0F D8`/`D9 /r`): subtract the packed unsigned bytes or
words with unsigned saturation, `DEST[7:0] ← SaturateToUnsignedByte(DEST[7:0] − SRC[7:0])` and so
on: a negative difference gives 0 (`saturateUnsigned` of the difference as an integer).
`psubusSpec w` is the result for lanes of `w` bits (`Operations.PSUBUS w 128`). No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits: `psubusMmxSpec`.
-/

namespace X86Proofs

/-- Each `w`-bit lane of the result is the difference of the lanes as unsigned numbers, saturated
(0 if negative). -/
def psubusSpec (w : Nat) (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 w fun i => saturateUnsigned w ((lane w a i).toNat - (lane w b i).toNat : Int)

/-- `psubusSpec` at 64 bits, for the MMX forms. -/
def psubusMmxSpec (w : Nat) (a b : BitVec 64) : BitVec 64 :=
  ofLanes 64 w fun i => saturateUnsigned w ((lane w a i).toNat - (lane w b i).toNat : Int)

open X86

theorem psubus_operation (w : Nat) (hw : w = 8 ∨ w = 16) (a b : BitVec 128) :
    X86.Instructions.Operations.PSUBUS w 128 a b = .ok (psubusSpec w a b) := by
  rcases hw with rfl | rfl <;>
  · unfold X86.Instructions.Operations.PSUBUS
    lanes_loop
    simp (disch := decide) only [stdUnsignedSaturate_eq_ok, Int.reduceToNat]
    rfl

theorem psubus_mmx_operation (w : Nat) (hw : w = 8 ∨ w = 16) (a b : BitVec 64) :
    X86.Instructions.Operations.PSUBUS w 64 a b = .ok (psubusMmxSpec w a b) := by
  rcases hw with rfl | rfl <;>
  · unfold X86.Instructions.Operations.PSUBUS
    lanes_loop
    simp (disch := decide) only [stdUnsignedSaturate_eq_ok, Int.reduceToNat]
    rfl

end X86Proofs
