import X86Proofs.Core.Lanes

/-!
# PSUBSB, PSUBSW specification

`PSUBSB`/`PSUBSW xmm1, xmm2/m128` (`66 0F E8`/`E9 /r`): subtract the packed signed bytes or words
with signed saturation, `DEST[7:0] ← SaturateToSignedByte(DEST[7:0] − SRC[7:0])` and so on
(`saturateSigned`). `psubsSpec w` is the result for lanes of `w` bits (`Operations.PSUBS w 128`).
No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits: `psubsMmxSpec`.
-/

namespace X86Proofs

/-- Each `w`-bit lane of the result is the signed difference of the lanes, saturated. -/
def psubsSpec (w : Nat) (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 w fun i => saturateSigned w ((lane w a i).toInt - (lane w b i).toInt)

/-- `psubsSpec` at 64 bits, for the MMX forms. -/
def psubsMmxSpec (w : Nat) (a b : BitVec 64) : BitVec 64 :=
  ofLanes 64 w fun i => saturateSigned w ((lane w a i).toInt - (lane w b i).toInt)

open X86

theorem psubs_operation (w : Nat) (hw : w = 8 ∨ w = 16) (a b : BitVec 128) :
    X86.Instructions.Operations.PSUBS w 128 a b = .ok (psubsSpec w a b) := by
  rcases hw with rfl | rfl <;>
  · unfold X86.Instructions.Operations.PSUBS
    lanes_loop
    simp (disch := decide) only [stdSignedSaturate_eq_ok, Int.reduceToNat]
    rfl

theorem psubs_mmx_operation (w : Nat) (hw : w = 8 ∨ w = 16) (a b : BitVec 64) :
    X86.Instructions.Operations.PSUBS w 64 a b = .ok (psubsMmxSpec w a b) := by
  rcases hw with rfl | rfl <;>
  · unfold X86.Instructions.Operations.PSUBS
    lanes_loop
    simp (disch := decide) only [stdSignedSaturate_eq_ok, Int.reduceToNat]
    rfl

end X86Proofs
