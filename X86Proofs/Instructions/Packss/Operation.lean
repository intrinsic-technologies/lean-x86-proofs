import X86Proofs.Core.Lanes

/-!
# PACKSSWB, PACKSSDW specification

`PACKSSWB`/`PACKSSDW xmm1, xmm2/m128` (`66 0F 63`/`6B /r`): narrow the signed words (doublewords)
of the destination and then of the source to bytes (words) with signed saturation: `DEST[7:0] ←
SaturateSignedWordToSignedByte(DEST[15:0]); …; DEST[63:56] ← Saturate…(DEST[127:112]);
DEST[71:64] ← Saturate…(SRC[15:0]); …`. lean-x86 (`Operations.PACKSS_lanes`) reads the lanes of
the 256-bit concatenation `SRC:DEST` (`b ++ a`). `packssSpec w` is the result for lanes of `w`
bits (from lanes of `2 w` bits). No flags.

The MMX forms (`NP 0F 63`/`6B mm, mm/m64`) pack two 64-bit operands into one, lean-x86's
`Operations.PACKSS`: `packssMmxSpec`.
-/

namespace X86Proofs

/-- Lane `i` of the result is lane `i` of `b ++ a` (twice as wide) saturated to a signed `w`-bit
value: the lanes of `a` first, then those of `b`. -/
def packssSpec (w : Nat) (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 w fun i => saturateSigned w (lane (2 * w) (b ++ a) i).toInt

/-- `packssSpec` at 64 bits, for the MMX forms (`PACKSSWB`/`PACKSSDW mm, mm/m64`): lane `i` of the
result is lane `i` of `b ++ a` saturated. -/
def packssMmxSpec (w : Nat) (a b : BitVec 64) : BitVec 64 :=
  ofLanes 64 w fun i => saturateSigned w (lane (2 * w) (b ++ a) i).toInt

open X86

theorem packss_operation (w : Nat) (hw : w = 8 ∨ w = 16) (a b : BitVec 128) :
    X86.Instructions.Operations.PACKSS_lanes (2 * w) 128 w 128 a b = .ok (packssSpec w a b) := by
  rw [← ofLanes_full (by decide) (packssSpec w a b)]
  rcases hw with rfl | rfl <;>
  · unfold X86.Instructions.Operations.PACKSS_lanes
    simp only [x86_runtime, pure_bind, bind_pure, Int.reduceDiv]
    refine forIn_ofLanes _ _ _ (by rfl) _ _ (fun l hl r => ?_)
    obtain rfl : l = 0 := by omega
    simp (disch := lanes_disch) only [x86_runtime, pure_bind, Nat.zero_mul, Int.zero_mul,
      Int.cast_ofNat_Int, BitVec.extractLsb'_eq_self, setSlice_full, ofNat_shiftLeft_add_eq_append]
    refine forIn_ofLanes_yield _ _ _ (by rfl) _ _ (fun i hi r => ?_)
    simp (disch := lanes_disch) only [x86_runtime, pure_bind, natCast_mul_toNat, Int.reduceToNat]
    simp (disch := decide) only [stdSignedSaturate_eq_ok, Int.reduceToNat]
    rfl

theorem packss_mmx_operation (w : Nat) (hw : w = 8 ∨ w = 16) (a b : BitVec 64) :
    X86.Instructions.Operations.PACKSS (2 * w) 64 w 64 a b = .ok (packssMmxSpec w a b) := by
  have hcat : BitVec.ofNat 128 (b.toNat <<< 64 + a.toNat) = b ++ a :=
    ofNat_shiftLeft_add_eq_append_any b a
  rcases hw with rfl | rfl <;>
  · unfold X86.Instructions.Operations.PACKSS
    simp only [x86_runtime, pure_bind, bind_pure, Int.reduceDiv, hcat]
    refine forIn_ofLanes _ _ _ (by rfl) _ _ (fun i hi r => ?_)
    simp (disch := lanes_disch) only [x86_runtime, pure_bind, natCast_mul_toNat, Int.reduceToNat]
    simp (disch := decide) only [stdSignedSaturate_eq_ok, Int.reduceToNat]
    rfl

end X86Proofs
