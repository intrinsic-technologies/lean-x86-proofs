import X86Proofs.Core.Lanes

/-!
# PACKUSWB specification

`PACKUSWB xmm1, xmm2/m128` (`66 0F 67 /r`): narrow the signed words of the destination and then
of the source to unsigned bytes with unsigned saturation: `DEST[7:0] ←
SaturateSignedWordToUnsignedByte(DEST[15:0]); …; DEST[127:120] ← Saturate…(SRC[127:112])`: a
negative word gives 0, one above 255 gives 255. lean-x86 (`Operations.PACKUS_lanes 16 128 8 128`)
reads the words of the 256-bit concatenation `SRC:DEST` (`b ++ a`). No flags.

The MMX form (`NP 0F 67 mm, mm/m64`) packs two 64-bit operands into one, lean-x86's
`Operations.PACKUS`: `packuswbMmxSpec`.
-/

namespace X86Proofs

/-- Byte `i` of the result is word `i` of `b ++ a`, a signed integer, saturated to an unsigned
byte: the words of `a` first, then those of `b`. -/
def packuswbSpec (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 8 fun i => saturateUnsigned 8 (lane 16 (b ++ a) i).toInt

/-- `packuswbSpec` at 64 bits, for the MMX form (`PACKUSWB mm, mm/m64`). -/
def packuswbMmxSpec (a b : BitVec 64) : BitVec 64 :=
  ofLanes 64 8 fun i => saturateUnsigned 8 (lane 16 (b ++ a) i).toInt

open X86

theorem packuswb_operation (a b : BitVec 128) :
    X86.Instructions.Operations.PACKUS_lanes 16 128 8 128 a b = .ok (packuswbSpec a b) := by
  rw [← ofLanes_full (by decide) (packuswbSpec a b)]
  unfold X86.Instructions.Operations.PACKUS_lanes
  simp only [x86_runtime, pure_bind, bind_pure, Int.reduceDiv]
  refine forIn_ofLanes _ _ _ (by rfl) _ _ (fun l hl r => ?_)
  obtain rfl : l = 0 := by omega
  simp (disch := lanes_disch) only [x86_runtime, pure_bind, Nat.zero_mul, Int.zero_mul,
    Int.cast_ofNat_Int, BitVec.extractLsb'_eq_self, setSlice_full, ofNat_shiftLeft_add_eq_append]
  refine forIn_ofLanes_yield _ _ _ (by rfl) _ _ (fun i hi r => ?_)
  simp (disch := lanes_disch) only [x86_runtime, pure_bind, natCast_mul_toNat, Int.reduceToNat]
  simp (disch := decide) only [stdUnsignedSaturate_eq_ok, Int.reduceToNat]
  rfl

theorem packuswb_mmx_operation (a b : BitVec 64) :
    X86.Instructions.Operations.PACKUS 16 64 8 64 a b = .ok (packuswbMmxSpec a b) := by
  have hcat : BitVec.ofNat 128 (b.toNat <<< 64 + a.toNat) = b ++ a :=
    ofNat_shiftLeft_add_eq_append_any b a
  unfold X86.Instructions.Operations.PACKUS
  simp only [x86_runtime, pure_bind, bind_pure, Int.reduceDiv, hcat]
  refine forIn_ofLanes _ _ _ (by rfl) _ _ (fun i hi r => ?_)
  simp (disch := lanes_disch) only [x86_runtime, pure_bind, natCast_mul_toNat, Int.reduceToNat]
  simp (disch := decide) only [stdUnsignedSaturate_eq_ok, Int.reduceToNat]
  rfl

end X86Proofs
