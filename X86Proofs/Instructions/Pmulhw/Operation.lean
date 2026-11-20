import X86Proofs.Core.Lanes

/-!
# PMULHW specification

`PMULHW xmm1, xmm2/m128` (`66 0F E5 /r`): multiply the packed signed words and keep the high word
of each 32-bit product, `TEMP0[31:0] ← DEST[15:0] ∗ SRC[15:0]; DEST[15:0] ← TEMP0[31:16]` and so
on (bits 16–31 of the signed product: the product divided by `2 ^ 16`, rounding down).
`pmulhwSpec` is lean-x86's `Operations.PMULH 16 128`. No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits: `pmulhwMmxSpec`.
-/

namespace X86Proofs

/-- Each word of the result is bits 16–31 of the signed product of the words of `a` and `b`. -/
def pmulhwSpec (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 16 fun i =>
    BitVec.ofInt 16 ((lane 16 a i).toInt * (lane 16 b i).toInt / 2 ^ 16)

/-- `pmulhwSpec` at 64 bits, for the MMX forms. -/
def pmulhwMmxSpec (a b : BitVec 64) : BitVec 64 :=
  ofLanes 64 16 fun i =>
    BitVec.ofInt 16 ((lane 16 a i).toInt * (lane 16 b i).toInt / 2 ^ 16)

open X86

theorem pmulhw_operation (a b : BitVec 128) :
    X86.Instructions.Operations.PMULH 16 128 a b = .ok (pmulhwSpec a b) := by
  unfold X86.Instructions.Operations.PMULH
  lanes_loop

theorem pmulhw_mmx_operation (a b : BitVec 64) :
    X86.Instructions.Operations.PMULH 16 64 a b = .ok (pmulhwMmxSpec a b) := by
  unfold X86.Instructions.Operations.PMULH
  lanes_loop

end X86Proofs
