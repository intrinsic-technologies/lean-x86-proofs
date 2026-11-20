import X86Proofs.Core.Lanes

/-!
# PMULLW specification

`PMULLW xmm1, xmm2/m128` (`66 0F D5 /r`): multiply the packed signed words and keep the low word
of each 32-bit product, `TEMP0[31:0] ← DEST[15:0] ∗ SRC[15:0]; DEST[15:0] ← TEMP0[15:0]` and so
on (the low half of a product is the same signed or unsigned: the wrapping 16-bit product).
`pmullwSpec` is lean-x86's `Operations.PMULL 16 128`. No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits: `pmullwMmxSpec`.
-/

namespace X86Proofs

/-- Each word of the result is the low word of the product of the words of `a` and `b`. -/
def pmullwSpec (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 16 fun i => lane 16 a i * lane 16 b i

/-- `pmullwSpec` at 64 bits, for the MMX forms. -/
def pmullwMmxSpec (a b : BitVec 64) : BitVec 64 :=
  ofLanes 64 16 fun i => lane 16 a i * lane 16 b i

open X86

theorem pmullw_operation (a b : BitVec 128) :
    X86.Instructions.Operations.PMULL 16 128 a b = .ok (pmullwSpec a b) := by
  unfold X86.Instructions.Operations.PMULL
  lanes_loop

theorem pmullw_mmx_operation (a b : BitVec 64) :
    X86.Instructions.Operations.PMULL 16 64 a b = .ok (pmullwMmxSpec a b) := by
  unfold X86.Instructions.Operations.PMULL
  lanes_loop

end X86Proofs
