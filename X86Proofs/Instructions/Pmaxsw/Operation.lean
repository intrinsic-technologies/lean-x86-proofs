import X86Proofs.Core.Lanes

/-!
# PMAXSW specification

`PMAXSW xmm1, xmm2/m128` (`66 0F EE /r`): the larger of each pair of signed words,
`IF DEST[15:0] > SRC[15:0] THEN DEST[15:0] ← DEST[15:0] ELSE DEST[15:0] ← SRC[15:0]` and so on.
`pmaxswSpec` is lean-x86's `Operations.PMAXS 16 128`. No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits: `pmaxswMmxSpec`.
-/

namespace X86Proofs

/-- Each word of the result is the larger of the words of `a` and `b` as signed integers. -/
def pmaxswSpec (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 16 fun i =>
    if (lane 16 a i).toInt ≥ (lane 16 b i).toInt then lane 16 a i else lane 16 b i

/-- `pmaxswSpec` at 64 bits, for the MMX forms. -/
def pmaxswMmxSpec (a b : BitVec 64) : BitVec 64 :=
  ofLanes 64 16 fun i =>
    if (lane 16 a i).toInt ≥ (lane 16 b i).toInt then lane 16 a i else lane 16 b i

open X86

theorem pmaxsw_operation (a b : BitVec 128) :
    X86.Instructions.Operations.PMAXS 16 128 a b = .ok (pmaxswSpec a b) := by
  unfold X86.Instructions.Operations.PMAXS
  lanes_loop
  rw [ofInt_max_toInt]
  rfl

theorem pmaxsw_mmx_operation (a b : BitVec 64) :
    X86.Instructions.Operations.PMAXS 16 64 a b = .ok (pmaxswMmxSpec a b) := by
  unfold X86.Instructions.Operations.PMAXS
  lanes_loop
  rw [ofInt_max_toInt]
  rfl

end X86Proofs
