import X86Proofs.Core.Lanes

/-!
# PMINSW specification

`PMINSW xmm1, xmm2/m128` (`66 0F EA /r`): the smaller of each pair of signed words,
`IF DEST[15:0] < SRC[15:0] THEN DEST[15:0] ← DEST[15:0] ELSE DEST[15:0] ← SRC[15:0]` and so on.
`pminswSpec` is lean-x86's `Operations.PMINS 16 128`. No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits: `pminswMmxSpec`.
-/

namespace X86Proofs

/-- Each word of the result is the smaller of the words of `a` and `b` as signed integers. -/
def pminswSpec (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 16 fun i =>
    if (lane 16 a i).toInt ≤ (lane 16 b i).toInt then lane 16 a i else lane 16 b i

/-- `pminswSpec` at 64 bits, for the MMX forms. -/
def pminswMmxSpec (a b : BitVec 64) : BitVec 64 :=
  ofLanes 64 16 fun i =>
    if (lane 16 a i).toInt ≤ (lane 16 b i).toInt then lane 16 a i else lane 16 b i

open X86

theorem pminsw_operation (a b : BitVec 128) :
    X86.Instructions.Operations.PMINS 16 128 a b = .ok (pminswSpec a b) := by
  unfold X86.Instructions.Operations.PMINS
  lanes_loop
  rw [ofInt_min_toInt]
  rfl

theorem pminsw_mmx_operation (a b : BitVec 64) :
    X86.Instructions.Operations.PMINS 16 64 a b = .ok (pminswMmxSpec a b) := by
  unfold X86.Instructions.Operations.PMINS
  lanes_loop
  rw [ofInt_min_toInt]
  rfl

end X86Proofs
