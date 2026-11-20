import X86Proofs.Core.Lanes

/-!
# PMAXUB specification

`PMAXUB xmm1, xmm2/m128` (`66 0F DE /r`): the larger of each pair of unsigned bytes,
`IF DEST[7:0] > SRC[7:0] THEN DEST[7:0] ← DEST[7:0] ELSE DEST[7:0] ← SRC[7:0]` and so on.
`pmaxubSpec` is lean-x86's `Operations.PMAXU 8 128`. No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits: `pmaxubMmxSpec`.
-/

namespace X86Proofs

/-- Each byte of the result is the larger of the bytes of `a` and `b` as unsigned numbers. -/
def pmaxubSpec (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 8 fun i =>
    if (lane 8 a i).toNat ≥ (lane 8 b i).toNat then lane 8 a i else lane 8 b i

/-- `pmaxubSpec` at 64 bits, for the MMX forms. -/
def pmaxubMmxSpec (a b : BitVec 64) : BitVec 64 :=
  ofLanes 64 8 fun i =>
    if (lane 8 a i).toNat ≥ (lane 8 b i).toNat then lane 8 a i else lane 8 b i

open X86

theorem pmaxub_operation (a b : BitVec 128) :
    X86.Instructions.Operations.PMAXU 8 128 a b = .ok (pmaxubSpec a b) := by
  unfold X86.Instructions.Operations.PMAXU
  lanes_loop
  rw [ofInt_max_toNat]
  rfl

theorem pmaxub_mmx_operation (a b : BitVec 64) :
    X86.Instructions.Operations.PMAXU 8 64 a b = .ok (pmaxubMmxSpec a b) := by
  unfold X86.Instructions.Operations.PMAXU
  lanes_loop
  rw [ofInt_max_toNat]
  rfl

end X86Proofs
