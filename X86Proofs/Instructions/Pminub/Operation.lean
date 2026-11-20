import X86Proofs.Core.Lanes

/-!
# PMINUB specification

`PMINUB xmm1, xmm2/m128` (`66 0F DA /r`): the smaller of each pair of unsigned bytes,
`IF DEST[7:0] < SRC[7:0] THEN DEST[7:0] ← DEST[7:0] ELSE DEST[7:0] ← SRC[7:0]` and so on.
`pminubSpec` is lean-x86's `Operations.PMINU 8 128`. No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits: `pminubMmxSpec`.
-/

namespace X86Proofs

/-- Each byte of the result is the smaller of the bytes of `a` and `b` as unsigned numbers. -/
def pminubSpec (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 8 fun i =>
    if (lane 8 a i).toNat ≤ (lane 8 b i).toNat then lane 8 a i else lane 8 b i

/-- `pminubSpec` at 64 bits, for the MMX forms. -/
def pminubMmxSpec (a b : BitVec 64) : BitVec 64 :=
  ofLanes 64 8 fun i =>
    if (lane 8 a i).toNat ≤ (lane 8 b i).toNat then lane 8 a i else lane 8 b i

open X86

theorem pminub_operation (a b : BitVec 128) :
    X86.Instructions.Operations.PMINU 8 128 a b = .ok (pminubSpec a b) := by
  unfold X86.Instructions.Operations.PMINU
  lanes_loop
  rw [ofInt_min_toNat]
  rfl

theorem pminub_mmx_operation (a b : BitVec 64) :
    X86.Instructions.Operations.PMINU 8 64 a b = .ok (pminubMmxSpec a b) := by
  unfold X86.Instructions.Operations.PMINU
  lanes_loop
  rw [ofInt_min_toNat]
  rfl

end X86Proofs
