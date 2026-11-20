import X86Proofs.Core.Lanes

/-!
# PMULUDQ specification

`PMULUDQ xmm1, xmm2/m128` (`66 0F F4 /r`): multiply the unsigned doublewords 0 and 2 (the low
doubleword of each quadword) into full 64-bit products, `DEST[63:0] ← DEST[31:0] ∗ SRC[31:0];
DEST[127:64] ← DEST[95:64] ∗ SRC[95:64]`. `pmuludqSpec` is lean-x86's `Operations.PMULUw 32 128`
(element size 32, results of twice that). No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits: `pmuludqMmxSpec`.
-/

namespace X86Proofs

/-- Quadword `i` of the result is the product of doubleword `2 i` of `a` and of `b`, unsigned. -/
def pmuludqSpec (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 64 fun i =>
    BitVec.ofNat 64 ((lane 32 a (2 * i)).toNat * (lane 32 b (2 * i)).toNat)

/-- `pmuludqSpec` at 64 bits, for the MMX forms. -/
def pmuludqMmxSpec (a b : BitVec 64) : BitVec 64 :=
  ofLanes 64 64 fun i =>
    BitVec.ofNat 64 ((lane 32 a (2 * i)).toNat * (lane 32 b (2 * i)).toNat)

open X86

theorem pmuludq_operation (a b : BitVec 128) :
    X86.Instructions.Operations.PMULUw 32 128 a b = .ok (pmuludqSpec a b) := by
  unfold X86.Instructions.Operations.PMULUw
  lanes_loop
  lane_eq
  rw [← BitVec.ofInt_natCast]
  congr 1 <;> omega

theorem pmuludq_mmx_operation (a b : BitVec 64) :
    X86.Instructions.Operations.PMULUw 32 64 a b = .ok (pmuludqMmxSpec a b) := by
  unfold X86.Instructions.Operations.PMULUw
  lanes_loop
  lane_eq
  rw [← BitVec.ofInt_natCast]
  congr 1 <;> omega

end X86Proofs
