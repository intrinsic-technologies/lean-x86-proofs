import X86Proofs.Core.Lanes

/-!
# PMULHUW specification

`PMULHUW xmm1, xmm2/m128` (`66 0F E4 /r`): multiply the packed unsigned words and keep the high
word of each 32-bit product, `TEMP0[31:0] ← DEST[15:0] ∗ SRC[15:0]; DEST[15:0] ← TEMP0[31:16]`
and so on. `pmulhuwSpec` is lean-x86's `Operations.PMULHU 16 128`. No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits: `pmulhuwMmxSpec`.
-/

namespace X86Proofs

/-- Each word of the result is the high word of the unsigned product of the words of `a` and `b`. -/
def pmulhuwSpec (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 16 fun i =>
    BitVec.ofNat 16 ((lane 16 a i).toNat * (lane 16 b i).toNat / 2 ^ 16)

/-- `pmulhuwSpec` at 64 bits, for the MMX forms. -/
def pmulhuwMmxSpec (a b : BitVec 64) : BitVec 64 :=
  ofLanes 64 16 fun i =>
    BitVec.ofNat 16 ((lane 16 a i).toNat * (lane 16 b i).toNat / 2 ^ 16)

open X86

theorem pmulhuw_operation (a b : BitVec 128) :
    X86.Instructions.Operations.PMULHU 16 128 a b = .ok (pmulhuwSpec a b) := by
  unfold X86.Instructions.Operations.PMULHU
  lanes_loop
  lane_eq
  rw [← BitVec.ofInt_natCast]
  congr 1 <;> omega

theorem pmulhuw_mmx_operation (a b : BitVec 64) :
    X86.Instructions.Operations.PMULHU 16 64 a b = .ok (pmulhuwMmxSpec a b) := by
  unfold X86.Instructions.Operations.PMULHU
  lanes_loop
  lane_eq
  rw [← BitVec.ofInt_natCast]
  congr 1 <;> omega

end X86Proofs
