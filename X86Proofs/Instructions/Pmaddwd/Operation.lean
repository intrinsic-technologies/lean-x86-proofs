import X86Proofs.Core.Lanes

/-!
# PMADDWD specification

`PMADDWD xmm1, xmm2/m128` (`66 0F F5 /r`): multiply the packed signed words and add the two
products of each doubleword, `DEST[31:0] ← (DEST[15:0] ∗ SRC[15:0]) + (DEST[31:16] ∗ SRC[31:16])`
and so on, in 32 bits (the SDM notes the sum wraps only for all four words `8000H`).
`pmaddwdSpec` is lean-x86's `Operations.PMADD 16 128`: the words of each doubleword sign-extended
to 32 bits, multiplied and added, odd word first. No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits: `pmaddwdMmxSpec`.
-/

namespace X86Proofs

/-- Doubleword `i` of the result is the sum of the signed products of the two words of doubleword
`i` of `a` and of `b`. -/
def pmaddwdSpec (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 32 fun i =>
    let x := lane 32 a i
    let y := lane 32 b i
    (lane 16 x 1).signExtend 32 * (lane 16 y 1).signExtend 32 +
      (lane 16 x 0).signExtend 32 * (lane 16 y 0).signExtend 32

/-- `pmaddwdSpec` at 64 bits, for the MMX forms. -/
def pmaddwdMmxSpec (a b : BitVec 64) : BitVec 64 :=
  ofLanes 64 32 fun i =>
    let x := lane 32 a i
    let y := lane 32 b i
    (lane 16 x 1).signExtend 32 * (lane 16 y 1).signExtend 32 +
      (lane 16 x 0).signExtend 32 * (lane 16 y 0).signExtend 32

open X86

theorem pmaddwd_operation (a b : BitVec 128) :
    X86.Instructions.Operations.PMADD 16 128 a b = .ok (pmaddwdSpec a b) := by
  unfold X86.Instructions.Operations.PMADD
  lanes_loop

theorem pmaddwd_mmx_operation (a b : BitVec 64) :
    X86.Instructions.Operations.PMADD 16 64 a b = .ok (pmaddwdMmxSpec a b) := by
  unfold X86.Instructions.Operations.PMADD
  lanes_loop

end X86Proofs
