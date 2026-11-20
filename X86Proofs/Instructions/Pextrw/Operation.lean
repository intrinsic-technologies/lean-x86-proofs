import X86Proofs.Core.Lanes
import X86Proofs.Core.Run

/-!
# PEXTRW specification

`PEXTRW r32, xmm, imm8` (`66 0F C5 /r ib`): the destination becomes the word of the source the low
three bits of the immediate select, zero-extended, `SEL ← imm8[2:0]; TEMP ← (SRC >> (SEL * 16))
AND FFFFH; DEST[15:0] ← TEMP[15:0]; DEST[31:16] ← 0`. `pextrwSpec` is the result; lean-x86
computes it with `Operations.PEXTR 32 16 128`, a `PartialResult` (`Std.Integer.Log2`). No flags.

The MMX form (`NP 0F C5`) extracts one of the four words of an MMX register: `pextrwMmxSpec`
(`Operations.PEXTR 32 16 64`).
-/

namespace X86Proofs

/-- Word `imm[2:0]` of `a`, zero-extended to 32 bits. -/
def pextrwSpec (a : BitVec 128) (imm : BitVec 8) : BitVec 32 :=
  (lane 16 a (imm.extractLsb' 0 3).toNat).setWidth 32

/-- The MMX form (`PEXTRW r32, mm, imm8`, `NP 0F C5`): word `imm[1:0]` of `a`, zero-extended to 32
bits. -/
def pextrwMmxSpec (a : BitVec 64) (imm : BitVec 8) : BitVec 32 :=
  (lane 16 a (imm.extractLsb' 0 2).toNat).setWidth 32

open X86

theorem pextrw_operation (a : BitVec 128) (imm : BitVec 8) :
    X86.Instructions.Operations.PEXTR 32 16 128 a imm =
      (pure (pextrwSpec a imm) : X86.Runtime.PartialResult Empty (BitVec 32)) := by
  unfold X86.Instructions.Operations.PEXTR
  simp only [x86_runtime, pure_bind, Int.reduceDiv, stdLog2_eight]
  have hv := (imm.extractLsb' 0 3).isLt
  simp only [Nat.reducePow] at hv
  simp (disch := lanes_disch) only [x86_runtime, pure_bind]
  rw [show (((imm.extractLsb' 0 3).toNat : Int) * 16).toNat = (imm.extractLsb' 0 3).toNat * 16 by
    omega]
  rfl

theorem pextrw_mmx_operation (a : BitVec 64) (imm : BitVec 8) :
    X86.Instructions.Operations.PEXTR 32 16 64 a imm =
      (pure (pextrwMmxSpec a imm) : X86.Runtime.PartialResult Empty (BitVec 32)) := by
  unfold X86.Instructions.Operations.PEXTR
  simp only [x86_runtime, pure_bind, Int.reduceDiv, stdLog2_four]
  have hv := (imm.extractLsb' 0 2).isLt
  simp only [Nat.reducePow] at hv
  simp (disch := lanes_disch) only [x86_runtime, pure_bind]
  rw [show (((imm.extractLsb' 0 2).toNat : Int) * 16).toNat = (imm.extractLsb' 0 2).toNat * 16 by
    omega]
  rfl

end X86Proofs
