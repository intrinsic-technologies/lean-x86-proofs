import X86Proofs.Core.Lanes

/-!
# PAND, ANDPS, ANDPD specification

`PAND xmm1, xmm2/m128` (`66 0F DB /r`): `DEST ← DEST AND SRC`, all 128 bits. `ANDPS` (`0F 54`)
and `ANDPD` (`66 0F 54`) are the same bitwise AND; the SDM writes them per 32-bit or 64-bit
element (`DEST[31:0] ← DEST[31:0] BITWISE AND SRC[31:0]`, …), as lean-x86 computes them
(`Operations.VPAND` with element size 32 or 64), and the elements together are the 128-bit AND
(`ofLanes_and`). They are bitwise: no MXCSR access, no floating-point exception. No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits.
-/

namespace X86Proofs

open X86

theorem pand_operation (a b : BitVec 128) :
    X86.Instructions.Operations.PAND 128 a b = .ok (a &&& b) := rfl

theorem vpand_operation (w : Nat) (hw : w = 32 ∨ w = 64) (a b : BitVec 128) :
    X86.Instructions.Operations.VPAND w 128 a b = .ok (a &&& b) := by
  have hd : w ∣ 128 := by rcases hw with rfl | rfl <;> decide
  rw [← ofLanes_and (by omega) hd]
  rcases hw with rfl | rfl <;>
  · unfold X86.Instructions.Operations.VPAND
    lanes_loop

theorem pand_mmx_operation (a b : BitVec 64) :
    X86.Instructions.Operations.PAND 64 a b = .ok (a &&& b) := rfl

end X86Proofs
