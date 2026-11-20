import X86Proofs.Core.Lanes

/-!
# POR, ORPS, ORPD specification

`POR xmm1, xmm2/m128` (`66 0F EB /r`): `DEST ← DEST OR SRC`, all 128 bits. `ORPS` (`0F 56`) and
`ORPD` (`66 0F 56`) are the same, per 32-bit or 64-bit element in the SDM and in lean-x86
(`Operations.VPOR`), which together is the 128-bit OR (`ofLanes_or`). Bitwise: no MXCSR access.
No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits.
-/

namespace X86Proofs

open X86

theorem por_operation (a b : BitVec 128) :
    X86.Instructions.Operations.POR 128 a b = .ok (a ||| b) := rfl

theorem vpor_operation (w : Nat) (hw : w = 32 ∨ w = 64) (a b : BitVec 128) :
    X86.Instructions.Operations.VPOR w 128 a b = .ok (a ||| b) := by
  have hd : w ∣ 128 := by rcases hw with rfl | rfl <;> decide
  rw [← ofLanes_or (by omega) hd]
  rcases hw with rfl | rfl <;>
  · unfold X86.Instructions.Operations.VPOR
    lanes_loop

theorem por_mmx_operation (a b : BitVec 64) :
    X86.Instructions.Operations.POR 64 a b = .ok (a ||| b) := rfl

end X86Proofs
