import X86Proofs.Core.Lanes

/-!
# PANDN, ANDNPS, ANDNPD specification

`PANDN xmm1, xmm2/m128` (`66 0F DF /r`): `DEST ← NOT(DEST) AND SRC`, all 128 bits. `ANDNPS`
(`0F 55`) and `ANDNPD` (`66 0F 55`) are the same, per 32-bit or 64-bit element in the SDM and in
lean-x86 (`Operations.VPANDN`), which together is the 128-bit AND NOT (`ofLanes_andNot`). Bitwise:
no MXCSR access. No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits.
-/

namespace X86Proofs

open X86

theorem pandn_operation (a b : BitVec 128) :
    X86.Instructions.Operations.PANDN 128 a b = .ok (~~~a &&& b) := rfl

theorem vpandn_operation (w : Nat) (hw : w = 32 ∨ w = 64) (a b : BitVec 128) :
    X86.Instructions.Operations.VPANDN w 128 a b = .ok (~~~a &&& b) := by
  have hd : w ∣ 128 := by rcases hw with rfl | rfl <;> decide
  rw [← ofLanes_andNot (by omega) hd]
  rcases hw with rfl | rfl <;>
  · unfold X86.Instructions.Operations.VPANDN
    lanes_loop

theorem pandn_mmx_operation (a b : BitVec 64) :
    X86.Instructions.Operations.PANDN 64 a b = .ok (~~~a &&& b) := rfl

end X86Proofs
