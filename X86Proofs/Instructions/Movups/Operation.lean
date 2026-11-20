import X86Proofs.Core.Lanes

/-!
# MOVUPS, MOVUPD specification

`MOVUPS`/`MOVUPD xmm1, xmm2/m128` (`0F 10 /r`, `66 0F 10 /r`) and their stores (`0F 11`,
`66 0F 11`): `DEST[127:0] ← SRC[127:0]`, the whole 128 bits copied (bits 128–511 of an XMM
destination's ZMM register are kept). lean-x86 copies element by element into a zero register
(`Operations.MOVUP w 128`, 32-bit elements for MOVUPS, 64-bit for MOVUPD), which is the identity.
A memory operand may be unaligned (`Explicitly_Unaligned`). No flags.
-/

namespace X86Proofs

open X86

theorem movup_lanes_operation (w : Nat) (hw : w = 32 ∨ w = 64) (a : BitVec 128) :
    X86.Instructions.Operations.MOVUP w 128 a = .ok a := by
  have hd : w ∣ 128 := by rcases hw with rfl | rfl <;> decide
  conv => rhs; rw [← ofLanes_lane (by omega) hd a]
  rcases hw with rfl | rfl <;>
  · unfold X86.Instructions.Operations.MOVUP
    lanes_loop

theorem movup_operation (a : BitVec 128) :
    X86.Instructions.Operations.MOVUP 32 128 a = .ok a :=
  movup_lanes_operation 32 (.inl rfl) a

end X86Proofs
