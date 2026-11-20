import X86Proofs.Core.Lanes

/-!
# MOVAPS, MOVAPD, MOVDQA specification

`MOVAPS`/`MOVAPD xmm1, xmm2/m128` (`0F 28 /r`, `66 0F 28 /r`), `MOVDQA xmm1, xmm2/m128`
(`66 0F 6F /r`) and their stores (`0F 29`, `66 0F 29`, `66 0F 7F`): `DEST[127:0] ← SRC[127:0]`,
the whole 128 bits copied (bits 128–511 of an XMM destination's ZMM register are kept, as for every
legacy SSE write). lean-x86 copies element by element (`Operations.MOVA w 128`, with 32-bit
elements for MOVAPS and MOVDQA and 64-bit ones for MOVAPD), which is the identity. A memory operand
must be 16-byte aligned (`Explicitly_Aligned`, else #GP). No flags.
-/

namespace X86Proofs

open X86

theorem mova_lanes_operation (w : Nat) (hw : w = 32 ∨ w = 64) (a : BitVec 128) :
    X86.Instructions.Operations.MOVA w 128 a = .ok a := by
  have hd : w ∣ 128 := by rcases hw with rfl | rfl <;> decide
  conv => rhs; rw [← ofLanes_lane (by omega) hd a]
  rcases hw with rfl | rfl <;>
  · unfold X86.Instructions.Operations.MOVA
    lanes_loop

theorem mova_operation (a : BitVec 128) :
    X86.Instructions.Operations.MOVA 32 128 a = .ok a :=
  mova_lanes_operation 32 (.inl rfl) a

end X86Proofs
