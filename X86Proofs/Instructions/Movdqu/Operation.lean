import X86Proofs.Core.Lanes

/-!
# MOVDQU specification

`MOVDQU xmm1, xmm2/m128` (`F3 0F 6F /r`) and its store (`F3 0F 7F /r`): `DEST[127:0] ←
SRC[127:0]`, the whole 128 bits copied (bits 128–511 of an XMM destination's ZMM register are
kept). lean-x86 copies element by element (`Operations.MOVU 32 128`), which is the identity. A
memory operand may be unaligned (`Explicitly_Unaligned`). No flags.
-/

namespace X86Proofs

open X86

theorem movu_operation (a : BitVec 128) :
    X86.Instructions.Operations.MOVU 32 128 a = .ok a := by
  conv => rhs; rw [← ofLanes_lane (by omega) (by decide : 32 ∣ 128) a]
  unfold X86.Instructions.Operations.MOVU
  lanes_loop

end X86Proofs
