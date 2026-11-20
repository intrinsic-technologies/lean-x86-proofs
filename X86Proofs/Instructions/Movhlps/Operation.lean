import X86Proofs.Core.Lanes

/-!
# MOVHLPS specification

`MOVHLPS xmm1, xmm2` (`0F 12 /r`, register operand): `DEST[63:0] ← SRC[127:64]`,
`DEST[127:64]` unchanged: `movhlpsSpec dst src = dst[127:64] ++ src[127:64]` (lean-x86's
`Operations.MOVHLP`). No flags.
-/

namespace X86Proofs

/-- The high quadword of `src` moved into the low quadword of `dst`. -/
def movhlpsSpec (dst src : BitVec 128) : BitVec 128 :=
  dst.extractLsb' 64 64 ++ src.extractLsb' 64 64

open X86

theorem movhlp_operation (dst src : BitVec 128) :
    X86.Instructions.Operations.MOVHLP dst src = .ok (movhlpsSpec dst src) := by
  unfold X86.Instructions.Operations.MOVHLP
  simp only [x86_runtime, sliceInclusive_eq, pure_bind]
  exact congrArg Except.ok (ofNat_shiftLeft_add_eq_append_any _ _)

end X86Proofs
