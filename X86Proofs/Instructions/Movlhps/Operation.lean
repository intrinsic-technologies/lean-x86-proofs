import X86Proofs.Core.Lanes

/-!
# MOVLHPS specification

`MOVLHPS xmm1, xmm2` (`0F 16 /r`, register operand): `DEST[127:64] ← SRC[63:0]`, `DEST[63:0]`
unchanged: `movlhpsSpec dst src = src[63:0] ++ dst[63:0]` (lean-x86's `Operations.MOVLHP`). No
flags.
-/

namespace X86Proofs

/-- The low quadword of `src` moved into the high quadword of `dst`. -/
def movlhpsSpec (dst src : BitVec 128) : BitVec 128 :=
  src.extractLsb' 0 64 ++ dst.extractLsb' 0 64

open X86

theorem movlhp_operation (w : Int) (dst src : BitVec 128) :
    X86.Instructions.Operations.MOVLHP dst src w = .ok (movlhpsSpec dst src) := by
  unfold X86.Instructions.Operations.MOVLHP
  simp only [x86_runtime, sliceInclusive_eq, pure_bind]
  exact congrArg Except.ok (ofNat_shiftLeft_add_eq_append_any _ _)

end X86Proofs
