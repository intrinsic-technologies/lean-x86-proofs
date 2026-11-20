import X86Proofs.Core.Lanes

/-!
# MOVHPS, MOVHPD specification

`MOVHPS`/`MOVHPD xmm1, m64` (`0F 16 /r`, `66 0F 16 /r`, memory operand): `DEST[127:64] ←
SRC[63:0]`, `DEST[63:0]` unchanged (`movhpLoadSpec dst src`). `MOVHPS`/`MOVHPD m64, xmm1`
(`0F 17`, `66 0F 17`): `DEST[63:0] ← SRC[127:64]`, the high quadword stored (`movhpStoreSpec
src`). lean-x86's `Operations.MOVHP_fromMem` and `MOVHP_toMem` (the element size is unused). No
flags.
-/

namespace X86Proofs

/-- The high quadword of `dst` replaced by `src`: `src ++ dst[63:0]`. -/
def movhpLoadSpec (dst : BitVec 128) (src : BitVec 64) : BitVec 128 := src ++ dst.extractLsb' 0 64

/-- The high quadword of `src`. -/
def movhpStoreSpec (src : BitVec 128) : BitVec 64 := src.extractLsb' 64 64

open X86

theorem movhp_load_operation (w : Int) (dst : BitVec 128) (src : BitVec 64) :
    X86.Instructions.Operations.MOVHP_fromMem w dst src = .ok (movhpLoadSpec dst src) := by
  unfold X86.Instructions.Operations.MOVHP_fromMem
  simp only [x86_runtime, sliceInclusive_eq, pure_bind]
  exact congrArg Except.ok (ofNat_shiftLeft_add_eq_append_any _ _)

theorem movhp_store_operation (w : Int) (src : BitVec 128) :
    X86.Instructions.Operations.MOVHP_toMem w src = .ok (movhpStoreSpec src) := rfl

end X86Proofs
