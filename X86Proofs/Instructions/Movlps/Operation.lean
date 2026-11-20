import X86Proofs.Core.Lanes

/-!
# MOVLPS, MOVLPD specification

`MOVLPS`/`MOVLPD xmm1, m64` (`0F 12 /r`, `66 0F 12 /r`, memory operand): `DEST[63:0] ← SRC[63:0]`,
`DEST[127:64]` unchanged (`movlpLoadSpec dst src`). `MOVLPS`/`MOVLPD m64, xmm1` (`0F 13`,
`66 0F 13`): `DEST[63:0] ← SRC[63:0]`, the low quadword stored (`movlpStoreSpec src`). lean-x86's
`Operations.MOVLP_fromMem` and `MOVLP_toMem` (the element size is unused). No flags.
-/

namespace X86Proofs

/-- The low quadword of `dst` replaced by `src`: `dst[127:64] ++ src`. -/
def movlpLoadSpec (dst : BitVec 128) (src : BitVec 64) : BitVec 128 := dst.extractLsb' 64 64 ++ src

/-- The low quadword of `src`. -/
def movlpStoreSpec (src : BitVec 128) : BitVec 64 := src.extractLsb' 0 64

open X86

theorem movlp_load_operation (w : Int) (dst : BitVec 128) (src : BitVec 64) :
    X86.Instructions.Operations.MOVLP_fromMem w dst src = .ok (movlpLoadSpec dst src) := by
  unfold X86.Instructions.Operations.MOVLP_fromMem
  simp only [x86_runtime, sliceInclusive_eq, pure_bind]
  exact congrArg Except.ok (ofNat_shiftLeft_add_eq_append_any _ _)

theorem movlp_store_operation (w : Int) (src : BitVec 128) :
    X86.Instructions.Operations.MOVLP_toMem w src = .ok (movlpStoreSpec src) := rfl

end X86Proofs
