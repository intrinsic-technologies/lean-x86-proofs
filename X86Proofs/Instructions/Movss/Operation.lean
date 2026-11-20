import X86Proofs.Core.Runtime

/-!
# MOVSS specification

`MOVSS xmm1, xmm2/m32` and `MOVSS xmm2/m32, xmm1` (`F3 0F 10 /r`, `F3 0F 11 /r`) move the low
doubleword, element size `e = 32` (lean-x86's `Operations.MOVS_load`, `MOVS_reg`, `MOVS_store`
take `e`, 64 for MOVSD):

- from memory (`movsLoadSpec e src`): `DEST[31:0] ← SRC[31:0]; DEST[127:32] ← 0`, the element
  zero-extended to 128 bits;
- between registers (`movsRegSpec e dst src`): `DEST[31:0] ← SRC[31:0]`, `DEST[127:32]`
  unchanged;
- to memory (`movsStoreSpec e src`): `DEST[31:0] ← SRC[31:0]`.

These are moves, not arithmetic: MXCSR is not read and no exception is raised. No flags.
-/

namespace X86Proofs

/-- A scalar loaded from memory: the `e`-bit element zero-extended to 128 bits. -/
def movsLoadSpec (e : Nat) (src : BitVec e) : BitVec 128 := src.setWidth 128

/-- A scalar moved between registers: the low `e` bits of `dst` replaced by those of `src`, the
rest of `dst` unchanged. -/
def movsRegSpec (e : Nat) (dst src : BitVec 128) : BitVec 128 :=
  X86.Runtime.setSlice dst 0 e (src.extractLsb' 0 e)

/-- A scalar stored to memory: the low `e` bits of `src`. -/
def movsStoreSpec (e : Nat) (src : BitVec 128) : BitVec e := src.extractLsb' 0 e

open X86

theorem movs_load_operation (e : Nat) (he : e = 32 ∨ e = 64) (src : BitVec e) :
    X86.Instructions.Operations.MOVS_load e 128 src = .ok (movsLoadSpec e src) := by
  unfold X86.Instructions.Operations.MOVS_load
  rcases he with rfl | rfl <;> simp [x86_runtime, movsLoadSpec] <;> rfl

theorem movs_reg_operation (e : Nat) (he : e = 32 ∨ e = 64) (dst src : BitVec 128) :
    X86.Instructions.Operations.MOVS_reg e 128 dst src = .ok (movsRegSpec e dst src) := by
  unfold X86.Instructions.Operations.MOVS_reg
  rcases he with rfl | rfl <;> simp [x86_runtime, movsRegSpec] <;> rfl

theorem movs_store_operation (e : Nat) (he : e = 32 ∨ e = 64) (src : BitVec 128) :
    X86.Instructions.Operations.MOVS_store e 128 src = .ok (movsStoreSpec e src) := by
  unfold X86.Instructions.Operations.MOVS_store
  rcases he with rfl | rfl <;> simp [x86_runtime, movsStoreSpec] <;> rfl

end X86Proofs
