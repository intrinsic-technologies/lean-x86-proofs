import X86Proofs.Core.Lanes

/-!
# BSWAP specification

`BSWAP r32` / `BSWAP r64` (`0F C8+r`) reverses the byte order of the register: `TEMP ← DEST;
DEST[7:0] ← TEMP[31:24]; DEST[15:8] ← TEMP[23:16]; DEST[23:16] ← TEMP[15:8]; DEST[31:24] ←
TEMP[7:0]` (and likewise with eight bytes at 64 bits). `bswapSpec x` is that result: byte `i` of
the result is byte `n / 8 - 1 - i` of `x`. No flags. lean-x86 computes it with
`Operations.BSWAP n` (`Byte_Reverse`). BSWAP of a 16-bit register is undefined in the SDM
(lean-x86 writes zero); it is not covered.
-/

namespace X86Proofs

/-- `x` with its bytes in reverse order: byte `i` of the result (bits `8 i` to `8 i + 7`) is byte
`n / 8 - 1 - i` of `x`. -/
def bswapSpec {n : Nat} (x : BitVec n) : BitVec n :=
  ofLanes n 8 (fun i => lane 8 x (n / 8 - 1 - i))

open X86 X86.Runtime

theorem bswap_operation (n : Nat) (hn : n = 32 ∨ n = 64) (x : BitVec n) :
    X86.Instructions.Operations.BSWAP n x = .ok (bswapSpec x) := by
  rcases hn with rfl | rfl
  · unfold X86.Instructions.Operations.BSWAP X86.Helpers.Byte_Reverse
    simp only [x86_runtime, pure_bind]
    erw [assertWithProof_bind_true _ rfl, remember_bind_ok _ 4 rfl]
    simp only [x86_runtime, pure_bind, Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
    rw [forIn_writeSlice_lanes 8 4 (by decide) rfl (fun i => x.extractLsb' ((3 - i) * 8) 8) _ ?h]
    case h =>
      intro i hi p u
      simp (disch := lanes_disch) only [x86_runtime, pure_bind, writeSlice_mk, BitVec.cast_eq,
        Int.toNat_natCast, Int.toNat_mul, Int.reduceToNat]
      rw [show ((3 : Int) - i).toNat = 3 - i by omega]
      rfl
    simp only [bind, Except.bind]
    rw [read_mk _ _ (by decide) rfl]
    rfl
  · unfold X86.Instructions.Operations.BSWAP X86.Helpers.Byte_Reverse
    simp only [x86_runtime, pure_bind]
    erw [assertWithProof_bind_true _ rfl, remember_bind_ok _ 8 rfl]
    simp only [x86_runtime, pure_bind, Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
    rw [forIn_writeSlice_lanes 8 8 (by decide) rfl (fun i => x.extractLsb' ((7 - i) * 8) 8) _ ?h]
    case h =>
      intro i hi p u
      simp (disch := lanes_disch) only [x86_runtime, pure_bind, writeSlice_mk, BitVec.cast_eq,
        Int.toNat_natCast, Int.toNat_mul, Int.reduceToNat]
      rw [show ((7 : Int) - i).toNat = 7 - i by omega]
      rfl
    simp only [bind, Except.bind]
    rw [read_mk _ _ (by decide) rfl]
    rfl

end X86Proofs
