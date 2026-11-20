import X86Proofs.Core.Lanes
import X86Proofs.Core.Shift

/-!
# PSRAW, PSRAD specification

`PSRAW`/`PSRAD xmm1, xmm2/m128` (`66 0F E1`/`E2 /r`): shift each word or doubleword of the
destination right by the same count, shifting in copies of its sign bit. The count is the low
quadword of the source, `COUNT ← SRC[63:0]`, capped at the lane width
(`IF COUNT > 15 THEN COUNT ← 16; DEST[15:0] ← SignExtend(DEST[15:0] >> COUNT); …`), so a count of
the width or more fills each lane with its sign bit. `PSRAW`/`PSRAD xmm1, imm8`
(`66 0F 71`/`72 /4 ib`) shift by the immediate instead. `psraSpec w` is the result for lanes of
`w` bits and a count given as a number; lean-x86 computes it with `Operations.PSRA w 128 128`
(count in `xmm/m128`) or `Operations.PSRA w 128 8` (immediate count). No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits: `psraMmxSpec`.
-/

namespace X86Proofs

/-- Each `w`-bit lane of `a` shifted right arithmetically by `count`, capped at `w`. -/
def psraSpec (w : Nat) (a : BitVec 128) (count : Nat) : BitVec 128 :=
  ofLanes 128 w fun i => (lane w a i).sshiftRight (min count w)

/-- `psraSpec` at 64 bits, for the MMX forms. -/
def psraMmxSpec (w : Nat) (a : BitVec 64) (count : Nat) : BitVec 64 :=
  ofLanes 64 w fun i => (lane w a i).sshiftRight (min count w)

open X86

theorem psra_operation (w : Nat) (hw : w = 16 ∨ w = 32) (a b : BitVec 128) :
    X86.Instructions.Operations.PSRA w 128 128 a b =
      .ok (psraSpec w a (b.extractLsb' 0 64).toNat) := by
  rcases hw with rfl | rfl <;>
  · unfold X86.Instructions.Operations.PSRA
    lanes_loop
    rw [ite_eq_left (by decide), shiftRightArithmetic_run _ _ (by decide)]
    rfl

theorem psra_imm_operation (w : Nat) (hw : w = 16 ∨ w = 32) (a : BitVec 128)
    (imm : BitVec 8) :
    X86.Instructions.Operations.PSRA w 128 8 a imm = .ok (psraSpec w a imm.toNat) := by
  rcases hw with rfl | rfl <;>
  · unfold X86.Instructions.Operations.PSRA
    lanes_loop
    rw [ite_eq_right (by decide), shiftRightArithmetic_run _ _ (by decide)]
    rfl

theorem psra_mmx_operation (w : Nat) (hw : w = 16 ∨ w = 32) (a b : BitVec 64) :
    X86.Instructions.Operations.PSRA w 64 64 a b =
      .ok (psraMmxSpec w a b.toNat) := by
  rcases hw with rfl | rfl <;>
  · unfold X86.Instructions.Operations.PSRA
    lanes_loop
    rw [ite_eq_right (by decide), shiftRightArithmetic_run _ _ (by decide)]
    rfl

theorem psra_mmx_imm_operation (w : Nat) (hw : w = 16 ∨ w = 32) (a : BitVec 64)
    (imm : BitVec 8) :
    X86.Instructions.Operations.PSRA w 64 8 a imm = .ok (psraMmxSpec w a imm.toNat) := by
  rcases hw with rfl | rfl <;>
  · unfold X86.Instructions.Operations.PSRA
    lanes_loop
    rw [ite_eq_right (by decide), shiftRightArithmetic_run _ _ (by decide)]
    rfl

end X86Proofs
