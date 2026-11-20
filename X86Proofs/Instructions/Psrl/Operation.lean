import X86Proofs.Core.Lanes
import X86Proofs.Core.Shift

/-!
# PSRLW, PSRLD, PSRLQ specification

`PSRLW`/`PSRLD`/`PSRLQ xmm1, xmm2/m128` (`66 0F D1`/`D2`/`D3 /r`): shift each word, doubleword or
quadword of the destination right by the same count, shifting in zeros. The count is the low
quadword of the source, `COUNT ← SRC[63:0]`; if it exceeds the lane width less one, every lane
becomes zero (`IF COUNT > 15 THEN DEST[127:0] ← 0 ELSE DEST[15:0] ← DEST[15:0] >> COUNT; …`).
`PSRLW`/`PSRLD`/`PSRLQ xmm1, imm8` (`66 0F 71`/`72`/`73 /2 ib`) shift by the immediate instead.
`psrlSpec w` is the result for lanes of `w` bits and a count given as a number; lean-x86 computes
it with `Operations.PSRL w 128 128` (count in `xmm/m128`) or `Operations.PSRL w 128 8` (immediate
count). No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits: `psrlMmxSpec`.
-/

namespace X86Proofs

/-- Each `w`-bit lane of `a` shifted right (logically) by `count`, or zero when `count ≥ w`. -/
def psrlSpec (w : Nat) (a : BitVec 128) (count : Nat) : BitVec 128 :=
  ofLanes 128 w fun i => if count < w then lane w a i >>> count else 0

/-- `psrlSpec` at 64 bits, for the MMX forms. -/
def psrlMmxSpec (w : Nat) (a : BitVec 64) (count : Nat) : BitVec 64 :=
  ofLanes 64 w fun i => if count < w then lane w a i >>> count else 0

open X86

theorem psrl_operation (w : Nat) (hw : w = 16 ∨ w = 32 ∨ w = 64) (a b : BitVec 128) :
    X86.Instructions.Operations.PSRL w 128 128 a b =
      .ok (psrlSpec w a (b.extractLsb' 0 64).toNat) := by
  rcases hw with rfl | rfl | rfl <;>
  · unfold X86.Instructions.Operations.PSRL
    lanes_loop
    rw [ite_eq_left (by decide), shiftRightLogical_run _ _ (by decide)]
    rfl

theorem psrl_imm_operation (w : Nat) (hw : w = 16 ∨ w = 32 ∨ w = 64) (a : BitVec 128)
    (imm : BitVec 8) :
    X86.Instructions.Operations.PSRL w 128 8 a imm = .ok (psrlSpec w a imm.toNat) := by
  rcases hw with rfl | rfl | rfl <;>
  · unfold X86.Instructions.Operations.PSRL
    lanes_loop
    rw [ite_eq_right (by decide), shiftRightLogical_run _ _ (by decide)]
    rfl

theorem psrl_mmx_operation (w : Nat) (hw : w = 16 ∨ w = 32 ∨ w = 64) (a b : BitVec 64) :
    X86.Instructions.Operations.PSRL w 64 64 a b =
      .ok (psrlMmxSpec w a b.toNat) := by
  rcases hw with rfl | rfl | rfl <;>
  · unfold X86.Instructions.Operations.PSRL
    lanes_loop
    rw [ite_eq_right (by decide), shiftRightLogical_run _ _ (by decide)]
    rfl

theorem psrl_mmx_imm_operation (w : Nat) (hw : w = 16 ∨ w = 32 ∨ w = 64) (a : BitVec 64)
    (imm : BitVec 8) :
    X86.Instructions.Operations.PSRL w 64 8 a imm = .ok (psrlMmxSpec w a imm.toNat) := by
  rcases hw with rfl | rfl | rfl <;>
  · unfold X86.Instructions.Operations.PSRL
    lanes_loop
    rw [ite_eq_right (by decide), shiftRightLogical_run _ _ (by decide)]
    rfl

end X86Proofs
