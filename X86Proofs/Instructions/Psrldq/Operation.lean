import X86Proofs.Core.Lanes
import X86Proofs.Core.Shift

/-!
# PSRLDQ specification

`PSRLDQ xmm1, imm8` (`66 0F 73 /3 ib`): shift the whole destination right by the immediate count of
bytes, shifting in zero bytes; a count above 15 clears it (`TEMP ← COUNT; IF TEMP > 15 THEN
TEMP ← 16; DEST ← DEST >> (TEMP * 8)`). `psrldqSpec` is the result for a count given as a number;
lean-x86 computes it with `Operations.PSRLDQ 128 128 8`. No flags.
-/

namespace X86Proofs

/-- `a` shifted right by `count` bytes, or zero when `count > 15`. -/
def psrldqSpec (a : BitVec 128) (count : Nat) : BitVec 128 :=
  if count < 16 then a >>> (count * 8) else 0

open X86

theorem psrldq_operation (a : BitVec 128) (imm : BitVec 8) :
    X86.Instructions.Operations.PSRLDQ 128 128 8 a imm = .ok (psrldqSpec a imm.toNat) := by
  rw [← ofLanes_full (by decide) (psrldqSpec a imm.toNat)]
  unfold X86.Instructions.Operations.PSRLDQ
  lanes_loop
  rw [show (imm.toNat : Int) * 8 = ((imm.toNat * 8 : Nat) : Int) by omega,
    shiftRightLogical_run _ _ (by decide)]
  rename_i i hi r
  obtain rfl : i = 0 := by omega
  simp only [Nat.zero_mul, Int.reduceToNat, BitVec.extractLsb'_eq_self, psrldqSpec]
  by_cases h : imm.toNat < 16
  · rw [ite_eq_left (by omega), ite_eq_left h]; rfl
  · rw [ite_eq_right (by omega), ite_eq_right h]; rfl

end X86Proofs
