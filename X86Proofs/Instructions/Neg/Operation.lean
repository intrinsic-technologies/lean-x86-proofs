import X86Proofs.Core.Run
import X86Proofs.Core.Flags

/-!
# NEG specification

A pure function: no state, no failure, no oracle. NEG is `0 - x` (two's complement negation) and
sets every flag as the subtraction `0 - x` does: CF says the operand is not zero, AF that the low
four bits are not zero (both are the borrows of `0 - x`), OF that the signed result differs from
the true negation (only for the most negative value).
-/

namespace X86Proofs

/-- Result and flags of `-x` (CF is set unless `x = 0`). -/
def negSpec {n : Nat} (x : BitVec n) : BitVec n × StatusFlags :=
  let r := -x
  (r, { OF := decide (r.toInt ≠ -x.toInt), CF := decide (x ≠ 0),
        SF := r.msb, ZF := r == 0, PF := evenParity (r.extractLsb' 0 8),
        AF := decide (x.extractLsb' 0 4 ≠ 0) })

open X86 X86.Helpers

theorem ofInt_neg_toNat {n : Nat} (x : BitVec n) : BitVec.ofInt n (-(x.toNat : Int)) = -x := by
  rw [BitVec.ofInt_neg, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem neg_af_iff {n : Nat} (x : BitVec n) :
    (max (-(x.toNat : Int) % 16) 0 = -((x.toNat : Int) % 16)) ↔ x.extractLsb' 0 4 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.extractLsb'_toNat]
  show _ ↔ x.toNat >>> 0 % 2 ^ 4 = 0
  rw [Nat.shiftRight_zero]
  omega

theorem neg_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x : BitVec n) :
    (X86.Instructions.Operations.NEG n x).run s =
      let (r, flags) := negSpec x
      (.ok r, setFlags s flags) := by
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.NEG
    simp only [isParityEven8_run]
    repeat spec_bind_rfl
    simp [x86_runtime, extractLsb'_msb, beq_zero_eq_decide, setFlags, StatusFlags.store,
      negSpec, ofInt_neg_toNat, neg_af_iff]
    repeat rw [ite_zero_one]
    repeat rw [ite_one_zero]
    simp only [Bool.decide_eq_true]

end X86Proofs
