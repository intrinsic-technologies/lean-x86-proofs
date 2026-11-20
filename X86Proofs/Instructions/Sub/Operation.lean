import X86Proofs.Core.Run
import X86Proofs.Core.Oracle
import X86Proofs.Core.Flags

/-!
# SUB specification

A pure function: no state, no failure, no oracle. Every flag is defined: CF and AF are the
borrows out of the whole value and out of the low four bits, OF says the signed result differs
from the true signed difference.
-/

namespace X86Proofs

/-- Result and flags of `x - y`. -/
def subSpec {n : Nat} (x y : BitVec n) : BitVec n × StatusFlags :=
  let r := x - y
  (r, { OF := decide (r.toInt ≠ x.toInt - y.toInt), CF := decide (x.toNat < y.toNat),
        SF := r.msb, ZF := r == 0, PF := evenParity (r.extractLsb' 0 8),
        AF := decide ((x.extractLsb' 0 4).toNat < (y.extractLsb' 0 4).toNat) })

open X86 X86.Helpers

theorem ofInt_sub_toNat {n : Nat} (x y : BitVec n) :
    BitVec.ofInt n ((x.toNat : Int) - (y.toNat : Int)) = x - y := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.ofInt_natCast,
    BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    BitVec.setWidth_eq, BitVec.sub_eq_add_neg]

theorem ofInt4_sub_toNat {n : Nat} (x y : BitVec n) (hn : 4 ≤ n) :
    BitVec.ofInt 4 ((x.toNat : Int) - (y.toNat : Int)) = (x - y).extractLsb' 0 4 := by
  apply BitVec.eq_of_toNat_eq
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.ofInt_natCast,
    BitVec.ofInt_natCast, ← BitVec.sub_eq_add_neg]
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  have hx := x.isLt
  have hy := y.isLt
  obtain ⟨k, hk⟩ : 16 ∣ 2^n := by
    rw [show (16 : Nat) = 2^4 from rfl]; exact Nat.pow_dvd_pow 2 hn
  rw [Nat.mod_mod_of_dvd _ (by rw [hk]; exact ⟨k, rfl⟩ : 2^4 ∣ 2^n)]
  rw [hk] at hx hy ⊢
  omega

theorem toNat_sub_eq_iff {n : Nat} (x y : BitVec n) :
    ((x - y).toNat : Int) = (x.toNat : Int) - y.toNat ↔ ¬ x.toNat < y.toNat := by
  have hx := x.isLt
  have hy := y.isLt
  rw [BitVec.toNat_sub]
  by_cases h : y.toNat ≤ x.toNat
  · rw [show 2^n - y.toNat + x.toNat = (x.toNat - y.toNat) + 2^n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem toNat_sub_mod16_eq_iff {n : Nat} (x y : BitVec n) (hn : 4 ≤ n) :
    ((x - y).toNat : Int) % 16 = (x.toNat : Int) % 16 - (y.toNat : Int) % 16 ↔
      ¬ x.toNat % 16 < y.toNat % 16 := by
  have hx := x.isLt
  have hy := y.isLt
  obtain ⟨k, hk⟩ : 16 ∣ 2^n := by
    rw [show (16 : Nat) = 2^4 from rfl]; exact Nat.pow_dvd_pow 2 hn
  rw [BitVec.toNat_sub]
  rw [hk] at hx hy ⊢
  have hm := Nat.mod_mod_of_dvd (16 * k - y.toNat + x.toNat) (⟨k, rfl⟩ : 16 ∣ 16 * k)
  generalize (16 * k - y.toNat + x.toNat) % (16 * k) = m at hm ⊢
  omega

set_option maxHeartbeats 1000000 in
theorem sub_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x y : BitVec n) :
    (X86.Instructions.Operations.SUB n x y).run s =
      let (r, flags) := subSpec x y
      (.ok r, setFlags s flags) := by
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.SUB
    simp only [isParityEven8_run]
    repeat spec_bind_rfl
    simp [x86_runtime, ofInt_sub_toNat, ofInt4_sub_toNat, toNat_sub_eq_iff, toNat_sub_mod16_eq_iff,
      -BitVec.toInt_sub, -BitVec.toNat_sub, extractLsb'_msb, beq_zero_eq_decide, setFlags,
      StatusFlags.store, subSpec]
    congr 2
    rw [ite_zero_one, ite_zero_one, ite_zero_one, ite_one_zero, ite_one_zero]
    simp only [← Nat.not_le, decide_not, Bool.decide_eq_true]

end X86Proofs
