import X86Proofs.Core.Run
import X86Proofs.Core.Oracle
import X86Proofs.Core.Flags

/-!
# ADD specification

A pure function: no state, no failure, no oracle. Every flag is defined; each carry or overflow
flag says the result differs from the true sum (unsigned for CF, signed for OF, the low four
bits for AF).
-/

namespace X86Proofs

/-- Result and flags of `x + y`. -/
def addSpec {n : Nat} (x y : BitVec n) : BitVec n × StatusFlags :=
  let r := x + y
  (r, { OF := decide (r.toInt ≠ x.toInt + y.toInt), CF := decide (r.toNat ≠ x.toNat + y.toNat),
        SF := r.msb, ZF := r == 0, PF := evenParity (r.extractLsb' 0 8),
        AF := decide ((r.extractLsb' 0 4).toNat ≠
          (x.extractLsb' 0 4).toNat + (y.extractLsb' 0 4).toNat) })

open X86 X86.Helpers

theorem ofInt_add_toNat {n : Nat} (x y : BitVec n) :
    BitVec.ofInt n ((x.toNat : Int) + (y.toNat : Int)) = x + y := by
  rw [show (x.toNat : Int) + y.toNat = ((x.toNat + y.toNat : Nat) : Int) by push_cast; rfl,
    BitVec.ofInt_natCast, BitVec.add_def]

theorem ofInt4_add_toNat {n : Nat} (x y : BitVec n) (hn : 4 ≤ n) :
    BitVec.ofInt 4 ((x.toNat : Int) + (y.toNat : Int)) = (x + y).extractLsb' 0 4 := by
  rw [show (x.toNat : Int) + y.toNat = ((x.toNat + y.toNat : Nat) : Int) by push_cast; rfl,
    BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, BitVec.toNat_add, Nat.shiftRight_zero]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hn)]

theorem natCast_eq_add {a b c : Nat} : ((a : Int) = b + c) ↔ a = b + c := by omega

theorem natCast_mod16_eq {a b c : Nat} :
    ((a : Int) % 16 = b % 16 + c % 16) ↔ a % 16 = b % 16 + c % 16 := by omega

set_option maxHeartbeats 1000000 in
theorem add_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x y : BitVec n) :
    (X86.Instructions.Operations.ADD n x y).run s =
      let (r, flags) := addSpec x y
      (.ok r, setFlags s flags) := by
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.ADD
    simp only [isParityEven8_run]
    repeat spec_bind_rfl
    simp [x86_runtime, ofInt_add_toNat, ofInt4_add_toNat, natCast_eq_add, natCast_mod16_eq,
      -BitVec.toInt_add, -BitVec.toNat_add, extractLsb'_msb, beq_zero_eq_decide, setFlags,
      StatusFlags.store, addSpec]
    congr 2
    rw [ite_zero_one, ite_zero_one, ite_zero_one, ite_one_zero, ite_one_zero]
    simp

end X86Proofs
