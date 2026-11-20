import X86Proofs.Instructions.Sub.Operation

/-!
# SBB specification

A pure function: no state, no failure, no oracle. SBB subtracts the source and the carry flag
`cf` from before the instruction (the borrow in), so the caller passes it. Every flag is defined,
as for SUB: CF and AF are the borrows out of the whole value and out of the low four bits, OF
says the signed result differs from the true signed difference `x - (y + cf)`.
-/

namespace X86Proofs

/-- Result and flags of `x - (y + cf)`. -/
def sbbSpec {n : Nat} (cf : Bool) (x y : BitVec n) : BitVec n × StatusFlags :=
  let r := x - (y + BitVec.ofNat n cf.toNat)
  (r, { OF := decide (r.toInt ≠ x.toInt - (y.toInt + cf.toNat)),
        CF := decide (x.toNat < y.toNat + cf.toNat),
        SF := r.msb, ZF := r == 0, PF := evenParity (r.extractLsb' 0 8),
        AF := decide ((x.extractLsb' 0 4).toNat < (y.extractLsb' 0 4).toNat + cf.toNat) })

open X86 X86.Helpers

theorem ofInt_sub_add_toNat {n : Nat} (x y : BitVec n) (c : Nat) :
    BitVec.ofInt n ((x.toNat : Int) - ((y.toNat : Int) + (c : Int))) = x - (y + BitVec.ofNat n c) := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg,
    show (y.toNat : Int) + c = ((y.toNat + c : Nat) : Int) by push_cast; rfl,
    BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    ← BitVec.sub_eq_add_neg]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

theorem toNat_sub_add_eq_iff {n : Nat} (x y : BitVec n) (c : Nat) :
    (((x - (y + BitVec.ofNat n c)).toNat : Int) = (x.toNat : Int) - ((y.toNat : Int) + c)) ↔
      ¬ x.toNat < y.toNat + c := by
  rw [← ofInt_sub_add_toNat, BitVec.toNat_ofInt]
  have hx := x.isLt
  have hM : (0 : Int) < ((2 ^ n : Nat) : Int) := by have := Nat.two_pow_pos n; omega
  by_cases h : y.toNat + c ≤ x.toNat
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  · have := Int.emod_nonneg ((x.toNat : Int) - ((y.toNat : Int) + c)) (by omega : ((2 ^ n : Nat) : Int) ≠ 0)
    omega

theorem int_sub_mod16_eq_iff {a b c : Nat} :
    (max (((a : Int) - ((b : Int) + c)) % 16) 0 = (a : Int) % 16 - ((b : Int) % 16 + c)) ↔
      ¬ a % 16 < b % 16 + c := by omega

set_option maxHeartbeats 1000000 in
theorem sbb_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x y : BitVec n) :
    (X86.Instructions.Operations.SBB n x y).run s =
      let (r, flags) := sbbSpec (StatusFlags.ofRFLAGS s.RFLAGS).CF x y
      (.ok r, setFlags s flags) := by
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.SBB
    spec_bind_rfl
    spec_bind_with rflagsCF_run s
    generalize (StatusFlags.ofRFLAGS s.RFLAGS).CF = c
    simp only [isParityEven8_run]
    repeat spec_bind_rfl
    simp only [unsigned_ofBool]
    simp [x86_runtime, ofInt_sub_add_toNat, toNat_sub_add_eq_iff, int_sub_mod16_eq_iff,
      -BitVec.toInt_sub, -BitVec.toNat_sub, extractLsb'_msb, beq_zero_eq_decide, setFlags,
      StatusFlags.store, sbbSpec]
    congr 2
    rw [ite_zero_one, ite_zero_one, ite_zero_one, ite_one_zero, ite_one_zero]
    simp only [← Nat.not_le, decide_not, Bool.decide_eq_true]

end X86Proofs
