import X86Proofs.Instructions.Add.Operation

/-!
# ADC specification

A pure function: no state, no failure, no oracle. ADC adds the carry flag `cf` from before the
instruction to the sum, so the caller passes it. Every flag is defined, as for ADD: each carry
or overflow flag says the result differs from the true sum `x + y + cf` (unsigned for CF, signed
for OF, the low four bits for AF).
-/

namespace X86Proofs

/-- Result and flags of `x + y + cf`. -/
def adcSpec {n : Nat} (cf : Bool) (x y : BitVec n) : BitVec n × StatusFlags :=
  let r := x + y + BitVec.ofNat n cf.toNat
  (r, { OF := decide (r.toInt ≠ x.toInt + y.toInt + cf.toNat),
        CF := decide (r.toNat ≠ x.toNat + y.toNat + cf.toNat),
        SF := r.msb, ZF := r == 0, PF := evenParity (r.extractLsb' 0 8),
        AF := decide ((r.extractLsb' 0 4).toNat ≠
          (x.extractLsb' 0 4).toNat + (y.extractLsb' 0 4).toNat + cf.toNat) })

open X86 X86.Helpers

theorem ofInt_add_add_toNat {n : Nat} (x y : BitVec n) (c : Nat) :
    BitVec.ofInt n ((x.toNat : Int) + (y.toNat : Int) + (c : Int)) = x + y + BitVec.ofNat n c := by
  rw [show (x.toNat : Int) + y.toNat + c = ((x.toNat + y.toNat + c : Nat) : Int) by push_cast; rfl,
    BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

theorem ofInt4_add_add_toNat {n : Nat} (x y : BitVec n) (c : Nat) (hn : 4 ≤ n) :
    BitVec.ofInt 4 ((x.toNat : Int) + (y.toNat : Int) + (c : Int)) =
      (x + y + BitVec.ofNat n c).extractLsb' 0 4 := by
  rw [show (x.toNat : Int) + y.toNat + c = ((x.toNat + y.toNat + c : Nat) : Int) by push_cast; rfl,
    BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, BitVec.toNat_add, Nat.shiftRight_zero]
  have h16 : 2 ^ 4 ∣ 2 ^ n := Nat.pow_dvd_pow 2 hn
  rw [Nat.mod_mod_of_dvd _ h16, ← Nat.mod_mod_of_dvd (_ % 2 ^ n + _ % 2 ^ n) h16, ← Nat.add_mod,
    Nat.mod_mod_of_dvd _ h16]

theorem natCast_eq_add_add {a b c d : Nat} : ((a : Int) = b + c + d) ↔ a = b + c + d := by omega

theorem natCast_mod16_eq_add {a b c d : Nat} :
    ((a : Int) % 16 = b % 16 + c % 16 + d) ↔ a % 16 = b % 16 + c % 16 + d := by omega

set_option maxHeartbeats 1000000 in
theorem adc_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x y : BitVec n) :
    (X86.Instructions.Operations.ADC n x y).run s =
      let (r, flags) := adcSpec (StatusFlags.ofRFLAGS s.RFLAGS).CF x y
      (.ok r, setFlags s flags) := by
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.ADC
    spec_bind_rfl
    spec_bind_with rflagsCF_run s
    generalize (StatusFlags.ofRFLAGS s.RFLAGS).CF = c
    simp only [isParityEven8_run]
    repeat spec_bind_rfl
    simp only [unsigned_ofBool]
    simp [x86_runtime, ofInt_add_add_toNat, ofInt4_add_add_toNat, natCast_eq_add_add,
      natCast_mod16_eq_add, -BitVec.toInt_add, -BitVec.toNat_add, extractLsb'_msb,
      beq_zero_eq_decide, setFlags, StatusFlags.store, adcSpec]
    congr 2
    rw [ite_zero_one, ite_zero_one, ite_zero_one, ite_one_zero, ite_one_zero]
    simp

end X86Proofs
