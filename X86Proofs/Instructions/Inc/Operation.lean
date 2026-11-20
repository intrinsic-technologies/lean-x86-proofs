import X86Proofs.Core.Run
import X86Proofs.Core.Flags

/-!
# INC specification

A pure function: no state, no failure, no oracle. INC writes OF, SF, ZF, AF and PF and leaves CF
alone, so the caller passes the flags before the instruction and CF is taken from them. OF says
the signed result differs from the true signed sum, AF that the low four bits carry.
-/

namespace X86Proofs

/-- Result and flags of `x + 1`, from the flags `f` before (CF stays `f.CF`). -/
def incSpec {n : Nat} (f : StatusFlags) (x : BitVec n) : BitVec n × StatusFlags :=
  let r := x + 1
  (r, { OF := decide (r.toInt ≠ x.toInt + 1), CF := f.CF,
        SF := r.msb, ZF := r == 0, PF := evenParity (r.extractLsb' 0 8),
        AF := decide ((r.extractLsb' 0 4).toNat ≠ (x.extractLsb' 0 4).toNat + 1) })

open X86 X86.Helpers

theorem ofInt_toNat_add_one {n : Nat} (x : BitVec n) :
    BitVec.ofInt n ((x.toNat : Int) + 1) = x + 1 := by
  rw [show (x.toNat : Int) + 1 = ((x.toNat + 1 : Nat) : Int) by push_cast; rfl,
    BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

theorem ofInt4_toNat_add_one {n : Nat} (x : BitVec n) (hn : 4 ≤ n) :
    BitVec.ofInt 4 ((x.toNat : Int) + 1) = (x + 1).extractLsb' 0 4 := by
  rw [show (x.toNat : Int) + 1 = ((x.toNat + 1 : Nat) : Int) by push_cast; rfl,
    BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, BitVec.toNat_add, Nat.shiftRight_zero]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hn),
    show (1 : BitVec n).toNat = 1 from BitVec.toNat_one (by omega)]

theorem natCast_mod16_eq_add_one {a b : Nat} :
    ((a : Int) % 16 = (b : Int) % 16 + 1) ↔ a % 16 = b % 16 + 1 := by omega

theorem inc_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x : BitVec n) :
    (X86.Instructions.Operations.INC n x).run s =
      let (r, flags) := incSpec (StatusFlags.ofRFLAGS s.RFLAGS) x
      (.ok r, setFlags s flags) := by
  simp only [setFlags]
  rw [StatusFlags.store_of_cf_eq _ _ rfl]
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.INC
    simp only [isParityEven8_run]
    repeat spec_bind_rfl
    simp [x86_runtime, extractLsb'_msb, beq_zero_eq_decide, incSpec, ofInt_toNat_add_one,
      ofInt4_toNat_add_one, natCast_mod16_eq_add_one, -BitVec.toInt_add, -BitVec.toNat_add]
    rw [ite_zero_one, ite_zero_one, ite_one_zero, ite_one_zero]
    simp

end X86Proofs
