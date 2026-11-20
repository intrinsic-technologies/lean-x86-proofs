import X86Proofs.Core.Run
import X86Proofs.Core.Flags

/-!
# DEC specification

A pure function: no state, no failure, no oracle. DEC writes OF, SF, ZF, AF and PF and leaves CF
alone, so the caller passes the flags before the instruction and CF is taken from them. OF says
the signed result differs from the true signed difference, AF that the low four bits borrow
(they are zero).
-/

namespace X86Proofs

/-- Result and flags of `x - 1`, from the flags `f` before (CF stays `f.CF`). -/
def decSpec {n : Nat} (f : StatusFlags) (x : BitVec n) : BitVec n × StatusFlags :=
  let r := x - 1
  (r, { OF := decide (r.toInt ≠ x.toInt - 1), CF := f.CF,
        SF := r.msb, ZF := r == 0, PF := evenParity (r.extractLsb' 0 8),
        AF := x.extractLsb' 0 4 == 0 })

open X86 X86.Helpers

theorem ofInt_toNat_sub_one {n : Nat} (x : BitVec n) :
    BitVec.ofInt n ((x.toNat : Int) - 1) = x - 1 := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.ofInt_natCast,
    BitVec.ofNat_toNat, BitVec.setWidth_eq, ← BitVec.sub_eq_add_neg]
  rfl

theorem dec_af_iff {n : Nat} (x : BitVec n) :
    (max (((x.toNat : Int) - 1) % 16) 0 = (x.toNat : Int) % 16 - 1) ↔
      ¬ x.extractLsb' 0 4 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.extractLsb'_toNat]
  show _ ↔ ¬ x.toNat >>> 0 % 2 ^ 4 = 0
  rw [Nat.shiftRight_zero]
  omega

theorem dec_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x : BitVec n) :
    (X86.Instructions.Operations.DEC n x).run s =
      let (r, flags) := decSpec (StatusFlags.ofRFLAGS s.RFLAGS) x
      (.ok r, setFlags s flags) := by
  simp only [setFlags]
  rw [StatusFlags.store_of_cf_eq _ _ rfl]
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.DEC
    simp only [isParityEven8_run]
    repeat spec_bind_rfl
    simp [x86_runtime, extractLsb'_msb, beq_zero_eq_decide, decSpec, ofInt_toNat_sub_one,
      dec_af_iff, -BitVec.toInt_sub, -BitVec.toNat_sub]
    repeat rw [ite_zero_one]
    repeat rw [ite_one_zero]
    simp

end X86Proofs
