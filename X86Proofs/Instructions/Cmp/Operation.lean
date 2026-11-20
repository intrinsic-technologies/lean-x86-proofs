import X86Proofs.Instructions.Sub.Operation

/-!
# CMP specification

CMP is SUB without the write-back: it computes `x - y` only for its flags. So `cmpSpec` is the
flags of `subSpec`, and every flag is defined (see `Sub/Operation.lean`).
-/

namespace X86Proofs

/-- Flags of `cmp x, y`: those of `x - y`. -/
def cmpSpec {n : Nat} (x y : BitVec n) : StatusFlags := (subSpec x y).2

open X86 X86.Helpers

set_option maxHeartbeats 1000000 in
theorem cmp_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x y : BitVec n) :
    (X86.Instructions.Operations.CMP n x y).run s = (.ok (), setFlags s (cmpSpec x y)) := by
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.CMP
    simp only [isParityEven8_run]
    repeat spec_bind_rfl
    rw [← specM_bind_pure_unit_run]
    spec_bind_rfl
    simp [x86_runtime, ofInt_sub_toNat, ofInt4_sub_toNat, toNat_sub_eq_iff, toNat_sub_mod16_eq_iff,
      -BitVec.toInt_sub, -BitVec.toNat_sub, extractLsb'_msb, beq_zero_eq_decide, setFlags,
      StatusFlags.store, cmpSpec, subSpec]
    congr 2
    rw [ite_zero_one, ite_zero_one, ite_zero_one, ite_one_zero, ite_one_zero]
    simp only [← Nat.not_le, decide_not, Bool.decide_eq_true]

open scoped X86.Runtime.Syntax in
theorem cmp_flags_run {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x y : BitVec n) :
    (do
      let (result, carry_out, overflow, alternative_carry) ← Subtract (size := (n : Int)) x y
      RFLAGS.setOF overflow
      RFLAGS.setSF (← result[(n : Int) - 1 +: 1])
      RFLAGS.setZF (← Bit (← Std.Bits.Is_Zero (size := (n : Int)) result))
      RFLAGS.setAF alternative_carry
      RFLAGS.setPF (← Bit (← Std.Bits.Is_Parity_Even (size := 8) (← result[0 +: 8])))
      RFLAGS.setCF carry_out : X86.Runtime.SpecM X86.Exception (X86.State σ) Unit).run s =
      (.ok (), setFlags s (cmpSpec x y)) := by
  have h := cmp_operation s n hn x y
  unfold X86.Instructions.Operations.CMP at h
  rw [assert_of_true (by rcases hn with rfl | rfl | rfl | rfl <;> decide), pure_bind] at h
  exact h

theorem cmpSpec_ZF {n : Nat} (x y : BitVec n) : (cmpSpec x y).ZF = (x == y) := by
  simp only [cmpSpec, subSpec]
  by_cases h : x = y
  · simp [h]
  · have hne : x - y ≠ 0 := fun he => h (by
      rw [← BitVec.sub_add_cancel x y, he]
      exact BitVec.zero_add _)
    rw [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr h]

end X86Proofs
