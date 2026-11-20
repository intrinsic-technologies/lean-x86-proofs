import X86Proofs.Core.Run
import X86Proofs.Core.Oracle
import X86Proofs.Instructions.And.Operation

/-!
# TEST specification

TEST is AND without the write-back: it computes `x AND y` only for its flags. So `testSpec` is
the flags of `andSpec`; Intel leaves AF unspecified, so the caller passes the bit lean-x86's
oracle supplies.
-/

namespace X86Proofs

/-- Flags of `test x, y`: those of `x AND y`; `af` is the unspecified auxiliary-carry bit. -/
def testSpec {n : Nat} (af : Bool) (x y : BitVec n) : StatusFlags := (andSpec af x y).2

open X86 X86.Helpers

theorem test_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x y : BitVec n) :
    (X86.Instructions.Operations.TEST n x y).run s =
      (.ok (), setFlags { s with oracle := oracleSkip s.oracle 1 }
        (testSpec (oracleBit s.oracle) x y)) := by
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.TEST
    simp only [isParityEven8_run]
    repeat spec_bind_rfl
    rw [← specM_bind_pure_unit_run]
    spec_bind_rfl
    simp [-BitVec.msb_and, extractLsb'_msb, beq_zero_eq_decide, oracleTake_match_eq_oracleTakeCount, oracleTakeGo_one,
      oracleSkip, testSpec, andSpec, setFlags, StatusFlags.store]
    congr 2
    rw [ite_one_zero, ite_one_zero]
    simp

end X86Proofs
