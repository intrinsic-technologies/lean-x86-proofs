import X86Proofs.Core.Run
import X86Proofs.Core.Oracle
import X86Proofs.Core.Flags

/-!
# AND specification

A pure function: no state, no failure, no oracle. Intel leaves AF unspecified after AND, so
the caller passes the bit lean-x86's oracle supplies.
-/

namespace X86Proofs

/-- Result and flags of `x AND y`; `af` is the unspecified auxiliary-carry bit. -/
def andSpec {n : Nat} (af : Bool) (x y : BitVec n) : BitVec n × StatusFlags :=
  let r := x &&& y
  (r, { OF := false, CF := false, SF := r.msb, ZF := r == 0,
        PF := evenParity (r.extractLsb' 0 8), AF := af })

open X86 X86.Helpers

theorem and_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x y : BitVec n) :
    (X86.Instructions.Operations.AND n x y).run s =
      let (r, flags) := andSpec (oracleBit s.oracle) x y
      (.ok r, setFlags { s with oracle := oracleSkip s.oracle 1 } flags) := by
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.AND
    simp only [isParityEven8_run]
    repeat spec_bind_rfl
    simp [-BitVec.msb_and, extractLsb'_msb, beq_zero_eq_decide, oracleTake_match_eq_oracleTakeCount, oracleTakeGo_one, oracleSkip, andSpec,
      setFlags, StatusFlags.store]
    congr 2
    rw [ite_one_zero, ite_one_zero]
    simp

end X86Proofs
