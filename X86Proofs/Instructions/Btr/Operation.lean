import X86Proofs.Instructions.Bt.Operation

/-!
# BTR specification

`BTR BitBase, BitOffset`: `CF ← Bit(BitBase, BitOffset); Bit(BitBase, BitOffset) ← 0`. The offset is
taken modulo the operand size (`bitOffset`), and the flags are BT's (`btSpec`, `btFlags` in
`Bt/Operation.lean`: CF the selected bit before the write, ZF unchanged, OF, SF, AF and PF
undefined).
-/

namespace X86Proofs

/-- Result and flags of `btr x, y`: `x` with the selected bit cleared, and BT's flags. -/
def btrSpec {n : Nat} (u : Nat → Bool) (f : StatusFlags) (x y : BitVec n) :
    BitVec n × StatusFlags :=
  (x &&& ~~~BitVec.twoPow n (bitOffset y), btSpec u f x y)

open X86 X86.Helpers

theorem btr_operation {σ : Type} (s : X86.State σ) (n : Nat) (hn : n = 16 ∨ n = 32 ∨ n = 64)
    (x y : BitVec n) :
    (X86.Instructions.Operations.BTR n x y).run s =
      let r := btrSpec (fun i => oracleBit (oracleSkip s.oracle i)) (StatusFlags.ofRFLAGS s.RFLAGS)
        x y
      (.ok r.1, setFlags { s with oracle := oracleSkip s.oracle 4 } r.2) := by
  have hk : y.toNat % n < n := Nat.mod_lt _ (by omega)
  rcases hn with rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.BTR
    simp (disch := first | omega | (simp only [decide_eq_true_eq]; omega)) only [x86_runtime,
      pure_bind]
    repeat spec_bind_rfl
    simp (disch := omega) only [btrSpec, btSpec, bitOffset, Int.toNat_emod, Int.toNat_natCast,
      Int.reduceToNat, setSlice_one_zero]
    rw [setFlags_eq_of_store]
    · rfl
    · rflags_ext

end X86Proofs
