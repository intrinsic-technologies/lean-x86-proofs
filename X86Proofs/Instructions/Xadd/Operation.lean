import X86Proofs.Instructions.Add.Operation

/-!
# XADD specification

`XADD DEST, SRC` (Intel SDM): `TEMP ← SRC + DEST; SRC ← DEST; DEST ← TEMP`. The flags are those of
the addition (as ADD's, `addSpec`). `xaddSpec x y` gives the new DEST, the new SRC and the flags
for DEST `x` and SRC `y`.
-/

namespace X86Proofs

/-- The new DEST (`x + y`), the new SRC (`x`) and the flags of `xadd x, y`. -/
def xaddSpec {n : Nat} (x y : BitVec n) : BitVec n × BitVec n × StatusFlags :=
  ((addSpec x y).1, x, (addSpec x y).2)

open X86 X86.Helpers

set_option maxHeartbeats 1000000 in
theorem xadd_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x y : BitVec n) :
    (X86.Instructions.Operations.XADD n x y).run s =
      (.ok ((xaddSpec x y).1, (xaddSpec x y).2.1), setFlags s (xaddSpec x y).2.2) := by
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.XADD
    simp only [isParityEven8_run]
    repeat spec_bind_rfl
    simp [x86_runtime, ofInt_add_toNat, ofInt4_add_toNat, natCast_eq_add, natCast_mod16_eq,
      -BitVec.toInt_add, -BitVec.toNat_add, extractLsb'_msb, beq_zero_eq_decide, setFlags,
      StatusFlags.store, xaddSpec, addSpec]
    congr 2
    rw [ite_zero_one, ite_zero_one, ite_zero_one, ite_one_zero, ite_one_zero]
    simp

end X86Proofs
