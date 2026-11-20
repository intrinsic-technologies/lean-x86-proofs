import X86Proofs.Instructions.Bsf.Operation

/-!
# BSR specification

`BSR DEST, SRC` (bit scan reverse): for a non-zero source, `ZF ← 0` and `DEST` is the index of
the highest set bit (`temp ← OperandSize - 1; WHILE Bit(SRC, temp) = 0 DO temp ← temp - 1;
DEST ← temp`, `highestSetBit`). For a zero source, `ZF ← 1` and the destination is left
unchanged, the discarded result drawn from the oracle, as for BSF; the flags are BSF's
(`bitScanFlags`, `Bsf/Operation.lean`). lean-x86 computes the index as
`OperandSize - 1 - leadingZeros`.
-/

namespace X86Proofs

/-- Result and flags of `bsr x`: the index of the highest set bit of `x` (written only for a
non-zero `x`). -/
def bsrSpec {n : Nat} (x : BitVec n) : BitVec n × StatusFlags :=
  (BitVec.ofNat n (highestSetBit x), bitScanFlags x)

open X86 X86.Helpers

theorem bsr_operation {σ : Type} (s : X86.State σ) (n : Nat) (hn : n = 16 ∨ n = 32 ∨ n = 64)
    (x : BitVec n) :
    (X86.Instructions.Operations.BSR n x).run s =
      (.ok ((if x = 0 then (s.oracle.take n).1 else (bsrSpec x).1), x != 0),
        setFlags { s with oracle := oracleSkip s.oracle (if x = 0 then n else 0) }
          (bsrSpec x).2) := by
  rcases hn with rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.BSR
    simp only [x86_runtime, pure_bind, countLeadingZeroBits_run, isParityOdd_run]
    by_cases hx : x = 0
    · subst hx
      simp only [beq_self_eq_true, ↓reduceIte]
      repeat spec_bind_rfl
      simp only [bsrSpec, bitScanFlags]
      generalize oddBits _ = p
      rw [setFlags_eq_of_store]
      · rfl
      · rflags_ext
    · obtain ⟨hlt, hlz⟩ := highestSetBit_of_ne_zero x hx
      simp only [beq_eq_false_iff_ne.mpr hx, hx, ↓reduceIte, bne_iff_ne.mpr hx]
      repeat spec_bind_rfl
      simp only [bsrSpec, bitScanFlags, Int.pow_zero, Int.ediv_one, hlz]
      rw [show BitVec.ofInt _ (_ - ((_ - 1 - highestSetBit x : Nat) : Int)) =
          BitVec.ofNat _ (highestSetBit x) by
        rw [← BitVec.ofInt_natCast]
        congr 1
        omega]
      generalize oddBits _ = p
      rw [setFlags_eq_of_store]
      · rfl
      · rflags_ext

end X86Proofs
