import X86Proofs.Core.Bits
import X86Proofs.Program.Effect

/-!
# LZCNT specification

`LZCNT DEST, SRC`: `DEST ← ` the number of leading zero bits of `SRC` (`leadingZeros`; the
operand size for a zero source). `CF ← (SRC = 0)`, `ZF ← (DEST = 0)`; OF, SF, AF and PF are
undefined: lean-x86 draws them from its oracle in the order OF, SF, AF, PF, and the spec takes them
as `u 0`, `u 1`, `u 2`, `u 3`. `lzcntFlags` is the same as a `StatusFlagsOutcome`, the undefined
flags `none`. The instruction exists only if CPUID reports LZCNT (`F3 0F BD` is BSR otherwise).
-/

namespace X86Proofs

/-- Result and flags of `lzcnt x`, with `u` the unspecified bits for OF, SF, AF, PF. -/
def lzcntSpec {n : Nat} (u : Nat → Bool) (x : BitVec n) : BitVec n × StatusFlags :=
  let r := BitVec.ofNat n (leadingZeros x)
  (r, { CF := x == 0, PF := u 3, AF := u 2, ZF := r == 0, SF := u 1, OF := u 0 })

/-- What LZCNT does to the flags: CF is whether the source is zero, ZF whether the result is; OF,
SF, AF and PF are undefined. -/
def lzcntFlags {n : Nat} (x : BitVec n) : StatusFlagsOutcome :=
  { CF := some (x == 0), PF := none, AF := none, ZF := some (BitVec.ofNat n (leadingZeros x) == 0),
    SF := none, OF := none }

theorem lzcntFlags_allows {n : Nat} (u : Nat → Bool) (x : BitVec n) :
    (lzcntFlags x).Allows (lzcntSpec u x).2 :=
  ⟨rfl, trivial, trivial, rfl, trivial, trivial⟩

open X86 X86.Helpers

theorem lzcnt_operation {σ : Type} (s : X86.State σ) (n : Nat) (hn : n = 16 ∨ n = 32 ∨ n = 64)
    (x : BitVec n) :
    (X86.Instructions.Operations.LZCNT n x).run s =
      let r := lzcntSpec (fun i => oracleBit (oracleSkip s.oracle i)) x
      (.ok r.1, setFlags { s with oracle := oracleSkip s.oracle 4 } r.2) := by
  rcases hn with rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.LZCNT
    simp only [x86_runtime, pure_bind, countLeadingZeroBits_run]
    repeat spec_bind_rfl
    simp only [lzcntSpec, Int.pow_zero, Int.ediv_one, BitVec.ofInt_natCast]
    rw [setFlags_eq_of_store]
    · rfl
    · rflags_ext

end X86Proofs
