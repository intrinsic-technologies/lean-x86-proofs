import X86Proofs.Core.Bits
import X86Proofs.Program.Effect

/-!
# BT specification

`BT BitBase, BitOffset`: `CF ← Bit(BitBase, BitOffset)`; the bit base is only read. With a
register bit base, or an immediate offset, the offset is taken modulo the operand size
(`bitOffset`). OF, SF, AF and PF are undefined: lean-x86 draws them from its oracle in the order
OF, SF, AF, PF, and the spec takes them as `u 0`, `u 1`, `u 2`, `u 3`. ZF is unaffected, so the
spec takes the flags before the instruction `f` and keeps `f.ZF`. `btFlags` is the same as a
`StatusFlagsOutcome`, the undefined flags `none`. BTS, BTR and BTC set the flags the same way and
write the bit base (`Bts/`, `Btr/`, `Btc/`).
-/

namespace X86Proofs

/-- The bit an offset `y` selects in an `n`-bit bit base: `y` modulo the operand size. -/
def bitOffset {n : Nat} (y : BitVec n) : Nat := y.toNat % n

/-- Flags of `bt x, y`: CF is the selected bit, ZF unchanged from `f`, and `u` the unspecified
bits for OF, SF, AF, PF (in that order). -/
def btSpec {n : Nat} (u : Nat → Bool) (f : StatusFlags) (x y : BitVec n) : StatusFlags :=
  { f with CF := x.getLsbD (bitOffset y), OF := u 0, SF := u 1, AF := u 2, PF := u 3 }

/-- What BT, BTS, BTR and BTC do to the flags: CF is the selected bit, ZF is kept, OF, SF, AF and
PF are undefined. -/
def btFlags {n : Nat} (f : StatusFlags) (x y : BitVec n) : StatusFlagsOutcome :=
  { CF := some (x.getLsbD (bitOffset y)), ZF := some f.ZF, OF := none, SF := none, AF := none,
    PF := none }

theorem btFlags_allows {n : Nat} (u : Nat → Bool) (f : StatusFlags) (x y : BitVec n) :
    (btFlags f x y).Allows (btSpec u f x y) :=
  ⟨rfl, trivial, trivial, rfl, trivial, trivial⟩

open X86 X86.Helpers

theorem bt_operation {σ : Type} (s : X86.State σ) (n : Nat) (hn : n = 16 ∨ n = 32 ∨ n = 64)
    (x y : BitVec n) :
    (X86.Instructions.Operations.BT n x y).run s =
      (.ok (), setFlags { s with oracle := oracleSkip s.oracle 4 }
        (btSpec (fun i => oracleBit (oracleSkip s.oracle i)) (StatusFlags.ofRFLAGS s.RFLAGS)
          x y)) := by
  have hk : y.toNat % n < n := Nat.mod_lt _ (by omega)
  rcases hn with rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.BT
    simp (disch := omega) only [x86_runtime, pure_bind]
    repeat spec_bind_rfl
    simp (disch := omega) only [btSpec, bitOffset, Int.toNat_emod, Int.toNat_natCast,
      Int.reduceToNat]
    rw [setFlags_eq_of_store]
    · rfl
    · rflags_ext

attribute [x86_compose] btFlags bitOffset

end X86Proofs
