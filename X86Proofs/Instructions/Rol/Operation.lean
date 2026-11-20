import X86Proofs.Core.Shift
import X86Proofs.Program.Effect
import X86Proofs.Program.ComposeAttr

/-!
# ROL specification

A pure function of the masked count `c` (see `shiftCount`): the result is `x.rotateLeft c`. The
flags depend on the count:

- `c = 0`: no flag changes; the spec returns the old flags `old`.
- `c = 1`: CF is the bit rotated into bit 0, OF is CF xor the new top bit; the other flags keep
  their old values.
- `c ≥ 2`: CF as for 1; OF is undefined (the caller passes the bit lean-x86's oracle supplies,
  `of`); the other flags keep their old values.

`rolFlags` is the same as a `StatusFlagsOutcome`: unchanged flags are `some` of their old value, the
undefined OF is `none`.
-/

namespace X86Proofs

/-- Result and flags of rotating `x` left by the masked count `c`. `old` are the flags before,
`of` is the unspecified OF bit for `c ≥ 2`. -/
def rolSpec {n : Nat} (old : StatusFlags) (of : Bool) (c : Nat) (x : BitVec n) : BitVec n × StatusFlags :=
  let r := x.rotateLeft c
  (r, if c = 0 then old else
    { old with CF := r.getLsbD 0, OF := if c = 1 then r.msb ^^ r.getLsbD 0 else of })

/-- Oracle bits ROL uses for count `c`: one (OF) for `c ≥ 2`, none otherwise. -/
def rolOracleBits (c : Nat) : Nat := if c = 0 ∨ c = 1 then 0 else 1

/-- What ROL by count `c` does to the flags, from old flags `old` and operand `x`: nothing for
`c = 0`; else CF is bit 0 of the result, OF (only for `c = 1`) is CF xor the result's top bit and
undefined otherwise, and PF, AF, ZF, SF keep their old values. -/
def rolFlags {n : Nat} (old : StatusFlags) (c : Nat) (x : BitVec n) : StatusFlagsOutcome :=
  let r := x.rotateLeft c
  if c = 0 then .ofStatusFlags old else
    { CF := some (r.getLsbD 0), PF := some old.PF, AF := some old.AF, ZF := some old.ZF,
      SF := some old.SF, OF := if c = 1 then some (r.msb ^^ r.getLsbD 0) else none }

theorem rolFlags_allows {n : Nat} (old : StatusFlags) (of : Bool) (c : Nat) (x : BitVec n) :
    (rolFlags old c x).Allows (rolSpec old of c x).2 := by
  unfold rolFlags rolSpec
  by_cases h0 : c = 0
  · simp only [h0, ↓reduceIte]
    exact StatusFlagsOutcome.allows_ofStatusFlags old
  · by_cases h1 : c = 1 <;>
      simp [h0, h1, StatusFlagsOutcome.Allows, FlagAllows]

open X86 X86.Helpers

theorem rol_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x : BitVec n) (count : BitVec 8) :
    (X86.Instructions.Operations.ROL n x count).run s =
      let c := shiftCount n count
      let (r, flags) := rolSpec (StatusFlags.ofRFLAGS s.RFLAGS) (oracleBit s.oracle) c x
      (.ok r, setFlags { s with oracle := oracleSkip s.oracle (rolOracleBits c) } flags) := by
  have hlt := shiftCount_lt_64 n count
  obtain ⟨c, hc⟩ : ∃ c, shiftCount n count = c := ⟨_, rfl⟩
  have hc32 : n ≠ 64 → count.toNat % 32 = c := fun h => by simp [← hc, shiftCount, h]
  have hc64 : n = 64 → count.toNat % 64 = c := fun h => by simp [← hc, shiftCount, h]
  rw [hc] at hlt ⊢
  simp only [rolSpec, rolOracleBits]
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.ROL
    repeat spec_bind_rfl
    simp only [Int.reduceToNat, Int.reduceSub, Int.reduceAdd, unsigned_extractLsb', Nat.reducePow]
    first | rw [hc32 (by decide)] | rw [hc64 rfl]
    rw [rotateLeft_run_nat _ _ (by decide)]
    generalize x.rotateLeft c = r
    rcases Nat.lt_or_ge c 2 with hc | hc
    · rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
      · simp
      · simp only [Nat.one_ne_zero, ↓reduceIte, or_true, oracleSkip_zero]
        rw [setFlags_eq_of_store]
        · rfl
        · rflags_ext
    · have h0 : c ≠ 0 := by omega
      have h1 : c ≠ 1 := by omega
      have e1 : ((c : Int) == 1) = false := by simp; omega
      have e2 : ((c : Int) != 0) = true := by simp; omega
      simp only [h0, h1, ↓reduceIte, or_self, e1, e2, Bool.false_eq_true]
      rw [setFlags_eq_of_store]
      · rfl
      · rflags_ext

attribute [x86_compose] rolFlags

end X86Proofs
