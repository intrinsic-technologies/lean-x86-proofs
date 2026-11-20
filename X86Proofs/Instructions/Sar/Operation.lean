import X86Proofs.Core.Shift
import X86Proofs.Program.Effect
import X86Proofs.Program.ComposeAttr

/-!
# SAR specification

A pure function of the masked count `c` (see `shiftCount`): the result is `x.sshiftRight c` (the
vacated top bits filled with the sign bit). The flags depend on the count:

- `c = 0`: no flag changes; the spec returns the old flags `old`.
- `c ≥ 1`: CF is the last bit shifted out (bit 0 of `x.sshiftRight (c - 1)`); SF, ZF, PF from the
  result; AF undefined (the caller passes lean-x86's oracle bit, `af`); OF is cleared for `c = 1`
  and undefined otherwise (`of`).

`sarFlags` is the same as a `StatusFlagsOutcome`: for `c = 0` every flag is `some` of its old
value; the undefined flags are `none`.
-/

namespace X86Proofs

/-- Result and flags of shifting `x` right (arithmetically) by the masked count `c`. `old` are
the flags before; `of` and `af` are the unspecified OF (for `c ≥ 2`) and AF bits. -/
def sarSpec {n : Nat} (old : StatusFlags) (of af : Bool) (c : Nat) (x : BitVec n) :
    BitVec n × StatusFlags :=
  let r := x.sshiftRight c
  let cf := (x.sshiftRight (c - 1)).getLsbD 0
  (r, if c = 0 then old else
    { CF := cf, PF := evenParity (r.extractLsb' 0 8), AF := af, ZF := r == 0, SF := r.msb,
      OF := if c = 1 then false else of })

/-- Oracle bits SAR uses for count `c`: none for 0, one (AF) for 1, two (OF, then AF) for more. -/
def sarOracleBits (c : Nat) : Nat := if c = 0 then 0 else if c = 1 then 1 else 2

/-- The oracle bit lean-x86's SAR by count `c` takes for AF from oracle `o`: the next bit for
`c = 1`; for `c ≥ 2` the one after, since OF takes the next. -/
def sarOracleAF (o : X86.Runtime.Oracle) (c : Nat) : Bool :=
  if c = 1 then oracleBit o else oracleBit (oracleSkip o 1)

/-- What SAR by count `c` does to the flags, from old flags `old` and operand `x`: nothing for
`c = 0`; else CF is the last bit shifted out, SF, ZF, PF come from the result, AF is undefined, and
OF is cleared for `c = 1` and undefined otherwise. -/
def sarFlags {n : Nat} (old : StatusFlags) (c : Nat) (x : BitVec n) : StatusFlagsOutcome :=
  let r := x.sshiftRight c
  let cf := (x.sshiftRight (c - 1)).getLsbD 0
  if c = 0 then .ofStatusFlags old else
    { CF := some cf, PF := some (evenParity (r.extractLsb' 0 8)), AF := none,
      ZF := some (r == 0), SF := some r.msb, OF := if c = 1 then some false else none }

theorem sarFlags_allows {n : Nat} (old : StatusFlags) (of af : Bool) (c : Nat) (x : BitVec n) :
    (sarFlags old c x).Allows (sarSpec old of af c x).2 := by
  unfold sarFlags sarSpec
  by_cases h0 : c = 0
  · simp only [h0, ↓reduceIte]
    exact StatusFlagsOutcome.allows_ofStatusFlags old
  · by_cases h1 : c = 1 <;>
      simp [h0, h1, StatusFlagsOutcome.Allows, FlagAllows]

open X86 X86.Helpers

theorem sar_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x : BitVec n) (count : BitVec 8) :
    (X86.Instructions.Operations.SAR n x count).run s =
      let c := shiftCount n count
      let (r, flags) := sarSpec (StatusFlags.ofRFLAGS s.RFLAGS) (oracleBit s.oracle)
        (sarOracleAF s.oracle c) c x
      (.ok r, setFlags { s with oracle := oracleSkip s.oracle (sarOracleBits c) } flags) := by
  have hlt := shiftCount_lt_64 n count
  obtain ⟨c, hc⟩ : ∃ c, shiftCount n count = c := ⟨_, rfl⟩
  have hc32 : n ≠ 64 → count.toNat % 32 = c := fun h => by simp [← hc, shiftCount, h]
  have hc64 : n = 64 → count.toNat % 64 = c := fun h => by simp [← hc, shiftCount, h]
  rw [hc] at hlt ⊢
  simp only [sarSpec, sarOracleBits, sarOracleAF]
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.SAR
    simp only [isParityEven8_run]
    repeat spec_bind_rfl
    simp only [Int.cast_ofNat_Int, Int.reduceBEq, Bool.false_eq_true, ↓reduceIte, Int.reduceToNat,
      unsigned_extractLsb', Nat.reducePow]
    first | rw [hc32 (by decide)] | rw [hc64 rfl]
    by_cases h0 : c = 0
    · subst h0
      simp
    have e0 : ((c : Int) != 0) = true := by simp; omega
    simp only [e0, h0, ↓reduceIte]
    spec_bind_rfl
    refine (specM_bind_run _ _ (specM_forIn_run _ _
      (fun _ (acc : BitVec _ × BitVec 1) => (acc.1.sshiftRight 1, acc.1.extractLsb' 0 1)) _ _
      ?_)).trans ?_
    · intro _ _ acc
      rw [shiftRightArithmetic_one_run acc.1 (by decide)]
      rfl
    rw [sar_fold _ _ _ (by omega)]
    generalize x.sshiftRight c = r
    by_cases h1 : c = 1
    · subst h1
      simp only [↓reduceIte]
      rw [setFlags_eq_of_store]
      · rfl
      · rflags_ext
    · have e1 : ((c : Int) == 1) = false := by simp; omega
      simp only [e1, h1, Bool.false_eq_true, ↓reduceIte]
      rw [setFlags_eq_of_store]
      · rfl
      · rflags_ext

attribute [x86_compose] sarFlags

end X86Proofs
