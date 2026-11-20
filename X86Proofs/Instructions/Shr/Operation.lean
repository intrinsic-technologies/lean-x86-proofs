import X86Proofs.Core.Shift
import X86Proofs.Program.Effect
import X86Proofs.Program.ComposeAttr

/-!
# SHR specification

A pure function of the masked count `c` (see `shiftCount`): the result is `x >>> c`. The flags
depend on the count:

- `c = 0`: no flag changes; the spec returns the old flags `old`.
- `c ≥ 1`: CF is the last bit shifted out (bit `c - 1` of `x`); SF, ZF, PF from the result; AF
  undefined (the caller passes lean-x86's oracle bit, `af`); OF is the top bit of `x` for `c = 1`
  and undefined otherwise (`of`).

`shrFlags` is the same as a `StatusFlagsOutcome`: for `c = 0` every flag is `some` of its old value; the
undefined flags are `none`.
-/

namespace X86Proofs

/-- Result and flags of shifting `x` right (logically) by the masked count `c`. `old` are the
flags before; `of` and `af` are the unspecified OF (for `c ≥ 2`) and AF bits. -/
def shrSpec {n : Nat} (old : StatusFlags) (of af : Bool) (c : Nat) (x : BitVec n) : BitVec n × StatusFlags :=
  let r := x >>> c
  (r, if c = 0 then old else
    { CF := x.getLsbD (c - 1), PF := evenParity (r.extractLsb' 0 8), AF := af, ZF := r == 0,
      SF := r.msb, OF := if c = 1 then x.msb else of })

/-- Oracle bits SHR uses for count `c`: none for 0, one (AF) for 1, two (OF, then AF) for more. -/
def shrOracleBits (c : Nat) : Nat := if c = 0 then 0 else if c = 1 then 1 else 2

/-- The oracle bit lean-x86's SHR by count `c` takes for AF from oracle `o`: the next bit for
`c = 1`; for `c ≥ 2` the one after, since OF takes the next. -/
def shrOracleAF (o : X86.Runtime.Oracle) (c : Nat) : Bool :=
  if c = 1 then oracleBit o else oracleBit (oracleSkip o 1)

/-- What SHR by count `c` does to the flags, from old flags `old` and operand `x`: nothing for
`c = 0`; else CF is the last bit shifted out, SF, ZF, PF come from the result, AF is undefined, and
OF is the top bit of `x` for `c = 1` and undefined otherwise. -/
def shrFlags {n : Nat} (old : StatusFlags) (c : Nat) (x : BitVec n) : StatusFlagsOutcome :=
  let r := x >>> c
  if c = 0 then .ofStatusFlags old else
    { CF := some (x.getLsbD (c - 1)), PF := some (evenParity (r.extractLsb' 0 8)), AF := none,
      ZF := some (r == 0), SF := some r.msb, OF := if c = 1 then some x.msb else none }

theorem shrFlags_allows {n : Nat} (old : StatusFlags) (of af : Bool) (c : Nat) (x : BitVec n) :
    (shrFlags old c x).Allows (shrSpec old of af c x).2 := by
  unfold shrFlags shrSpec
  by_cases h0 : c = 0
  · simp only [h0, ↓reduceIte]
    exact StatusFlagsOutcome.allows_ofStatusFlags old
  · by_cases h1 : c = 1 <;>
      simp [h0, h1, StatusFlagsOutcome.Allows, FlagAllows]

open X86 X86.Helpers

theorem shr_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x : BitVec n) (count : BitVec 8) :
    (X86.Instructions.Operations.SHR n x count).run s =
      let c := shiftCount n count
      let (r, flags) := shrSpec (StatusFlags.ofRFLAGS s.RFLAGS) (oracleBit s.oracle)
        (shrOracleAF s.oracle c) c x
      (.ok r, setFlags { s with oracle := oracleSkip s.oracle (shrOracleBits c) } flags) := by
  have hlt := shiftCount_lt_64 n count
  obtain ⟨c, hc⟩ : ∃ c, shiftCount n count = c := ⟨_, rfl⟩
  have hc32 : n ≠ 64 → count.toNat % 32 = c := fun h => by simp [← hc, shiftCount, h]
  have hc64 : n = 64 → count.toNat % 64 = c := fun h => by simp [← hc, shiftCount, h]
  rw [hc] at hlt ⊢
  simp only [shrSpec, shrOracleBits, shrOracleAF]
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.SHR
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
      (fun _ (acc : BitVec _ × BitVec 1) => (acc.1 >>> 1, acc.1.extractLsb' 0 1)) _ _ ?_)).trans ?_
    · intro _ _ _
      rfl
    rw [shr_fold _ _ _ (by omega)]
    generalize x >>> c = r
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

attribute [x86_compose] shrFlags

end X86Proofs
