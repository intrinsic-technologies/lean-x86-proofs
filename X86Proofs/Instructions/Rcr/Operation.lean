import X86Proofs.Core.Shift
import X86Proofs.Program.Effect
import X86Proofs.Program.ComposeAttr

/-!
# RCR specification

Rotate through carry: CF above the operand, an `n + 1`-bit value (`BitVec.cons cf x`), is rotated
right by the masked count `c` (see `shiftCount`), so by `c` modulo `n + 1` (the SDM's count modulo
9 or 17 at 8 and 16 bits); the result is its low `n` bits and CF its top bit. The carry-in `cf` is
the CF before the instruction. The flags depend on the count:

- `c = 0`: no flag changes; the spec returns the old flags `old`.
- `c ≥ 1`: CF is the top bit of the rotated value; OF is the operand's top bit xor the carry-in
  for `c = 1` and undefined otherwise (the caller passes the bit lean-x86's oracle supplies,
  `of`); the other flags keep their old values.

`rcrFlags` is the same as a `StatusFlagsOutcome`: unchanged flags are `some` of their old value, the
undefined OF is `none`. It takes the carry-in as an argument rather than reading it from `old`, so
an effect stating it reads each old flag only for that flag.
-/

namespace X86Proofs

/-- Result and flags of rotating `x` right through the carry `cf` by the masked count `c`. `old` are
the flags before, `of` is the unspecified OF bit for `c ≥ 2`. -/
def rcrSpec {n : Nat} (old : StatusFlags) (of cf : Bool) (c : Nat) (x : BitVec n) :
    BitVec n × StatusFlags :=
  let t := (BitVec.cons cf x).rotateRight c
  let r := t.setWidth n
  (r, if c = 0 then old else { old with CF := t.msb, OF := if c = 1 then x.msb ^^ cf else of })

/-- Oracle bits RCR uses for count `c`: one (OF) for `c ≥ 2`, none otherwise. -/
def rcrOracleBits (c : Nat) : Nat := if c = 0 ∨ c = 1 then 0 else 1

/-- What RCR by count `c` with carry-in `cf` does to the flags, from old flags `old` and operand
`x`: nothing for `c = 0`; else CF is the top bit of the rotated value, OF (only for `c = 1`) is the
operand's top bit xor the carry-in and undefined otherwise, and PF, AF, ZF, SF keep their old
values. -/
def rcrFlags {n : Nat} (old : StatusFlags) (cf : Bool) (c : Nat) (x : BitVec n) :
    StatusFlagsOutcome :=
  let t := (BitVec.cons cf x).rotateRight c
  if c = 0 then .ofStatusFlags old else
    { CF := some t.msb, PF := some old.PF, AF := some old.AF, ZF := some old.ZF,
      SF := some old.SF, OF := if c = 1 then some (x.msb ^^ cf) else none }

theorem rcrFlags_allows {n : Nat} (old : StatusFlags) (of cf : Bool) (c : Nat) (x : BitVec n) :
    (rcrFlags old cf c x).Allows (rcrSpec old of cf c x).2 := by
  unfold rcrFlags rcrSpec
  by_cases h0 : c = 0
  · simp only [h0, ↓reduceIte]
    exact StatusFlagsOutcome.allows_ofStatusFlags old
  · by_cases h1 : c = 1 <;>
      simp [h0, h1, StatusFlagsOutcome.Allows, FlagAllows]

open X86 X86.Helpers

theorem rcr_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x : BitVec n) (count : BitVec 8) :
    (X86.Instructions.Operations.RCR n x count).run s =
      let c := shiftCount n count
      let (r, flags) := rcrSpec (StatusFlags.ofRFLAGS s.RFLAGS) (oracleBit s.oracle)
        (StatusFlags.ofRFLAGS s.RFLAGS).CF c x
      (.ok r, setFlags { s with oracle := oracleSkip s.oracle (rcrOracleBits c) } flags) := by
  have hlt := shiftCount_lt_64 n count
  obtain ⟨c, hc⟩ : ∃ c, shiftCount n count = c := ⟨_, rfl⟩
  have hc32 : n ≠ 64 → count.toNat % 32 = c := fun h => by simp [← hc, shiftCount, h]
  have hc64 : n = 64 → count.toNat % 64 = c := fun h => by simp [← hc, shiftCount, h]
  rw [hc] at hlt ⊢
  simp only [rcrSpec, rcrOracleBits]
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.RCR
    first
      | (iterate 7 spec_bind_rfl
         refine (specM_bind_run _ _
           (specM_forIn_run _ _ (fun _ acc => rcrStep acc) _ _ ?_)).trans ?_)
      | (iterate 6 spec_bind_rfl
         refine (specM_bind_run _ _
           (specM_forIn_run _ _ (fun _ acc => rcrStep acc) _ _ ?_)).trans ?_)
    · intro _ _ _
      rfl
    simp only [Int.cast_ofNat_Int, Int.reduceToNat, Int.reduceSub, Int.reduceAdd,
      unsigned_extractLsb', Nat.reducePow]
    first | rw [hc32 (by decide)] | rw [hc64 rfl]
    rw [rcr_fold _ _ (by omega), ofNat_concat_eq_cons, cf_ofRFLAGS]
    first
      | simp only [Int.toNat_emod (Int.natCast_nonneg _) (by decide : (0 : Int) ≤ 9),
          Int.toNat_emod (Int.natCast_nonneg _) (by decide : (0 : Int) ≤ 17), Int.toNat_natCast,
          Int.reduceToNat, BitVec.rotateRight_mod_eq_rotateRight]
      | simp only [Int.toNat_natCast]
    rw [BitVec.setWidth_eq_extractLsb' (by decide)]
    rcases Nat.lt_or_ge c 2 with hc | hc
    · rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
      · simp only [rotateRight_zero]
        repeat spec_bind_rfl
        simp only [↓reduceIte, Int.reduceToNat, extractLsb'_cons_top]
        rw [setFlags_eq_of_store]
        · rfl
        · rflags_ext
      · iterate 7 spec_bind_rfl
        spec_bind_with rflagsCF_run _
        repeat spec_bind_rfl
        simp only [Nat.one_ne_zero, ↓reduceIte, or_true, oracleSkip_zero]
        rw [setFlags_eq_of_store]
        · rfl
        · rflags_ext
    · have h0 : c ≠ 0 := by omega
      have h1 : c ≠ 1 := by omega
      have e1 : ((c : Int) == 1) = false := by simp; omega
      have e2 : ((c : Int) != 0) = true := by simp; omega
      repeat spec_bind_rfl
      simp only [h0, h1, ↓reduceIte, or_self, e1, e2, Bool.false_eq_true]
      rw [setFlags_eq_of_store]
      · rfl
      · rflags_ext

attribute [x86_compose] rcrFlags

end X86Proofs
