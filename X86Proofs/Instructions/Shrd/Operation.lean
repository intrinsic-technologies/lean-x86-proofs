import X86Proofs.Core.Shift
import X86Proofs.Core.Lanes
import X86Proofs.Program.Effect
import X86Proofs.Program.ComposeAttr

/-!
# SHRD specification

`SHRD DEST, SRC, COUNT` (double-precision shift right): `DEST` is shifted right by the masked count
`c` (`shiftCount`: the count's low 6 bits at 64 bits, 5 otherwise), and the vacated high bits are
filled from the bottom of `SRC`; `SRC` is unchanged. For `0 < c ≤ n` the result is `shrdResult`, CF
is the last bit shifted out of `DEST`, SF, ZF and PF come from the result, AF is undefined, and OF
is the change of sign for `c = 1` and undefined otherwise. For `c = 0` nothing changes (at 32 bits
the destination register is still written, so its upper half is cleared).

A count above the operand size is possible only at 16 bits (17 to 31). The SDM leaves the result
and every flag undefined; lean-x86 draws the result (`n` bits) and then OF, SF, ZF, AF, PF and CF
from its oracle. The spec takes the oracle bits as a function `o` (bit `i` is the `i`-th bit
lean-x86 draws) and the undefined result as `u`; `shrdOracleBits` is how many bits are used.
`shrdFlags` is the flags outcome, the undefined flags `none`.
-/

namespace X86Proofs

/-- `x` shifted right by `c`, the high `c` bits filled from the bottom of `y` (for `c ≤ n`). -/
def shrdResult {n : Nat} (c : Nat) (x y : BitVec n) : BitVec n := x >>> c ||| y <<< (n - c)

/-- Result and flags of `shrd x, y` by the masked count `c`, from the flags before `old`, the
oracle bits `o` and the undefined result `u` (used for `c > n`). -/
def shrdSpec {n : Nat} (o : Nat → Bool) (u : BitVec n) (old : StatusFlags) (c : Nat)
    (x y : BitVec n) : BitVec n × StatusFlags :=
  if c = 0 then (x, old) else if n < c then
    (u, { CF := o (n + 5), PF := o (n + 4), AF := o (n + 3), ZF := o (n + 2), SF := o (n + 1),
          OF := o n })
  else
    let r := shrdResult c x y
    (r, { CF := x.getLsbD (c - 1), PF := evenParity (r.extractLsb' 0 8),
          AF := if c = 1 then o 0 else o 1, ZF := r == 0, SF := r.msb,
          OF := if c = 1 then x.msb ^^ r.msb else o 0 })

/-- Oracle bits SHRD uses at `n` bits for count `c`: none for 0, AF for 1, OF and AF up to `n`,
the result and the six flags above `n`. -/
def shrdOracleBits (n c : Nat) : Nat :=
  if c = 0 then 0 else if n < c then n + 6 else if c = 1 then 1 else 2

/-- What SHRD by count `c` does to the flags: nothing for `c = 0`; every flag undefined above `n`;
else CF the last bit shifted out, SF, ZF, PF from the result, AF undefined, OF the change of sign
for `c = 1` and undefined otherwise. -/
def shrdFlags {n : Nat} (old : StatusFlags) (c : Nat) (x y : BitVec n) : StatusFlagsOutcome :=
  if c = 0 then .ofStatusFlags old else if n < c then ⟨none, none, none, none, none, none⟩ else
    let r := shrdResult c x y
    { CF := some (x.getLsbD (c - 1)), PF := some (evenParity (r.extractLsb' 0 8)), AF := none,
      ZF := some (r == 0), SF := some r.msb,
      OF := if c = 1 then some (x.msb ^^ r.msb) else none }

theorem shrdFlags_allows {n : Nat} (o : Nat → Bool) (u : BitVec n) (old : StatusFlags) (c : Nat)
    (x y : BitVec n) : (shrdFlags old c x y).Allows (shrdSpec o u old c x y).2 := by
  unfold shrdFlags shrdSpec
  by_cases h0 : c = 0
  · simp only [h0, ↓reduceIte]
    exact StatusFlagsOutcome.allows_ofStatusFlags old
  · by_cases hb : n < c
    · simp [h0, hb, StatusFlagsOutcome.Allows, FlagAllows]
    · simp only [h0, hb, ↓reduceIte]
      by_cases h1 : c = 1 <;> simp only [h1, ↓reduceIte] <;>
        exact ⟨rfl, rfl, trivial, rfl, rfl, by first | rfl | trivial⟩

theorem shrdSpec_fst {n : Nat} (o : Nat → Bool) (u : BitVec n) (old : StatusFlags) (c : Nat)
    (hc : c ≤ n) (x y : BitVec n) : (shrdSpec o u old c x y).1 = shrdResult c x y := by
  unfold shrdSpec shrdResult
  by_cases h0 : c = 0
  · subst h0
    simp only [↓reduceIte, Nat.sub_zero]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp
  · simp [h0, show ¬ n < c by omega]

theorem shrdResult_eq_extract {n m : Nat} (hm : m = n + n) (c : Nat) (hc : c ≤ n)
    (x y : BitVec n) :
    (BitVec.ofNat m (y.toNat <<< n + x.toNat)).extractLsb' c n = shrdResult c x y := by
  subst hm
  rw [ofNat_shiftLeft_add_eq_append_any]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, shrdResult, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  by_cases h : c + i < n
  · simp [h, show i < n - c by omega]
  · simp [h, show ¬ (i < n - c) by omega, show c + i - n = i - (n - c) by omega,
      BitVec.getLsbD_of_ge x (c + i) (by omega)]

open X86 X86.Helpers

theorem shrd_operation {σ : Type} (s : X86.State σ) (n : Nat) (hn : n = 16 ∨ n = 32 ∨ n = 64)
    (x y : BitVec n) (count : BitVec 8) :
    (X86.Instructions.Operations.SHRD n x y count).run s =
      let c := shiftCount n count
      let r := shrdSpec (fun i => oracleBit (oracleSkip s.oracle i)) (s.oracle.take n).1
        (StatusFlags.ofRFLAGS s.RFLAGS) c x y
      (.ok r.1, setFlags { s with oracle := oracleSkip s.oracle (shrdOracleBits n c) } r.2) := by
  have hlt := shiftCount_lt_64 n count
  obtain ⟨c, hc⟩ : ∃ c, shiftCount n count = c := ⟨_, rfl⟩
  have hc32 : n ≠ 64 → count.toNat % 32 = c := fun h => by simp [← hc, shiftCount, h]
  have hc64 : n = 64 → count.toNat % 64 = c := fun h => by simp [← hc, shiftCount, h]
  rw [hc] at hlt ⊢
  simp only [shrdSpec, shrdOracleBits]
  by_cases h0 : c = 0
  · subst h0
    rcases hn with rfl | rfl | rfl
    all_goals
      unfold X86.Instructions.Operations.SHRD
      simp only [isParityEven8_run]
      repeat spec_bind_rfl
      simp only [Int.cast_ofNat_Int, Int.reduceSub, Int.reduceAdd, Int.reduceToNat,
        unsigned_extractLsb', Nat.reducePow]
      first | rw [hc32 (by decide)] | rw [hc64 rfl]
      simp
  have e0 : ((c : Int) == 0) = false := by simp; omega
  by_cases hb : n < c
  · obtain rfl : n = 16 := by
      rcases hn with rfl | rfl | rfl
      · rfl
      · have := hc32 (by decide); omega
      · omega
    have e1 : decide ((c : Int) > 16) = true := by simp; omega
    unfold X86.Instructions.Operations.SHRD
    simp only [isParityEven8_run]
    repeat spec_bind_rfl
    simp only [Int.cast_ofNat_Int, Int.reduceSub, Int.reduceAdd, Int.reduceToNat,
      unsigned_extractLsb', Nat.reducePow]
    rw [hc32 (by decide)]
    simp only [e0, e1, h0, hb, Bool.false_eq_true, ↓reduceIte]
    repeat spec_bind_rfl
    simp only [Int.reduceToNat, oracleTake_fst]
    rw [setFlags_eq_of_store]
    · rfl
    · rflags_ext
  rcases hn with rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.SHRD
    simp only [isParityEven8_run]
    repeat spec_bind_rfl
    simp only [Int.cast_ofNat_Int, Int.reduceSub, Int.reduceAdd, Int.reduceToNat,
      unsigned_extractLsb', Nat.reducePow]
    first | rw [hc32 (by decide)] | rw [hc64 rfl]
    simp only [e0, h0, hb, Bool.false_eq_true, ↓reduceIte]
    simp (disch := omega) only [decide_eq_false, decide_eq_true, Bool.false_eq_true, ↓reduceIte]
    simp (disch := first | omega | (simp only [decide_eq_true_eq]; omega)) only [x86_runtime,
      pure_bind]
    simp (disch := omega) only [shrdResult_eq_extract]
    by_cases h1 : c = 1
    · subst h1
      simp only [↓reduceIte]
      repeat spec_bind_rfl
      rw [setFlags_eq_of_store]
      · rfl
      · rflags_ext
    · have e1 : ((c : Int) == 1) = false := by simp; omega
      simp only [e1, h1, Bool.false_eq_true, ↓reduceIte]
      repeat spec_bind_rfl
      rw [setFlags_eq_of_store]
      · rfl
      · rflags_ext

attribute [x86_compose] shrdResult shrdFlags

end X86Proofs
