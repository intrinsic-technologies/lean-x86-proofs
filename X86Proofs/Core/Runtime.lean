import X86
import X86Proofs.Core.RuntimeAttr
import X86Proofs.Core.Hardware

/-!
# lean-x86's runtime helpers

The one place that looks inside lean-x86's runtime helpers (`X86.Runtime.*`: `assert`, `slice`,
`Zero_Extend`, `setSlice`, …, and their `X86.Helpers.Std.*` wrappers); every other file uses the
lemmas below (architecture rule 5).

Each checked helper is monadic in any monad with runtime errors: it asserts its side conditions
and then returns a plain value. Its lemma takes the side conditions as hypotheses and states the
result as `pure` of a plain `BitVec`/`Int`/`Nat` term, for every lawful monad (`Except`, `SpecM`,
`PartialSpecM`). The lemmas are in the `x86_runtime` simp set; `simp` discharges the hypotheses
when they are closed arithmetic facts, or from hypotheses passed to it.

Not in the simp set:
- `assert_eq_ite`, the unconditional form of `assert`, for a condition decided later (by
  `split`, a case analysis or a rewrite);
- `ofValue_eq_mk`, `empty_eq_mk`, `toNat_setSlice`, `getLsbD_setSlice`, for looking at the bits;
- `stdSignedSaturate_eq_ok`, `stdUnsignedSaturate_eq_ok`: saturation to a signed or unsigned
  range, stated with the clamping `if`s (for the packed-integer SSE operations);
- `readSlice_specM`: reading initialized bits in `SpecM` leaves the state alone;
- `assertWithProof_bind_true`, `remember_bind_ok`: an assertion that keeps its proof, and a
  result kept with its equation (`remember`), in `Except` (lean-x86's dependent-width operations,
  e.g. BSWAP).

Monad plumbing (`liftNoSourceException`, `PartialLoop.forIn`) is `X86Proofs.Core.Run`'s.

For a site that only needs `assert` with a condition the tactic's own lemmas decide, prefer
`assert_of_true` (or `assert_eq_ite`) to the whole set: the set's arithmetic simprocs also
normalize the goal's literals, which can break a later `rw` that expects them unnormalized.
-/

namespace X86Proofs

open X86.Runtime

/-! ### Discharging side conditions

The hypotheses below are closed arithmetic facts at most sites (`0 ≤ 6`, `6 + 2 ≤ ↑8`). These
simprocs and core lemmas let `simp only [x86_runtime]` discharge them without the default simp set;
they also normalize the literals in the results (`(6 : Int).toNat` to `6`). -/
attribute [x86_runtime] Int.reduceLE Int.reduceLT Int.reduceAdd Int.reduceSub Int.reduceMul
  Int.reduceToNat Int.cast_ofNat_Int Int.natCast_nonneg decide_true decide_eq_true_eq
  Bool.and_true Bool.true_and Bool.and_self and_self and_true true_and

variable {m : Type → Type} [Monad m] {ε : Type} [MonadExcept (Error ε) m]

/-! ### Assertions -/

/-- An assertion is `pure ()` if its condition holds and fails otherwise. -/
theorem assert_eq_ite (c : Bool) :
    (assert c : m Unit) = if c then pure () else throw .assertionFailed := rfl

/-- An assertion whose condition holds is `pure ()`. -/
@[x86_runtime] theorem assert_of_true {c : Bool} (h : c = true) : (assert c : m Unit) = pure () := by
  simp [assert_eq_ite, h]

/-- An assertion that keeps its proof (`assertWithProof`), in `Except`, whose condition holds:
the rest of the computation runs with that proof. -/
theorem assertWithProof_bind_true {e β : Type} (c : Bool) (h : c = true)
    (f : PLift (c = true) → Except (Error e) β) :
    (assertWithProof c >>= f) = f ⟨h⟩ := by
  subst h
  rfl

/-- `remember a` (a result kept with its equation, as lean-x86 does for dependent widths) of an
action that returns `v`: the rest of the computation runs with `v`. -/
theorem remember_bind_ok {e α β : Type} (a : Except e α) (v : α) (h : a = .ok v)
    (f : { value : α // a = .ok value } → Except e β) :
    (remember a >>= f) = f ⟨v, h⟩ := by
  subst h
  rfl

/-! ### Checked bit operations -/

section Lawful

variable [LawfulMonad m]

/-- `x[lo +: width]`: bits `lo` to `lo + width - 1` of `x`. -/
@[x86_runtime] theorem slice_eq_pure {n : Nat} (x : BitVec n) {lo width : Int} (hlo : 0 ≤ lo)
    (hw : 0 ≤ width) (hle : lo + width ≤ n) :
    (slice x lo width : m (Bits width)) = pure (x.extractLsb' lo.toNat width.toNat) := by
  simp [slice, assert_eq_ite, hlo, hw, hle]

/-- The checked slice syntax on a bit vector is `slice`. -/
@[x86_runtime] theorem checkedSliceRead_eq_pure {n : Nat} (x : BitVec n) {lo width : Int}
    (hlo : 0 ≤ lo) (hw : 0 ≤ width) (hle : lo + width ≤ n) :
    (CheckedSlice.read x lo width : m (Bits width)) = pure (x.extractLsb' lo.toNat width.toNat) :=
  slice_eq_pure x hlo hw hle

/-- `x[hi:lo]`: bits `lo` to `hi` of `x`, the checked slice of width `hi - lo + 1`. -/
@[x86_runtime] theorem sliceInclusive_eq_pure {n : Nat} (x : BitVec n) {hi lo : Int}
    (hlo : 0 ≤ lo) (hw : 0 ≤ hi - lo + 1) (hle : lo + (hi - lo + 1) ≤ n) :
    (sliceInclusive x hi lo : m (Bits (hi - lo + 1))) =
      pure (x.extractLsb' lo.toNat (hi - lo + 1).toNat) :=
  slice_eq_pure x hlo hw hle

/-- Element `index` of width `width`: the slice at `index * width`. -/
@[x86_runtime] theorem sliceElement_bitVec_eq_pure {n : Nat} (x : BitVec n) {width index : Int}
    (hlo : 0 ≤ index * width) (hw : 0 ≤ width) (hle : index * width + width ≤ n) :
    (sliceElement x width index : m (Bits width)) =
      pure (x.extractLsb' (index * width).toNat width.toNat) :=
  slice_eq_pure x hlo hw hle

/-- Zero extension to `target` bits. -/
@[x86_runtime] theorem zeroExtend_eq_pure {n : Nat} (x : BitVec n) {target : Int}
    (h : (n : Int) ≤ target) : (Zero_Extend x target : m (Bits target)) = pure (x.setWidth target.toNat) := by
  simp [Zero_Extend, assert_eq_ite, h]

@[x86_runtime] theorem stdZeroExtend_eq_pure {n : Int} (x : Bits n) {target : Int}
    (h : ((n.toNat : Nat) : Int) ≤ target) :
    (X86.Helpers.Std.Bits.Zero_Extend x target : m (Bits target)) = pure (x.setWidth target.toNat) := by
  simp [X86.Helpers.Std.Bits.Zero_Extend, zeroExtend_eq_pure x h]

/-- Sign extension to `target` bits. -/
@[x86_runtime] theorem signExtend_eq_pure {n : Nat} (x : BitVec n) {target : Int} (h0 : 0 < n)
    (h : (n : Int) ≤ target) :
    (Sign_Extend x target : m (Bits target)) = pure (x.signExtend target.toNat) := by
  simp [Sign_Extend, assert_eq_ite, h0, h, BitVec.signExtend]

@[x86_runtime] theorem stdSignExtend_eq_pure {n : Int} (x : Bits n) {target : Int}
    (h0 : 0 < n.toNat) (h : ((n.toNat : Nat) : Int) ≤ target) :
    (X86.Helpers.Std.Bits.Sign_Extend x target : m (Bits target)) =
      pure (x.signExtend target.toNat) := by
  simp [X86.Helpers.Std.Bits.Sign_Extend, signExtend_eq_pure x h0 h]

/-- An integer as a `size`-bit vector (two's complement, wrapping). -/
@[x86_runtime] theorem fromInteger_eq_pure (value : Int) {size : Int} (h : 0 ≤ size) :
    (From_Integer value size : m (Bits size)) = pure (BitVec.ofInt size.toNat value) := by
  simp [From_Integer, assert_eq_ite, h]

@[x86_runtime] theorem stdFromInteger_eq_pure (value : Int) {size : Int} (h : 0 ≤ size) :
    (X86.Helpers.Std.Bits.From_Integer value size : m (Bits size)) =
      pure (BitVec.ofInt size.toNat value) := by
  simp [X86.Helpers.Std.Bits.From_Integer, fromInteger_eq_pure value h]

/-- The `size`-bit zero. -/
@[x86_runtime] theorem zeroBits_eq_pure {size : Int} (h : 0 ≤ size) :
    (zeroBits size : m (Bits size)) = pure 0 := by
  simp [zeroBits, assert_eq_ite, h]

@[x86_runtime] theorem stdZero_eq_pure {size : Int} (h : 0 ≤ size) :
    (X86.Helpers.Std.Bits.Zero size : m (Bits size)) = pure 0 := by
  simp [X86.Helpers.Std.Bits.Zero, zeroBits_eq_pure h]

/-- The `size`-bit all-ones value. -/
@[x86_runtime] theorem allOnes_eq_pure {size : Int} (h : 0 ≤ size) :
    (All_Ones size : m (Bits size)) = pure (BitVec.allOnes size.toNat) := by
  simp [All_Ones, assert_eq_ite, h]

@[x86_runtime] theorem stdAllOnes_eq_pure {size : Int} (h : 0 ≤ size) :
    (X86.Helpers.Std.Bits.All_Ones size : m (Bits size)) = pure (BitVec.allOnes size.toNat) := by
  simp [X86.Helpers.Std.Bits.All_Ones, allOnes_eq_pure h]

/-- `left ++ right`, as a number: `left` shifted above `right`'s bits. -/
@[x86_runtime] theorem concatBits_eq_pure {l r : Int} (left : Bits l) (right : Bits r) (hl : 0 ≤ l)
    (hr : 0 ≤ r) :
    (concatBits left right : m (Bits (l + r))) =
      pure (BitVec.ofNat (l + r).toNat ((left.toNat <<< r.toNat) + right.toNat)) := by
  simp [concatBits, assert_eq_ite, hl, hr]

/-- The checked bit update is `setSlice`. -/
@[x86_runtime] theorem setSliceChecked_eq_pure {n : Nat} (x : BitVec n) {lo width : Int}
    (value : Bits width) (hlo : 0 ≤ lo) (hw : 0 ≤ width) (hle : lo + width ≤ n) :
    (setSliceChecked x lo width value : m (BitVec n)) =
      pure (setSlice x lo.toNat width.toNat value) := by
  simp [setSliceChecked, assert_eq_ite, hlo, hw, hle]

/-! ### Checked integer operations -/

@[x86_runtime] theorem positiveDivide_eq_pure {a b : Int} (ha : 0 ≤ a) (hb : 0 < b) :
    (Positive_Divide a b : m Int) = pure (a / b) := by
  simp [Positive_Divide, assert_eq_ite, ha, hb]

@[x86_runtime] theorem stdPositiveDivide_eq_pure {a b : Int} (ha : 0 ≤ a) (hb : 0 < b) :
    (X86.Helpers.Std.Integer.Positive_Divide a b : m Int) = pure (a / b) := by
  simp [X86.Helpers.Std.Integer.Positive_Divide, positiveDivide_eq_pure ha hb]

@[x86_runtime] theorem positiveRemainder_eq_pure {a b : Int} (ha : 0 ≤ a) (hb : 0 < b) :
    (Positive_Remainder a b : m Int) = pure (a % b) := by
  simp [Positive_Remainder, assert_eq_ite, ha, hb]

@[x86_runtime] theorem stdPositiveRemainder_eq_pure {a b : Int} (ha : 0 ≤ a) (hb : 0 < b) :
    (X86.Helpers.Std.Integer.Positive_Remainder a b : m Int) = pure (a % b) := by
  simp [X86.Helpers.Std.Integer.Positive_Remainder, positiveRemainder_eq_pure ha hb]

/-- `Std.Integer.Align_Down a b`: `a` rounded toward zero to a multiple of `b ≠ 0`. -/
@[x86_runtime] theorem stdAlignDown_eq_pure {a b : Int} (hb : b ≠ 0) :
    (X86.Helpers.Std.Integer.Align_Down a b : m Int) = pure (b * a.tdiv b) := by
  simp [X86.Helpers.Std.Integer.Align_Down, alignDown, truncatedDivide, assert_eq_ite, hb]

/-- An integer's bits `lo` to `lo + width - 1` (`x[lo +: width]` on an `Int`): two's complement,
so `x / 2 ^ lo` (rounding down) wrapped to `width` bits. -/
@[x86_runtime] theorem checkedSliceRead_int_eq_pure (x lo width : Int) (hlo : 0 ≤ lo)
    (hw : 0 ≤ width) :
    (CheckedSlice.read x lo width : m (Bits width)) =
      pure (BitVec.ofInt width.toNat (x / 2 ^ lo.toNat)) := by
  simp [CheckedSlice.read, intSlice, assert_eq_ite, hlo, hw]

/-- Element `index` of width `width` of an integer: its slice at `index * width`. -/
@[x86_runtime] theorem sliceElement_int_eq_pure (x width index : Int) (hlo : 0 ≤ index * width)
    (hw : 0 ≤ width) :
    (sliceElement x width index : m (Bits width)) =
      pure (BitVec.ofInt width.toNat (x / 2 ^ (index * width).toNat)) := by
  simp [sliceElement, checkedSliceRead_int_eq_pure x _ width hlo hw]

omit [LawfulMonad m] in
/-- The inclusive slice `x[hi:lo]` is the slice of width `hi - lo + 1` at `lo`. -/
theorem sliceInclusive_eq {α : Type} [CheckedSlice α] (x : α) (hi lo : Int) :
    (sliceInclusive x hi lo : m (Bits (hi - lo + 1))) = CheckedSlice.read x lo (hi - lo + 1) := rfl

/-- Truncating division (rounding toward zero), by a nonzero divisor. -/
@[x86_runtime] theorem stdTruncatedDivide_eq_pure (a b : Int) (hb : b ≠ 0) :
    (X86.Helpers.Std.Integer.Truncated_Divide a b : m Int) = pure (a.tdiv b) := by
  simp [X86.Helpers.Std.Integer.Truncated_Divide, truncatedDivide, assert_eq_ite, hb]

/-- The remainder of truncating division, by a nonzero divisor (it has the dividend's sign). -/
@[x86_runtime] theorem stdTruncatedRemainder_eq_pure (a b : Int) (hb : b ≠ 0) :
    (X86.Helpers.Std.Integer.Truncated_Remainder a b : m Int) = pure (a.tmod b) := by
  simp [X86.Helpers.Std.Integer.Truncated_Remainder, truncatedRemainder, assert_eq_ite, hb]

/-! ### Arrays -/

omit [LawfulMonad m] in
/-- Reading entry `index` of an array, in bounds. -/
@[x86_runtime] theorem arrayGet_eq_pure {α : Type} {size : Int} (values : X86.Runtime.Array size α)
    {index : Int} (h0 : 0 ≤ index) (h : index < size) :
    (X86.Runtime.Array.get values index : m α) = pure (values[index.toNat]'(by omega)) := by
  simp [X86.Runtime.Array.get, h0, h]

omit [LawfulMonad m] in
/-- Writing entry `index` of an array, in bounds. -/
@[x86_runtime] theorem arraySet_eq_pure {α : Type} {size : Int} (values : X86.Runtime.Array size α)
    {index : Int} (value : α) (h0 : 0 ≤ index) (h : index < size) :
    (X86.Runtime.Array.set values index value : m (X86.Runtime.Array size α)) =
      pure (Vector.set values index.toNat value (by omega)) := by
  simp [X86.Runtime.Array.set, h0, h]

/-! ### Initialized bits -/

/-- Reading bits `lo` to `lo + width - 1` of a value whose unwritten mask is zero there. -/
@[x86_runtime] theorem readSlice_mk {size : Int} (payload unwritten : Bits size) {lo width : Int}
    (hs : 0 ≤ size) (hlo : 0 ≤ lo) (hw : 0 ≤ width) (hle : lo + width ≤ size)
    (hu : unwritten.extractLsb' lo.toNat width.toNat = 0) :
    ((InitializedBits.mk payload unwritten).readSlice lo width : m (Bits width)) =
      pure (payload.extractLsb' lo.toNat width.toNat) := by
  have hle' : lo + width ≤ ((size.toNat : Nat) : Int) := by omega
  simp [InitializedBits.readSlice, assert_eq_ite, hs, slice_eq_pure _ hlo hw hle', hu]

/-- Reading the whole of a value with no unwritten bits. -/
@[x86_runtime] theorem read_mk {size : Int} (payload unwritten : Bits size) (hs : 0 ≤ size)
    (hu : unwritten = 0) :
    ((InitializedBits.mk payload unwritten).read : m (Bits size)) = pure payload := by
  subst hu
  simp only [InitializedBits.read]
  rw [readSlice_mk payload 0 hs (Int.le_refl 0) hs (by omega) (by simp)]
  simp [BitVec.extractLsb'_eq_self]

/-- A value with no bits written: payload zero, every bit unwritten. -/
theorem empty_eq_mk (size : Int) :
    InitializedBits.empty size = InitializedBits.mk 0 (BitVec.allOnes size.toNat) := rfl

theorem ofValue_eq_mk {size : Int} (value : Bits size) :
    InitializedBits.ofValue value = InitializedBits.mk value 0 := rfl

@[x86_runtime] theorem readSlice_ofValue {size : Int} (value : Bits size) {lo width : Int}
    (hs : 0 ≤ size) (hlo : 0 ≤ lo) (hw : 0 ≤ width) (hle : lo + width ≤ size) :
    ((InitializedBits.ofValue value).readSlice lo width : m (Bits width)) =
      pure (value.extractLsb' lo.toNat width.toNat) :=
  readSlice_mk value 0 hs hlo hw hle (by simp)

@[x86_runtime] theorem read_ofValue {size : Int} (value : Bits size) (hs : 0 ≤ size) :
    ((InitializedBits.ofValue value).read : m (Bits size)) = pure value :=
  read_mk value 0 hs rfl

/-- Writing bits `lo` to `lo + width - 1`: the payload gets `value` there and those bits are
marked written. -/
@[x86_runtime] theorem writeSlice_mk {size : Int} (payload unwritten : Bits size) {lo width : Int}
    (value : Bits width) (hs : 0 ≤ size) (hlo : 0 ≤ lo) (hw : 0 ≤ width)
    (hle : lo + width ≤ ((size.toNat : Nat) : Int)) :
    ((InitializedBits.mk payload unwritten).writeSlice lo width value : m (InitializedBits size)) =
      pure (InitializedBits.mk (setSlice payload lo.toNat width.toNat value)
        (setSlice unwritten lo.toNat width.toNat 0)) := by
  simp [InitializedBits.writeSlice, assert_eq_ite, hs, setSliceChecked_eq_pure _ _ hlo hw hle]

end Lawful

/-- Reading initialized bits in `SpecM` leaves the state alone: it is the `Except` read. -/
theorem readSlice_specM {σ : Type} {size : Int} (v : InitializedBits size) (lo w : Int) :
    (v.readSlice lo w : SpecM ε σ (Bits w)) =
      ExceptT.mk (fun s => ((v.readSlice lo w : Except (Error ε) (Bits w)), s)) := by
  cases v with
  | mk p q =>
  simp only [InitializedBits.readSlice, slice, assert_eq_ite]
  by_cases h1 : 0 ≤ size <;>
    by_cases h2 : (decide (0 ≤ lo) && decide (0 ≤ w) && decide (lo + w ≤ ↑size.toNat)) = true <;>
    simp only [h1, h2, decide_true, decide_false, ↓reduceIte, pure_bind] <;> try rfl
  by_cases h3 : (BitVec.extractLsb' lo.toNat w.toNat q == 0) = true <;>
    simp only [h3, ↓reduceIte] <;> rfl

/-! ### Total helpers -/

/-- `Unsigned x` is `x` as a natural number. -/
@[x86_runtime] theorem unsigned_eq {n : Nat} (x : BitVec n) : Unsigned x = (x.toNat : Int) := rfl

/-- `Signed x` is `x` as a two's-complement integer. -/
@[x86_runtime] theorem signed_eq {n : Nat} (x : BitVec n) : Signed x = x.toInt := rfl

/-- `inRange value lo hi`: `lo ≤ value ≤ hi`. -/
@[x86_runtime] theorem inRange_eq (value lo hi : Int) :
    inRange value lo hi = (decide (lo ≤ value) && decide (value ≤ hi)) := rfl

/-- `intRange lo hi` is `[lo, lo + 1, …, hi]` (empty if `hi < lo`). -/
@[x86_runtime] theorem intRange_eq (lo hi : Int) :
    intRange lo hi = (List.range (hi - lo + 1).toNat).map (fun i : Nat => lo + (i : Int)) := rfl

/-- `Std.Bits.Add_int left right`: `left + right`, wrapping. -/
@[x86_runtime] theorem stdAddInt_eq_ok {n : Int} (left : Bits n) (right : Int) (h : 0 ≤ n) :
    X86.Helpers.Std.Bits.Add_int left right = .ok (left + BitVec.ofInt n.toNat right) := by
  simp [X86.Helpers.Std.Bits.Add_int, assert_eq_ite, h, fromInteger_eq_pure right h,
    X86.Helpers.Std.Bits.From_Integer]
  rfl

/-- `Std.Bits.Subtract_int left right`: `left - right`, wrapping. -/
theorem stdSubtractInt_eq_ok {n : Int} (left : Bits n) (right : Int) (h : 0 ≤ n) :
    X86.Helpers.Std.Bits.Subtract_int left right = .ok (left - BitVec.ofInt n.toNat right) := by
  simp [X86.Helpers.Std.Bits.Subtract_int, assert_eq_ite, h, stdFromInteger_eq_pure right h]
  rfl

/-- `Std.Bits.Is_Zero x`: whether `x` is zero. -/
@[x86_runtime] theorem stdIsZero_eq_ok {n : Int} (x : Bits n) (h : 0 ≤ n) :
    X86.Helpers.Std.Bits.Is_Zero x = .ok (x == 0) := by
  simp [X86.Helpers.Std.Bits.Is_Zero, assert_eq_ite, h, zeroBits_eq_pure,
    X86.Helpers.Std.Bits.Zero]
  rfl

/-- `Std.Integer.Max left right`: the larger of the two. -/
@[x86_runtime] theorem stdIntegerMax_eq (left right : Int) :
    X86.Helpers.Std.Integer.Max left right = max left right := by
  simp only [X86.Helpers.Std.Integer.Max, ge_iff_le, decide_eq_true_eq]
  split <;> omega

/-- `Std.Integer.Min left right`: the smaller of the two. -/
@[x86_runtime] theorem stdIntegerMin_eq (left right : Int) :
    X86.Helpers.Std.Integer.Min left right = min left right := by
  simp only [X86.Helpers.Std.Integer.Min, decide_eq_true_eq]
  split <;> omega

/-- `Std.Integer.Abs x`: the absolute value. -/
@[x86_runtime] theorem stdIntegerAbs_eq_ok (x : Int) :
    X86.Helpers.Std.Integer.Abs x = .ok (x.natAbs : Int) := by
  simp only [X86.Helpers.Std.Integer.Abs, ge_iff_le, decide_eq_true_eq]
  split <;> (congr 1; omega)

/-- `Std.Integer.Is_Even x`: whether bit 0 of `x` is clear. -/
@[x86_runtime] theorem stdIntegerIsEven_eq_ok (x : Int) :
    X86.Helpers.Std.Integer.Is_Even x = .ok (x % 2 == 0) := by
  simp only [X86.Helpers.Std.Integer.Is_Even]
  rw [checkedSliceRead_int_eq_pure x 0 1 (by decide) (by decide)]
  simp only [pure_bind, Int.toNat_zero, Int.pow_zero, Int.ediv_one, Int.reduceToNat]
  show Except.ok (BitVec.ofInt 1 x == 0) = Except.ok (x % 2 == 0)
  congr 1
  rcases Int.emod_two_eq x with h | h <;> simp [BitVec.ofInt, h]

/-- `2 ** k` (`Std.Integer.Exp 2 k`) for `k ≥ 0` is `2 ^ k`. -/
theorem stdExp_two_eq_ok (k : Int) (hk : 0 ≤ k) :
    X86.Helpers.Std.Integer.Exp 2 k = .ok ((2 ^ k.toNat : Nat) : Int) := by
  simp [X86.Helpers.Std.Integer.Exp, X86.Helpers.Std.Integer.Power2, Power2, assert_eq_ite, hk]
  rfl

/-- `Std.Bits.Signed_Saturate x size` (`size ≥ 1`): `x` clamped to the signed range of `size`
bits, `[-2 ^ (size - 1), 2 ^ (size - 1) - 1]`, as a `size`-bit value. -/
theorem stdSignedSaturate_eq_ok (x : Int) {size : Int} (h : 1 ≤ size) :
    X86.Helpers.Std.Bits.Signed_Saturate x size =
      .ok (BitVec.ofInt size.toNat
        (if 2 ^ (size.toNat - 1) ≤ x then 2 ^ (size.toNat - 1) - 1
          else if x < -2 ^ (size.toNat - 1) then -2 ^ (size.toNat - 1) else x)) := by
  have hexp := stdExp_two_eq_ok (size - 1) (by omega)
  rw [show (size - 1).toNat = size.toNat - 1 by omega] at hexp
  simp only [X86.Helpers.Std.Bits.Signed_Saturate, assert_of_true (decide_eq_true h), pure_bind]
  simp only [bind, Except.bind, hexp, ge_iff_le, decide_eq_true_eq, Int.natCast_pow,
    Int.cast_ofNat_Int]
  split <;> (try split) <;>
    rw [checkedSliceRead_int_eq_pure _ 0 size (by decide) (by omega)] <;>
    simp [pure, Except.pure]

/-- `Std.Bits.Unsigned_Saturate x size`: `x` clamped to `[0, 2 ^ size - 1]`, as a `size`-bit
value. -/
theorem stdUnsignedSaturate_eq_ok (x : Int) {size : Int} (h : 0 ≤ size) :
    X86.Helpers.Std.Bits.Unsigned_Saturate x size =
      .ok (BitVec.ofInt size.toNat
        (if 2 ^ size.toNat ≤ x then 2 ^ size.toNat - 1 else if x < 0 then 0 else x)) := by
  have hexp := stdExp_two_eq_ok size h
  simp only [X86.Helpers.Std.Bits.Unsigned_Saturate, assert_of_true (decide_eq_true h), pure_bind]
  simp only [bind, Except.bind, hexp, ge_iff_le, decide_eq_true_eq, Int.natCast_pow,
    Int.cast_ofNat_Int]
  split <;> (try split) <;>
    rw [checkedSliceRead_int_eq_pure _ 0 size (by decide) h] <;>
    simp [pure, Except.pure]

/-! ### Bit updates -/

/-- Writing no bits. -/
@[x86_runtime] theorem setSlice_zero_width {n : Nat} (x : BitVec n) (lo : Nat) (value : BitVec 0) :
    setSlice x lo 0 value = x := rfl

/-- `setSlice x lo w v` as a number: `x` with bits `lo` to `lo + w - 1` replaced by `v`. -/
theorem toNat_setSlice {n : Nat} (x : BitVec n) (lo w : Nat) (v : BitVec w) (hw : w ≠ 0) :
    (setSlice x lo w v).toNat =
      (x.toNat >>> (lo + w) <<< (lo + w) ||| x.toNat % 2 ^ lo ||| v.toNat <<< lo) % 2 ^ n := by
  simp only [setSlice, hw, ite_false, BitVec.toNat_ofNat]

/-- Bit `k` of `setSlice x lo w v`: `v`'s bits in `[lo, lo + w)`, `x`'s elsewhere. -/
theorem getLsbD_setSlice {n : Nat} (x : BitVec n) (lo w : Nat) (v : BitVec w) (k : Nat)
    (hk : k < n) :
    (setSlice x lo w v).getLsbD k =
      if lo ≤ k ∧ k < lo + w then v.getLsbD (k - lo) else x.getLsbD k := by
  unfold setSlice
  split
  · subst_vars; simp; omega
  · simp only [BitVec.getLsbD_ofNat, hk, decide_true, Bool.true_and, Nat.testBit_or,
      Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow, BitVec.testBit_toNat]
    by_cases h1 : lo ≤ k <;> by_cases h2 : k < lo + w
    · simp [h1, h2, show ¬ lo + w ≤ k by omega, show ¬ k < lo by omega]
    · have hv : v.getLsbD (k - lo) = false := BitVec.getLsbD_of_ge v _ (by omega)
      simp [h1, h2, hv, show lo + w ≤ k by omega, show ¬ k < lo by omega,
        show lo + w + (k - (lo + w)) = k by omega]
    · simp [h1, h2, show ¬ lo + w ≤ k by omega, show k < lo by omega]
    · omega

/-- Writing all `n` bits from bit 0 replaces the value. -/
@[x86_runtime] theorem setSlice_full {n : Nat} (x v : BitVec n) : setSlice x 0 n v = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [getLsbD_setSlice x 0 n v k hk]
  simp [hk]

end X86Proofs
