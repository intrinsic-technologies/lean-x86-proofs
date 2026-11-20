import X86Proofs.Core.Shift

/-!
# Single bits: bit test and bit scan

Shared by the bit-test operations (BT, BTS, BTR, BTC) and the bit scans (BSF, BSR):

- `extractLsb'_width_one`: a one-bit slice is the bit as a `BitVec 1`.
- `setSlice_one_one`, `setSlice_one_zero`, `setSlice_one_not`: lean-x86's one-bit update of bit `k`
  (`setSlice x k 1 v`) setting, clearing and complementing it, as `|||`, `&&& ~~~` and `^^^` with
  `BitVec.twoPow n k`.
- `lowestSetBit`, `highestSetBit?`, `highestSetBit`, `leadingZeros`, `oddBits`: the bit scans and
  the parity of a whole operand, as the SDM describes them (a scan up from bit 0, down from bit
  `n - 1`), and `countTrailingZeroBits_run`, `countLeadingZeroBits_run`, `isParityOdd_run`:
  lean-x86's loops (`Std.Bits.Count_Trailing_Zero_Bits`, `Count_Leading_Zero_Bits`,
  `Is_Parity_Odd`) compute them. This is the one place that looks inside those loops
  (architecture rule 5).
- `bitStringOffset`, `calculateBitOffset_eq`: the byte offset of the operand BT, BTS, BTR, BTC
  address with a memory bit base and a register bit offset, as lean-x86's `Calculate_Bit_Offset`
  computes it (owned here).
- `ofInt_toInt_mul`: the signed product truncated to `n` bits (the two- and three-operand IMUL's
  result) is the product.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- A one-bit slice of `x` at `k` is bit `k` of `x`. -/
theorem extractLsb'_width_one {n : Nat} (x : BitVec n) (k : Nat) :
    x.extractLsb' k 1 = BitVec.ofBool (x.getLsbD k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have : i = 0 := by omega
  subst this
  simp

/-- Setting bit `k` of `x` to 1 is `x ||| 2 ^ k`. -/
theorem setSlice_one_one {n : Nat} (x : BitVec n) (k : Nat) (hk : k < n) :
    X86.Runtime.setSlice x k 1 (1 : BitVec 1) = x ||| BitVec.twoPow n k := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_setSlice_one_eq _ _ _ _ hk]
  by_cases h : j = k
  · subst h; simp [hk]
  · simp [BitVec.getLsbD_twoPow, Ne.symm h, h]

/-- Setting bit `k` of `x` to 0 is `x &&& ~~~2 ^ k`. -/
theorem setSlice_one_zero {n : Nat} (x : BitVec n) (k : Nat) (hk : k < n) :
    X86.Runtime.setSlice x k 1 (0 : BitVec 1) = x &&& ~~~BitVec.twoPow n k := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_setSlice_one_eq _ _ _ _ hk]
  by_cases h : j = k
  · subst h; simp [hk]
  · simp [h, hj]

/-- Setting bit `k` of `x` to its complement is `x ^^^ 2 ^ k`. -/
theorem setSlice_one_not {n : Nat} (x : BitVec n) (k : Nat) (hk : k < n) (v : BitVec 1)
    (hv : v.getLsbD 0 = !x.getLsbD k) :
    X86.Runtime.setSlice x k 1 v = x ^^^ BitVec.twoPow n k := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_setSlice_one_eq _ _ _ _ hk]
  by_cases h : j = k
  · subst h; rw [hv]; simp [hk]
  · simp [BitVec.getLsbD_twoPow, Ne.symm h, h]

/-- The index of the lowest set bit of `x`, scanning up from bit 0; `n` if no bit is set. -/
def lowestSetBit {n : Nat} (x : BitVec n) : Nat := ((List.range n).find? x.getLsbD).getD n

/-- The index of the highest set bit of `x`, scanning down from bit `n - 1`; `none` if no bit is
set. -/
def highestSetBit? {n : Nat} (x : BitVec n) : Option Nat :=
  ((List.range n).map (fun i => n - 1 - i)).find? x.getLsbD

/-- The index of the highest set bit of `x` (0 if no bit is set). -/
def highestSetBit {n : Nat} (x : BitVec n) : Nat := (highestSetBit? x).getD 0

/-- The number of zero bits above the highest set bit of `x`; `n` if no bit is set. -/
def leadingZeros {n : Nat} (x : BitVec n) : Nat :=
  match highestSetBit? x with
  | some i => n - 1 - i
  | none => n

/-- `x` has an odd number of set bits. -/
def oddBits {n : Nat} (x : BitVec n) : Bool :=
  (List.range n).foldl (fun r i => r ^^ x.getLsbD i) false

/-- A non-zero `x` has a highest set bit, below `n`, with `leadingZeros` zero bits above it. -/
theorem highestSetBit_of_ne_zero {n : Nat} (x : BitVec n) (hx : x ≠ 0) :
    highestSetBit x < n ∧ leadingZeros x = n - 1 - highestSetBit x := by
  unfold highestSetBit leadingZeros
  cases h : highestSetBit? x with
  | some i =>
    have hm := List.mem_of_find?_eq_some h
    simp only [List.mem_map, List.mem_range] at hm
    obtain ⟨j, hj, rfl⟩ := hm
    simp only [Option.getD_some, and_true]
    omega
  | none =>
    exfalso
    apply hx
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := List.find?_eq_none.mp h (n - 1 - (n - 1 - i))
      (List.mem_map.mpr ⟨n - 1 - i, List.mem_range.mpr (by omega), rfl⟩)
    rw [show n - 1 - (n - 1 - i) = i by omega] at this
    simpa using this

/-- lean-x86's `Count_Trailing_Zero_Bits` is `lowestSetBit`. -/
theorem countTrailingZeroBits_run (n : Nat) (x : BitVec n) :
    Std.Bits.Count_Trailing_Zero_Bits (size := (n : Int)) x = .ok (lowestSetBit x : Int) := by
  unfold Std.Bits.Count_Trailing_Zero_Bits lowestSetBit
  simp only [x86_runtime, Int.zero_add]
  have key : ∀ l : List Nat, (∀ i ∈ l, i < n) →
      forIn (m := Except (X86.Runtime.Error Empty)) (List.map (fun i : Nat => (i : Int)) l)
        ((none, ()) : Option Int × Unit)
        (fun i (_ : Option Int × Unit) => do
          let b ← X86.Runtime.CheckedSlice.read x i 1
          if (b == 1) = true then pure (ForInStep.done (some i, ()))
          else pure (ForInStep.yield (none, ()))) =
        .ok ((l.find? x.getLsbD).map (fun i : Nat => (i : Int)), ()) := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a l ih =>
      have ha := hl a (by simp)
      have ih' := ih (fun i hi => hl i (by simp [hi]))
      simp only [List.map_cons, List.forIn_cons]
      rw [checkedSliceRead_eq_pure x (by omega) (by omega) (by omega)]
      simp only [beq_iff_eq] at ih' ⊢
      simp only [pure_bind, Int.toNat_natCast, Int.reduceToNat, extractLsb'_width_one]
      cases h : x.getLsbD a
      · simpa [h] using ih'
      · simp [h]; rfl
  have hr : ((n : Int) - 1 - 0 + 1).toNat = n := by omega
  rw [hr, key _ (fun i hi => List.mem_range.mp hi)]
  cases (List.range n).find? x.getLsbD <;> rfl

/-- lean-x86's `Count_Leading_Zero_Bits` is `leadingZeros`. -/
theorem countLeadingZeroBits_run (n : Nat) (x : BitVec n) :
    Std.Bits.Count_Leading_Zero_Bits (size := (n : Int)) x = .ok (leadingZeros x : Int) := by
  unfold Std.Bits.Count_Leading_Zero_Bits X86.Runtime.intRangeDown leadingZeros highestSetBit?
  simp only [x86_runtime]
  have key : ∀ l : List Nat, (∀ i ∈ l, i < n) →
      forIn (m := Except (X86.Runtime.Error Empty))
        (List.map (fun i : Nat => (n : Int) - 1 - (i : Int)) l)
        ((none, ()) : Option Int × Unit)
        (fun i (_ : Option Int × Unit) => do
          let b ← X86.Runtime.CheckedSlice.read x i 1
          if (b == 1) = true then pure (ForInStep.done (some ((n : Int) - i - 1), ()))
          else pure (ForInStep.yield (none, ()))) =
        .ok ((l.find? (fun i => x.getLsbD (n - 1 - i))).map (fun i : Nat => (i : Int)), ()) := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a l ih =>
      have ha := hl a (by simp)
      have ih' := ih (fun i hi => hl i (by simp [hi]))
      simp only [List.map_cons, List.forIn_cons]
      rw [checkedSliceRead_eq_pure x (by omega) (by omega) (by omega)]
      simp only [beq_iff_eq] at ih' ⊢
      simp only [pure_bind, Int.reduceToNat, extractLsb'_width_one]
      rw [show ((n : Int) - 1 - (a : Int)).toNat = n - 1 - a by omega]
      cases h : x.getLsbD (n - 1 - a)
      · simpa [h] using ih'
      · simp [h]
        show Except.ok _ = Except.ok _
        congr 3
        omega
  have hr : ((n : Int) - 1 - 0 + 1).toNat = n := by omega
  rw [hr, key _ (fun i hi => List.mem_range.mp hi), List.find?_map]
  simp only [Function.comp_def]
  cases hf : (List.range n).find? (fun i => x.getLsbD (n - 1 - i)) with
  | none => rfl
  | some i =>
    have := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    show Except.ok _ = Except.ok _
    congr 1
    simp only [Option.map_some]
    omega

/-- lean-x86's `Is_Parity_Odd` is `oddBits`. -/
theorem isParityOdd_run (n : Nat) (x : BitVec n) :
    Std.Bits.Is_Parity_Odd (size := (n : Int)) x = .ok (oddBits x) := by
  unfold Std.Bits.Is_Parity_Odd oddBits
  simp only [x86_runtime, Int.zero_add]
  have key : ∀ (l : List Nat) (b : Bool), (∀ i ∈ l, i < n) →
      forIn (m := Except (X86.Runtime.Error Empty)) (List.map (fun i : Nat => (i : Int)) l)
        (BitVec.ofBool b : X86.Runtime.Bit)
        (fun i (r : X86.Runtime.Bit) => do
          let c ← X86.Runtime.CheckedSlice.read x i 1
          pure (ForInStep.yield (r ^^^ c))) =
        .ok (BitVec.ofBool (l.foldl (fun r i => r ^^ x.getLsbD i) b)) := by
    intro l
    induction l with
    | nil => intro b _; rfl
    | cons a l ih =>
      intro b hl
      have ha := hl a (by simp)
      simp only [List.map_cons, List.forIn_cons]
      rw [checkedSliceRead_eq_pure x (by omega) (by omega) (by omega)]
      simp only [pure_bind, Int.toNat_natCast, Int.reduceToNat, extractLsb'_width_one,
        List.foldl_cons]
      rw [← ih (b ^^ x.getLsbD a) (fun i hi => hl i (by simp [hi]))]
      congr 1
      cases b <;> cases x.getLsbD a <;> rfl
  have hr : ((n : Int) - 1 - 0 + 1).toNat = n := by omega
  rw [hr, show (0 : BitVec 1) = BitVec.ofBool false from rfl,
    key _ _ (fun i hi => List.mem_range.mp hi)]
  show Except.ok _ = Except.ok _
  cases (List.range n).foldl (fun r i => r ^^ x.getLsbD i) false <;> rfl

/-! ### Bit strings in memory -/

section BitString

open BitVec

/-- The byte offset, from a memory bit base, of the `n`-bit operand that holds bit `y` of the bit
string (BT, BTS, BTR, BTC with a register bit offset): the offset is signed and not reduced modulo
`n`, so the operand is `y / n` (rounded down) operands of `n / 8` bytes from the bit base, as the
SDM gives it ("Effective Address + (4 ∗ (BitOffset DIV 32))" at 32 bits); the bit in it is
`y` modulo `n`. -/
def bitStringOffset {n : Nat} (y : BitVec n) : BitVec 64 :=
  BitVec.ofInt 64 (y.toInt / n * (n / 8 : Nat))

/-- Bit `i` of `2 ^ j - 1` is `i < j`. -/
private theorem low_mask_bit (m j i : Nat) (hm : m = 2 ^ j - 1) (hj : j ≤ 3) :
    (BitVec.ofNat 64 m).getLsbD i = decide (i < j) := by
  subst hm
  rw [BitVec.getLsbD_ofNat]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
  · by_cases hi : i < 64
    · simp only [hi, decide_true, Bool.true_and]
      rw [Nat.testBit_two_pow_sub_one]
    · simp only [hi, decide_false, Bool.false_and]
      exact (decide_eq_false (by omega)).symm

/-- An arithmetic shift right by `k`, then left by `j`, of a sign-extended value, as an integer. -/
private theorem sshr_shl_eq_ofInt {w : Nat} (y : BitVec w) (hw : w ≤ 64) (k j : Nat)
    (hj : j < 8) :
    ((y.signExtend 64).sshiftRight k) <<< j = BitVec.ofInt 64 (y.toInt / 2 ^ k * 2 ^ j) := by
  rw [shiftLeft_eq_mul_twoPow]
  apply eq_of_toInt_eq
  rw [toInt_mul, toInt_sshiftRight, toInt_signExtend_of_le hw, toInt_ofInt,
    Int.shiftRight_eq_div_pow, toInt_twoPow]
  simp only [show ¬ 64 ≤ j by omega, show j + 1 ≠ 64 by omega, ↓reduceIte]
  norm_cast

/-- lean-x86's sign-extended `y[w-1:3]` aligned down to `2 ^ j` (`w = 2 ^ (j + 3)`) is `y`
shifted right by `j + 3` and left by `j`. -/
private theorem align_eq {w : Nat} (y : BitVec w) (j : Nat) (hw : w = 2 ^ (j + 3))
    (hj : j ≤ 3) :
    (BitVec.extractLsb' 3 (w - 3) y).signExtend 64 &&& ~~~(BitVec.ofNat 64 (2 ^ j - 1)) =
      ((y.signExtend 64).sshiftRight (j + 3)) <<< j := by
  have hw3 : 8 ≤ w := by
    rw [hw, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]; have := Nat.one_le_two_pow (n := j); omega
  have hw64 : w ≤ 64 := by
    rw [hw, show 64 = 2 ^ 6 from rfl]; exact Nat.pow_le_pow_right (by omega) (by omega)
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [getLsbD_and, getLsbD_not, getLsbD_signExtend, getLsbD_extractLsb',
    getLsbD_sshiftRight, getLsbD_shiftLeft, low_mask_bit _ j i rfl hj, hi, decide_true,
    Bool.true_and]
  by_cases hij : i < j
  · simp [hij]
  · simp only [hij, decide_false, Bool.not_false, Bool.and_true, Bool.true_and,
      show ¬ 64 ≤ i - j by omega, decide_false, Bool.not_false]
    by_cases hlo : i < w - 3
    · simp [hlo, show j + 3 + (i - j) = 3 + i by omega, show 3 + i < 64 by omega,
        show 3 + i < w by omega]
    · have hl : (extractLsb' 3 (w - 3) y).msb = y.msb := by
        simp only [BitVec.msb, getMsbD_extractLsb', Nat.sub_zero]
        rw [decide_eq_true (by omega : 0 < w - 3), decide_eq_true (by omega : 3 + (w - 3) ≤ w),
          show w - (3 + (w - 3)) = 0 by omega]
        rfl
      simp only [hlo, ↓reduceIte, show j + 3 + (i - j) = i + 3 by omega,
        show ¬ i + 3 < w by omega]
      rw [hl]
      by_cases h64 : i + 3 < 64
      · simp [h64]
      · simp [h64, BitVec.msb_signExtend, hw64]
        intro
        rfl


/-- `bitStringOffset` is lean-x86's computation (`w = 2 ^ (j + 3)`). -/
private theorem bitStringOffset_eq {w : Nat} (j : Nat) (hw : w = 2 ^ (j + 3)) (hj : j ≤ 3)
    (y : BitVec w) :
    (BitVec.extractLsb' 3 (w - 3) y).signExtend 64 &&& ~~~(BitVec.ofNat 64 (2 ^ j - 1)) =
      bitStringOffset y := by
  have hw64 : w ≤ 64 := by
    rw [hw, show 64 = 2 ^ 6 from rfl]; exact Nat.pow_le_pow_right (by omega) (by omega)
  rw [align_eq y j hw hj, sshr_shl_eq_ofInt y hw64 _ _ (by omega), bitStringOffset]
  subst hw
  congr 2
  push_cast [Nat.pow_succ]
  omega

/-- `Calculate_Bit_Offset` of a register bit offset at operand size 16, 32 or 64 is
`bitStringOffset`. -/
theorem calculateBitOffset_eq (n : Nat) (hn : n = 16 ∨ n = 32 ∨ n = 64) (y : BitVec n) :
    Calculate_Bit_Offset (operand_size := (n : Int)) y = .ok (bitStringOffset y) := by
  rcases hn with rfl | rfl | rfl
  · rw [← bitStringOffset_eq 1 rfl (by omega)]; rfl
  · rw [← bitStringOffset_eq 2 rfl (by omega)]; rfl
  · rw [← bitStringOffset_eq 3 rfl (by omega)]; rfl

end BitString

/-- The signed product of `a` and `b` truncated to `n` bits (the two- and three-operand IMUL's
result) is their product. -/
theorem ofInt_toInt_mul {n : Nat} (a b : BitVec n) :
    BitVec.ofInt n (a.toInt * b.toInt) = a * b := by
  rw [BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_toInt]

end X86Proofs
