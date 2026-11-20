import X86Proofs.Core.Runtime

/-!
# Lanes of a vector register

The packed-integer SSE instructions (PADDB, PCMPEQW, PMULLW, …) treat a 128-bit XMM value as
`128 / w` lanes of `w` bits and compute each lane of the result from the same lanes of the
operands. The Intel SDM writes them lane by lane (`DEST[7:0] := DEST[7:0] + SRC[7:0]; …`), and
so does lean-x86, with a loop over the lanes that starts from zero and sets one lane per pass.

- `lane w x i`: lane `i` of `x`, bits `i * w` to `i * w + w - 1`.
- `ofLanes n w f`: the `n`-bit value whose lane `i` is `f i` for each `i < n / w`, built as
  lean-x86's loops build it (`setSlice` of each lane in turn, from zero).
- `lane_ofLanes`, `getLsbD_ofLanes`: reading a lane or a bit of `ofLanes`.
- `ofLanes_and`, `ofLanes_or`, `ofLanes_xor`, `ofLanes_andNot`: a bitwise operation applied lane
  by lane is the operation on the whole value.
- `ofInt_max_toNat`, `ofInt_min_toNat`, `ofInt_max_toInt`, `ofInt_min_toInt`: the larger or
  smaller of two lanes, unsigned or signed, as lean-x86 computes it (`Std.Integer.Max` of the
  lanes as integers, back to bits).
- `ofNat_shiftLeft_add_eq_append`: two 128-bit values side by side, as lean-x86's `concatBits`
  computes them, are `++`; `ofNat_shiftLeft_add_eq_append_any`: the same at any widths (the two
  64-bit halves of MOVLPS, MOVHLPS, …).
- `foldl_add_natAbs`: a sum accumulated by a loop.
- `forIn_lanes`: a `for i in [0, k)` loop in `Except` whose every pass yields `g i` of the
  accumulator, as lean-x86's lane loops run once their checks pass, is a `foldl`.
- `forIn_ofLanes`, `forIn_ofLanes_yield`: a lane loop (outermost, or nested in a loop over
  128-bit lanes) that sets lane `i` to `f i` returns `ofLanes n w f`; `ofLanes_full`: a single
  128-bit lane. `forIn_lanesM`, `forIn_ofLanesM`, `forIn_ofLanes_yieldM`: the same in any lawful
  monad (the partial operations' `PartialResult`).
- `forIn_writeSlice`: a loop that writes one bit of initialized bits per lane (lean-x86's
  MOVMSK, building its mask) returns every bit written, the payload `ofLanes k 1 v`.
- `forIn_writeSlice_lanes`: the same for lanes of `w` bits (lean-x86's `Byte_Reverse`, BSWAP),
  payload `ofLanes n w v`.
- `natCast_mul_toNat`, `toNat_natCast_ediv`: the lane offsets lean-x86 computes in `Int`.
- Tactics: `lanes_loop` reduces an unfolded lean-x86 lane operation to the equation for one lane
  (`lanes_disch` discharges the loop's bounds checks); `lane_eq` turns it into an equation
  between the two lane values.
-/

namespace X86Proofs

/-- `x` saturated to a signed `w`-bit value: clamped to `[-2 ^ (w - 1), 2 ^ (w - 1) - 1]` (the
SDM's `SaturateSignedWordToSignedByte`, `SaturateToSignedWord`, …). -/
def saturateSigned (w : Nat) (x : Int) : BitVec w :=
  BitVec.ofInt w (if 2 ^ (w - 1) ≤ x then 2 ^ (w - 1) - 1
    else if x < -2 ^ (w - 1) then -2 ^ (w - 1) else x)

/-- `x` saturated to an unsigned `w`-bit value: clamped to `[0, 2 ^ w - 1]` (the SDM's
`SaturateToUnsignedByte`, `SaturateSignedWordToUnsignedByte`, …). -/
def saturateUnsigned (w : Nat) (x : Int) : BitVec w :=
  BitVec.ofInt w (if 2 ^ w ≤ x then 2 ^ w - 1 else if x < 0 then 0 else x)

/-- Lane `i` of `x` when `x` is split into lanes of `w` bits: bits `i * w` to `i * w + w - 1`. -/
def lane (w : Nat) {n : Nat} (x : BitVec n) (i : Nat) : BitVec w := x.extractLsb' (i * w) w

/-- The `n`-bit value whose `w`-bit lanes are `f 0`, `f 1`, …, `f (n / w - 1)`, from the least
significant lane up (any bits above the last lane are zero). -/
def ofLanes (n w : Nat) (f : Nat → BitVec w) : BitVec n :=
  (List.range (n / w)).foldl (fun r i => X86.Runtime.setSlice r (i * w) w (f i)) 0

theorem getLsbD_foldl_setSlice {n w : Nat} (f : Nat → BitVec w) (r : BitVec n) (m : Nat)
    (hm : m * w ≤ n) (k : Nat) (hk : k < n) :
    ((List.range m).foldl (fun r i => X86.Runtime.setSlice r (i * w) w (f i)) r).getLsbD k =
      if k < m * w then (f (k / w)).getLsbD (k % w) else r.getLsbD k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      getLsbD_setSlice _ _ _ _ _ hk, ih (by rw [Nat.succ_mul] at hm; omega)]
    by_cases h1 : m * w ≤ k ∧ k < m * w + w
    · have hdiv : k / w = m := Nat.div_eq_of_lt_le h1.1 (by rw [Nat.succ_mul]; exact h1.2)
      have hmod : k % w = k - m * w := by
        rw [Nat.mod_eq_sub_mul_div, hdiv, Nat.mul_comm]
      rw [ite_eq_left h1, ite_eq_left (by rw [Nat.succ_mul]; omega), hdiv, hmod]
    · rw [ite_eq_right h1]
      by_cases h2 : k < m * w
      · rw [ite_eq_left h2, ite_eq_left (by rw [Nat.succ_mul]; omega)]
      · rw [ite_eq_right h2, ite_eq_right (by rw [Nat.succ_mul]; omega)]

/-- Bit `k` of `ofLanes n w f`: bit `k % w` of lane `k / w`, or zero above the last lane. -/
theorem getLsbD_ofLanes {n w : Nat} (f : Nat → BitVec w) (k : Nat) (hk : k < n) :
    (ofLanes n w f).getLsbD k = if k < n / w * w then (f (k / w)).getLsbD (k % w) else false := by
  unfold ofLanes
  rw [getLsbD_foldl_setSlice f 0 (n / w) (Nat.div_mul_le_self n w) k hk]
  simp

/-- Lane `i` of `ofLanes n w f` is `f i`, for a lane of the value (`i < n / w`). -/
theorem lane_ofLanes {n w : Nat} (f : Nat → BitVec w) (i : Nat) (hi : i < n / w) :
    lane w (ofLanes n w f) i = f i := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hw : 0 < w := by omega
  have hiw : (i + 1) * w ≤ n / w * w := Nat.mul_le_mul_right w hi
  have hle : n / w * w ≤ n := Nat.div_mul_le_self n w
  rw [Nat.succ_mul] at hiw
  have hdiv : (i * w + j) / w = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (i * w + j) % w = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  simp only [lane, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  rw [getLsbD_ofLanes f _ (by omega), ite_eq_left (by omega), hdiv, hmod]

/-- When `w` divides `n`, the lanes of `x` rebuild `x`. -/
theorem ofLanes_lane {n w : Nat} (hw : 0 < w) (hdvd : w ∣ n) (x : BitVec n) :
    ofLanes n w (lane w x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hn : n / w * w = n := Nat.div_mul_cancel hdvd
  have hkw : k % w < w := Nat.mod_lt _ hw
  rw [getLsbD_ofLanes _ _ hk, ite_eq_left (by omega)]
  simp only [lane, BitVec.getLsbD_extractLsb', hkw, decide_true, Bool.true_and]
  rw [Nat.mul_comm, Nat.div_add_mod]

/-- A lane-wise operation whose lanes depend bit by bit on the operands' lanes is the
operation on the whole value: `getLsbD` of each lane is `op` of the operands' bits. -/
theorem ofLanes_bitwise {n w : Nat} (hw : 0 < w) (hdvd : w ∣ n) (a b c : BitVec n)
    (op : Bool → Bool → Bool) (f : Nat → BitVec w)
    (hf : ∀ i j, j < w → (f i).getLsbD j = op ((lane w a i).getLsbD j) ((lane w b i).getLsbD j))
    (hc : ∀ k, k < n → c.getLsbD k = op (a.getLsbD k) (b.getLsbD k)) :
    ofLanes n w f = c := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hn : n / w * w = n := Nat.div_mul_cancel hdvd
  have hkw : k % w < w := Nat.mod_lt _ hw
  rw [getLsbD_ofLanes _ _ hk, ite_eq_left (by omega), hf _ _ hkw, hc _ hk]
  simp only [lane, BitVec.getLsbD_extractLsb', hkw, decide_true, Bool.true_and]
  rw [Nat.mul_comm, Nat.div_add_mod]

/-- AND applied lane by lane is AND. -/
theorem ofLanes_and {n w : Nat} (hw : 0 < w) (hdvd : w ∣ n) (a b : BitVec n) :
    ofLanes n w (fun i => lane w a i &&& lane w b i) = a &&& b :=
  ofLanes_bitwise hw hdvd a b _ (· && ·) _ (fun _ _ _ => BitVec.getLsbD_and ..)
    (fun _ _ => BitVec.getLsbD_and ..)

/-- OR applied lane by lane is OR. -/
theorem ofLanes_or {n w : Nat} (hw : 0 < w) (hdvd : w ∣ n) (a b : BitVec n) :
    ofLanes n w (fun i => lane w a i ||| lane w b i) = a ||| b :=
  ofLanes_bitwise hw hdvd a b _ (· || ·) _ (fun _ _ _ => BitVec.getLsbD_or ..)
    (fun _ _ => BitVec.getLsbD_or ..)

/-- XOR applied lane by lane is XOR. -/
theorem ofLanes_xor {n w : Nat} (hw : 0 < w) (hdvd : w ∣ n) (a b : BitVec n) :
    ofLanes n w (fun i => lane w a i ^^^ lane w b i) = a ^^^ b :=
  ofLanes_bitwise hw hdvd a b _ (xor · ·) _ (fun _ _ _ => BitVec.getLsbD_xor ..)
    (fun _ _ => BitVec.getLsbD_xor ..)

/-- AND NOT (`~~~a &&& b`) applied lane by lane is AND NOT. -/
theorem ofLanes_andNot {n w : Nat} (hw : 0 < w) (hdvd : w ∣ n) (a b : BitVec n) :
    ofLanes n w (fun i => ~~~lane w a i &&& lane w b i) = ~~~a &&& b :=
  ofLanes_bitwise hw hdvd a b _ (fun x y => !x && y) _
    (fun _ _ hj => by simp [hj]) (fun _ hk => by simp [hk])

/-- The larger of two lanes as unsigned numbers (`Std.Integer.Max` of their values, back to
`w` bits). -/
theorem ofInt_max_toNat {w : Nat} (x y : BitVec w) :
    BitVec.ofInt w (max (x.toNat : Int) (y.toNat : Int)) = if x.toNat ≥ y.toNat then x else y := by
  rw [Int.max_def]
  by_cases h : y.toNat ≤ x.toNat
  · rw [ite_eq_left h]
    by_cases h' : (x.toNat : Int) ≤ y.toNat
    · rw [ite_eq_left h', BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact BitVec.eq_of_toNat_eq (by omega)
    · rw [ite_eq_right h', BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [ite_eq_right h, ite_eq_left (by omega), BitVec.ofInt_natCast, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]

/-- The smaller of two lanes as unsigned numbers. -/
theorem ofInt_min_toNat {w : Nat} (x y : BitVec w) :
    BitVec.ofInt w (min (x.toNat : Int) (y.toNat : Int)) = if x.toNat ≤ y.toNat then x else y := by
  rw [Int.min_def]
  by_cases h : x.toNat ≤ y.toNat
  · rw [ite_eq_left h, ite_eq_left (by omega), BitVec.ofInt_natCast, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  · rw [ite_eq_right h, ite_eq_right (by omega), BitVec.ofInt_natCast, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]

/-- The larger of two lanes as signed numbers. -/
theorem ofInt_max_toInt {w : Nat} (x y : BitVec w) :
    BitVec.ofInt w (max x.toInt y.toInt) = if x.toInt ≥ y.toInt then x else y := by
  rw [Int.max_def]
  by_cases h : y.toInt ≤ x.toInt
  · rw [ite_eq_left h]
    by_cases h' : x.toInt ≤ y.toInt
    · rw [ite_eq_left h', BitVec.ofInt_toInt]
      exact BitVec.eq_of_toInt_eq (by omega)
    · rw [ite_eq_right h', BitVec.ofInt_toInt]
  · rw [ite_eq_right h, ite_eq_left (by omega), BitVec.ofInt_toInt]

/-- The smaller of two lanes as signed numbers. -/
theorem ofInt_min_toInt {w : Nat} (x y : BitVec w) :
    BitVec.ofInt w (min x.toInt y.toInt) = if x.toInt ≤ y.toInt then x else y := by
  rw [Int.min_def]
  by_cases h : x.toInt ≤ y.toInt
  · rw [ite_eq_left h, ite_eq_left h, BitVec.ofInt_toInt]
  · rw [ite_eq_right h, ite_eq_right h, BitVec.ofInt_toInt]

/-- `b` above `a` as one 256-bit value, as lean-x86's `concatBits b a` computes it, is
`b ++ a`. -/
theorem ofNat_shiftLeft_add_eq_append (b a : BitVec 128) :
    BitVec.ofNat 256 (b.toNat <<< 128 + a.toNat) = b ++ a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt a.isLt, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have := b.isLt
  have := a.isLt
  rw [Nat.shiftLeft_eq]
  simp only [Nat.reducePow] at *
  omega

/-- `b` above `a`, as lean-x86's `concatBits b a` computes it, is `b ++ a`, at any widths. -/
theorem ofNat_shiftLeft_add_eq_append_any {m n : Nat} (b : BitVec m) (a : BitVec n) :
    BitVec.ofNat (m + n) (b.toNat <<< n + a.toNat) = b ++ a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt a.isLt, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have := b.isLt
  have := a.isLt
  rw [Nat.shiftLeft_eq, Nat.pow_add]
  calc b.toNat * 2 ^ n + a.toNat < (b.toNat + 1) * 2 ^ n := by rw [Nat.succ_mul]; omega
    _ ≤ 2 ^ m * 2 ^ n := Nat.mul_le_mul_right _ (by omega)

/-- A loop that adds `f j` to an integer accumulator for each `j` of `l` adds their sum. -/
theorem foldl_add_natAbs (f : Nat → Nat) (l : List Nat) (init : Int) :
    l.foldl (fun s j => s + (f j : Int)) init = init + ((l.map f).sum : Nat) := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => simp [ih]; omega

/-- A `for` loop over `0, 1, …, k - 1` (as lean-x86's `intRange 0 (k - 1)` gives them) in
`Except`, whose pass `i` yields `g i` of the accumulator, returns the `foldl` of `g`. -/
theorem forIn_lanes {ε β : Type} (k : Nat) (init : β)
    (body : Int → β → Except ε (ForInStep β)) (g : Nat → β → β)
    (h : ∀ i < k, ∀ r, body i r = .ok (.yield (g i r))) :
    forIn ((List.range k).map (fun i : Nat => (0 : Int) + (i : Int))) init body =
      .ok ((List.range k).foldl (fun r i => g i r) init) := by
  simp only [Int.zero_add]
  rw [List.forIn_map]
  have : ∀ l : List Nat, (∀ i ∈ l, i < k) → ∀ init,
      forIn (m := Except ε) l init (fun (i : Nat) (r : β) => body (i : Int) r) =
      Except.ok (l.foldl (fun r i => g i r) init) := by
    intro l hl
    induction l with
    | nil => intro; rfl
    | cons a l ih =>
      intro init
      rw [List.forIn_cons, h a (hl a (by simp)) init]
      exact ih (fun i hi => hl i (by simp [hi])) _
  exact this _ (fun i hi => List.mem_range.mp hi) init

/-- lean-x86's lane loop, from zero, setting lane `i` to `f i` on pass `i`, returns
`ofLanes n w f`. -/
theorem forIn_ofLanes {ε : Type} (n w k : Nat) (hk : n / w = k) (f : Nat → BitVec w)
    (body : Int → BitVec n → Except ε (ForInStep (BitVec n)))
    (h : ∀ i < k, ∀ r, body i r = .ok (.yield (X86.Runtime.setSlice r (i * w) w (f i)))) :
    forIn ((List.range k).map (fun i : Nat => (0 : Int) + (i : Int))) 0 body =
      .ok (ofLanes n w f) := by
  subst hk
  exact forIn_lanes _ _ _ _ h

/-- The offset of lane `i` as lean-x86 computes it, `(i * w).toNat` in `Int`, is `i * w`. -/
theorem natCast_mul_toNat (i : Nat) (w : Int) (hw : 0 ≤ w) :
    ((i : Int) * w).toNat = i * w.toNat := by
  obtain ⟨v, rfl⟩ : ∃ v : Nat, w = v := ⟨w.toNat, (Int.toNat_of_nonneg hw).symm⟩
  rw [← Int.natCast_mul, Int.toNat_natCast, Int.toNat_natCast]

/-- `(i / k).toNat` for a natural number `i` and `k ≥ 0`: the natural-number quotient. -/
theorem toNat_natCast_ediv (i : Nat) (k : Int) (hk : 0 ≤ k) :
    ((i : Int) / k).toNat = i / k.toNat := by
  obtain ⟨v, rfl⟩ : ∃ v : Nat, k = v := ⟨k.toNat, (Int.toNat_of_nonneg hk).symm⟩
  rw [← Int.natCast_ediv, Int.toNat_natCast, Int.toNat_natCast]

/-- A lane of `ofLanes` that fills the whole value is that value. -/
theorem ofLanes_full {n : Nat} (hn : 0 < n) (x : BitVec n) : ofLanes n n (fun _ => x) = x := by
  simp [ofLanes, Nat.div_self hn, setSlice_full]

/-- `forIn_ofLanes` for an inner lane loop whose result the outer loop's pass yields, as in
lean-x86's operations that loop over 128-bit lanes and then over elements. -/
theorem forIn_ofLanes_yield {ε : Type} (n w k : Nat) (hk : n / w = k) (f : Nat → BitVec w)
    (body : Int → BitVec n → Except ε (ForInStep (BitVec n)))
    (h : ∀ i < k, ∀ r, body i r = .ok (.yield (X86.Runtime.setSlice r (i * w) w (f i)))) :
    (forIn ((List.range k).map (fun i : Nat => (0 : Int) + (i : Int))) 0 body >>=
        fun s => (pure (ForInStep.yield s) : Except ε (ForInStep (BitVec n)))) =
      .ok (.yield (ofLanes n w f)) := by
  rw [forIn_ofLanes n w k hk f body h]
  rfl

/-- `forIn_lanes` in any lawful monad (lean-x86's partial operations run their lane loops in
`PartialResult`). -/
theorem forIn_lanesM {m : Type → Type} [Monad m] [LawfulMonad m] {β : Type} (k : Nat) (init : β)
    (body : Int → β → m (ForInStep β)) (g : Nat → β → β)
    (h : ∀ i < k, ∀ r, body i r = pure (.yield (g i r))) :
    forIn ((List.range k).map (fun i : Nat => (0 : Int) + (i : Int))) init body =
      pure ((List.range k).foldl (fun r i => g i r) init) := by
  simp only [Int.zero_add]
  rw [List.forIn_map]
  have : ∀ l : List Nat, (∀ i ∈ l, i < k) → ∀ init,
      forIn (m := m) l init (fun (i : Nat) (r : β) => body (i : Int) r) =
      pure (l.foldl (fun r i => g i r) init) := by
    intro l hl
    induction l with
    | nil => intro; rfl
    | cons a l ih =>
      intro init
      rw [List.forIn_cons, h a (hl a (by simp)) init, pure_bind]
      exact ih (fun i hi => hl i (by simp [hi])) _
  exact this _ (fun i hi => List.mem_range.mp hi) init

/-- `forIn_ofLanes` in any lawful monad. -/
theorem forIn_ofLanesM {m : Type → Type} [Monad m] [LawfulMonad m] (n w k : Nat) (hk : n / w = k)
    (f : Nat → BitVec w) (body : Int → BitVec n → m (ForInStep (BitVec n)))
    (h : ∀ i < k, ∀ r, body i r = pure (.yield (X86.Runtime.setSlice r (i * w) w (f i)))) :
    forIn ((List.range k).map (fun i : Nat => (0 : Int) + (i : Int))) 0 body =
      pure (ofLanes n w f) := by
  subst hk
  exact forIn_lanesM _ _ _ _ h

/-- `forIn_ofLanes_yield` in any lawful monad. -/
theorem forIn_ofLanes_yieldM {m : Type → Type} [Monad m] [LawfulMonad m] (n w k : Nat)
    (hk : n / w = k) (f : Nat → BitVec w) (body : Int → BitVec n → m (ForInStep (BitVec n)))
    (h : ∀ i < k, ∀ r, body i r = pure (.yield (X86.Runtime.setSlice r (i * w) w (f i)))) :
    (forIn ((List.range k).map (fun i : Nat => (0 : Int) + (i : Int))) 0 body >>=
        fun s => (pure (ForInStep.yield s) : m (ForInStep (BitVec n)))) =
      pure (.yield (ofLanes n w f)) := by
  rw [forIn_ofLanesM n w k hk f body h, pure_bind]

/-- A loop over lanes `l` that writes bit `i` of initialized bits to `v i` on pass `i` (as
lean-x86's MOVMSK builds its mask) sets those bits of the payload and marks them written. -/
theorem forIn_writeSlice_aux {ε : Type} {n : Int} (k : Nat) (v : Nat → BitVec 1)
    (body : Int → X86.Runtime.InitializedBits n →
      Except ε (ForInStep (X86.Runtime.InitializedBits n)))
    (h : ∀ i < k, ∀ p u : BitVec n.toNat, body (i : Int) (.mk p u) =
      .ok (.yield (.mk (X86.Runtime.setSlice p (i * 1) 1 (v i))
        (X86.Runtime.setSlice u (i * 1) 1 0)))) :
    ∀ (l : List Nat), (∀ i ∈ l, i < k) → ∀ p u : BitVec n.toNat,
      forIn l (X86.Runtime.InitializedBits.mk p u) (fun (i : Nat) r => body (i : Int) r) =
        .ok (X86.Runtime.InitializedBits.mk
          (l.foldl (fun r i => X86.Runtime.setSlice r (i * 1) 1 (v i)) p)
          (l.foldl (fun r i => X86.Runtime.setSlice r (i * 1) 1 0) u)) := by
  intro l hl
  induction l with
  | nil => intro p u; rfl
  | cons a l ih =>
    intro p u
    rw [List.forIn_cons, h a (hl a (by simp)) p u]
    exact ih (fun i hi => hl i (by simp [hi])) _ _

/-- lean-x86's loop that builds a mask in initialized bits, from nothing written, writing bit `i`
to `v i` on each of the `k` passes, returns every bit written, with payload `ofLanes k 1 v`. -/
theorem forIn_writeSlice {ε : Type} {n : Int} (k : Nat) (hk : n.toNat = k) (v : Nat → BitVec 1)
    (body : Int → X86.Runtime.InitializedBits n →
      Except ε (ForInStep (X86.Runtime.InitializedBits n)))
    (h : ∀ i < k, ∀ p u : BitVec n.toNat, body (i : Int) (.mk p u) =
      .ok (.yield (.mk (X86.Runtime.setSlice p (i * 1) 1 (v i))
        (X86.Runtime.setSlice u (i * 1) 1 0)))) :
    forIn ((List.range k).map (fun i : Nat => (0 : Int) + (i : Int)))
        (X86.Runtime.InitializedBits.empty n) body =
      .ok (X86.Runtime.InitializedBits.mk (ofLanes n.toNat 1 v) 0) := by
  simp only [Int.zero_add]
  rw [List.forIn_map, empty_eq_mk,
    forIn_writeSlice_aux k v body h _ (fun i hi => List.mem_range.mp hi)]
  congr
  · simp [hk]
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [getLsbD_foldl_setSlice _ _ k (by omega) j hj]
    simp
    omega

/-- A loop over lanes `l` that writes lane `i` (`w` bits) of initialized bits to `v i` on pass `i`
sets those lanes of the payload and marks them written. -/
theorem forIn_writeSlice_lanes_aux {ε : Type} {n : Int} (w k : Nat) (v : Nat → BitVec w)
    (body : Int → X86.Runtime.InitializedBits n →
      Except ε (ForInStep (X86.Runtime.InitializedBits n)))
    (h : ∀ i < k, ∀ p u : BitVec n.toNat, body (i : Int) (.mk p u) =
      .ok (.yield (.mk (X86.Runtime.setSlice p (i * w) w (v i))
        (X86.Runtime.setSlice u (i * w) w 0)))) :
    ∀ (l : List Nat), (∀ i ∈ l, i < k) → ∀ p u : BitVec n.toNat,
      forIn l (X86.Runtime.InitializedBits.mk p u) (fun (i : Nat) r => body (i : Int) r) =
        .ok (X86.Runtime.InitializedBits.mk
          (l.foldl (fun r i => X86.Runtime.setSlice r (i * w) w (v i)) p)
          (l.foldl (fun r i => X86.Runtime.setSlice r (i * w) w 0) u)) := by
  intro l hl
  induction l with
  | nil => intro p u; rfl
  | cons a l ih =>
    intro p u
    rw [List.forIn_cons, h a (hl a (by simp)) p u]
    exact ih (fun i hi => hl i (by simp [hi])) _ _

/-- lean-x86's loop that fills initialized bits lane by lane (`Byte_Reverse`), from nothing
written, writing lane `i` of `w` bits to `v i` on each of the `k` passes that cover the value,
returns every bit written, with payload `ofLanes n w v`. -/
theorem forIn_writeSlice_lanes {ε : Type} {n : Int} (w k : Nat) (hw : 0 < w)
    (hk : n.toNat = k * w) (v : Nat → BitVec w)
    (body : Int → X86.Runtime.InitializedBits n →
      Except ε (ForInStep (X86.Runtime.InitializedBits n)))
    (h : ∀ i < k, ∀ p u : BitVec n.toNat, body (i : Int) (.mk p u) =
      .ok (.yield (.mk (X86.Runtime.setSlice p (i * w) w (v i))
        (X86.Runtime.setSlice u (i * w) w 0)))) :
    forIn ((List.range k).map (fun i : Nat => (0 : Int) + (i : Int)))
        (X86.Runtime.InitializedBits.empty n) body =
      .ok (X86.Runtime.InitializedBits.mk (ofLanes n.toNat w v) 0) := by
  simp only [Int.zero_add]
  rw [List.forIn_map, empty_eq_mk,
    forIn_writeSlice_lanes_aux w k v body h _ (fun i hi => List.mem_range.mp hi)]
  congr
  · rw [hk, Nat.mul_div_cancel _ hw]
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [getLsbD_foldl_setSlice _ _ k (by omega) j hj]
    simp
    omega

/-- The side conditions of lean-x86's lane loops (`assert`s on lane offsets, slice bounds),
for a lane index below the lane count. -/
macro "lanes_disch" : tactic =>
  `(tactic| first | rfl | omega | (simp only [decide_eq_true_eq]; omega))

/-- Reduce a lean-x86 lane operation (after `unfold`) to one pass of its lane loop: run the
checks before the loop, replace the loop by `ofLanes` of the specification's lane function
(`forIn_ofLanes`), and run the pass for a lane `i` below the lane count, leaving the equation
between the lane lean-x86 writes and the specification's. -/
macro "lanes_loop" : tactic => `(tactic| (
  simp only [x86_runtime, pure_bind, bind_pure, Int.reduceDiv]
  refine forIn_ofLanes _ _ _ (by rfl) _ _ (fun i hi r => ?_)
  simp (disch := lanes_disch) only [x86_runtime, pure_bind, Int.toNat_mul, Int.toNat_add,
    Int.toNat_natCast, toNat_natCast_ediv, natCast_mul_toNat, Int.pow_zero, Int.ediv_one,
    Int.pow_one, BitVec.cast_eq]
  try simp only [pure, Except.pure, lane]))

/-- Turn the equation `lanes_loop` leaves into one between the two lane values. -/
macro "lane_eq" : tactic => `(tactic|
  refine congrArg (fun v => Except.ok (ForInStep.yield (X86.Runtime.setSlice _ _ _ v))) ?_)

end X86Proofs
