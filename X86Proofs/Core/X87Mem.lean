import X86Proofs.Core.X87Arith
import X86Proofs.Core.Shift
import X86.Helpers.FP87.Convert_From_Float
import X86.Helpers.FP87.Convert_From_Integer
import X86.Helpers.FP87.Convert_To_Float
import X86.Helpers.FP87.Convert_To_Integer

/-!
# x87 memory operands: conversions to and from the 80-bit format

The x87 memory forms convert their operand between the 80-bit register format and a memory
format: single or double precision (`m32fp`, `m64fp`) or a signed integer (`m16int`, `m32int`,
`m64int`).

- Loads. `FP87.Convert_From_Float` and `FP87.Convert_From_Integer` are `PartialResult`s: a
  denormal single or double, and every integer, is normalized by `FP87.Normalize`, a `while` loop
  that shifts the significand left until its top bit is set. The loop ends (`fp87Normalize_ok`: a
  shift doubles a nonzero significand below `2^63`), so both conversions return a value on every
  operand (`partial_ok`, a tactic that steps through such a computation). `x87FromFloat x` is the
  value and whether `x` was denormal, `x87FromInt x` the value; `fp87ConvertFromFloat_eq32` etc.
  state lean-x86's conversion as `pure` of them. Every single, double and integer is exactly
  representable in the 80-bit format, and lean-x86's conversion is exact.
- Stores. `FP87.Convert_To_Float x N` rounds by the control word (`ReadsFcw`, as the arithmetic
  helpers of `Core/X87Arith.lean`): `x87ToFloat N fcw x` is the result, whether it was rounded up
  and the exception flags, with its definedness predicate `X87ToFloatOk`. `FP87.Convert_To_Integer
  x rc N` is a pure function of the rounding control: `x87ToInt rc N x` with `X87ToIntOk`.
- Arithmetic and comparison with a memory operand pass whether the converted operand was
  denormal to lean-x86's helpers: `x87ArithD op fcw dx dy x y` (`X87ArithDOk`) generalizes
  `x87Arith op fcw x y` (`dx`, `dy` false), `x87CompareD ordered d x y` (`X87CompareDOk`)
  generalizes `x87Compare`.

This file is the one that unfolds lean-x86's `FP87.Normalize`, `FP87.Convert_From_Float`,
`FP87.Convert_From_Integer`, `FP87.Convert_To_Float`, `F80_Type.setMantissa` and
`F80_Type.setExponent`.
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers X86.Runtime

/-! ### `FP87.Normalize` terminates -/

theorem f80Mantissa_setMantissa (v : BitVec 80) (w : BitVec 64) :
    F80_Type.Mantissa (F80_Type.setMantissa v w) = w := by
  rw [f80Mantissa_eq]
  unfold F80_Type.setMantissa
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb', getLsbD_setSlice _ _ _ _ _ (by omega)]
  simp [hi]

theorem f80Mantissa_setExponent (v : BitVec 80) (e : BitVec 15) :
    F80_Type.Mantissa (F80_Type.setExponent v e) = F80_Type.Mantissa v := by
  rw [f80Mantissa_eq, f80Mantissa_eq]
  unfold F80_Type.setExponent
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', getLsbD_setSlice _ _ _ _ _ (by omega)]
  simp only [show ¬ (64 ≤ 0 + i ∧ 0 + i < 64 + 15) by omega, ite_false]

/-- A `while` loop over an 80-bit value (a `PartialLoop` with no state) whose body, while the
significand is nonzero and below `2^63`, doubles it, and otherwise stops, ends. -/
theorem normalize_loop {ε : Type}
    (body : Unit → BitVec 80 → PartialSpecM ε Unit (ForInStep (BitVec 80)))
    (hy : ∀ v : BitVec 80, (F80_Type.Mantissa v).toNat < 2 ^ 63 → F80_Type.Mantissa v ≠ 0 →
      ∃ v', (body () v).run () = some (.ok (.yield v'), ()) ∧
        (F80_Type.Mantissa v').toNat = 2 * (F80_Type.Mantissa v).toNat)
    (hd : ∀ v : BitVec 80, ¬ ((F80_Type.Mantissa v).toNat < 2 ^ 63 ∧ F80_Type.Mantissa v ≠ 0) →
      (body () v).run () = some (.ok (.done v), ())) :
    ∀ x : BitVec 80, ∃ r, PartialLoop.forIn x body () = some (.ok r, ()) := by
  suffices H : ∀ k : Nat, ∀ x : BitVec 80, 2 ^ 64 - (F80_Type.Mantissa x).toNat ≤ k →
      ∃ r, PartialLoop.forIn x body () = some (.ok r, ()) from
    fun x => H _ x (Nat.le_refl _)
  intro k
  induction k with
  | zero =>
    intro x hk
    have hlt := (F80_Type.Mantissa x).isLt
    exact ⟨x, partialSpecM_loop_done_run _ _ _ (hd x (by omega))⟩
  | succ k ih =>
    intro x hk
    by_cases hc : (F80_Type.Mantissa x).toNat < 2 ^ 63 ∧ F80_Type.Mantissa x ≠ 0
    · obtain ⟨v', hv', hm⟩ := hy x hc.1 hc.2
      have hpos : 0 < (F80_Type.Mantissa x).toNat := by
        rcases Nat.eq_zero_or_pos (F80_Type.Mantissa x).toNat with h0 | h0
        · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hc.2
        · exact h0
      obtain ⟨r, hr⟩ := ih v' (by omega)
      exact ⟨r, partialSpecM_loop_yield_run _ _ _ _ hv' hr⟩
    · exact ⟨x, partialSpecM_loop_done_run _ _ _ (hd x hc)⟩

/-- `normalize_loop` for a loop in `PartialResult` (lean-x86's `while` in a pure helper). -/
theorem partialResult_normalize_loop {ε : Type}
    (body : Unit → BitVec 80 → PartialResult ε (ForInStep (BitVec 80)))
    (hy : ∀ v : BitVec 80, (F80_Type.Mantissa v).toNat < 2 ^ 63 → F80_Type.Mantissa v ≠ 0 →
      ∃ v', (body () v).run = some (.ok (.yield v')) ∧
        (F80_Type.Mantissa v').toNat = 2 * (F80_Type.Mantissa v).toNat)
    (hd : ∀ v : BitVec 80, ¬ ((F80_Type.Mantissa v).toNat < 2 ^ 63 ∧ F80_Type.Mantissa v ≠ 0) →
      (body () v).run = some (.ok (.done v))) (x : BitVec 80) :
    ∃ r, (forIn PartialLoop.mk x body : PartialResult ε _).run = some (.ok r) := by
  obtain ⟨r, hr⟩ := normalize_loop (ε := ε)
    (fun t v _ => Option.map (fun result => (result, ())) (body t v).run)
    (fun v h1 h2 => by
      obtain ⟨v', hv', hm⟩ := hy v h1 h2
      exact ⟨v', by simp only [hv']; rfl, hm⟩)
    (fun v h => by simp only [hd v h]; rfl) x
  refine ⟨r, ?_⟩
  show (PartialLoop.forIn (σ := Unit) x _ ()).map Prod.fst = _
  rw [hr]
  rfl

/-- lean-x86's `FP87.Normalize` ends on every value (each pass doubles the significand). -/
theorem fp87Normalize_ok (x : BitVec 80) : ∃ v, (FP87.Normalize x).run = some (.ok v) := by
  unfold FP87.Normalize
  simp only [bind_pure]
  apply partialResult_normalize_loop
  · intro v h1 h2
    have hb : (F80_Type.Mantissa v).extractLsb' 63 1 = 0#1 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h1]
    have hsl : Std.Bits.Shift_Left_Logical (size := 64) (F80_Type.Mantissa v) 1 =
        .ok (F80_Type.Mantissa v <<< 1) := by
      have := shiftLeftLogical_run (size := 64) (F80_Type.Mantissa v) 1 (by decide)
      simpa using this
    have hne : (F80_Type.Mantissa v == 0) = false := by simpa using h2
    simp only [x86_runtime, hb, hne, hsl]
    refine ⟨_, rfl, ?_⟩
    rw [f80Mantissa_setExponent, f80Mantissa_setMantissa, BitVec.toNat_shiftLeft,
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by simp; omega)]
    omega
  · intro v h
    have h64 : (F80_Type.Mantissa v).toNat < 2 ^ 64 := by
      simpa using (F80_Type.Mantissa v).isLt
    by_cases h0 : F80_Type.Mantissa v = 0
    · simp only [x86_runtime, h0]
      rfl
    · have h1 : ¬ (F80_Type.Mantissa v).toNat < 2 ^ 63 := fun h' => h ⟨h', h0⟩
      have hb : (F80_Type.Mantissa v).extractLsb' 63 1 = 1#1 := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]
        rw [Nat.shiftRight_eq_div_pow]
        omega
      simp only [x86_runtime, hb]
      rfl

/-! ### Quiet NaNs -/

/-- The quiet NaN of a NaN `x`: its quiet bit (62, the fraction's top bit) set. -/
def x87Quiet (x : BitVec 80) : BitVec 80 := x ||| 0x4000000000000000#80

theorem quietizeNaN_eq (x : BitVec 80) (h : fp87Class x = .FP87_Class_SNaN) :
    FP87.Quietize_NaN x = .ok (x87Quiet x) := by
  unfold FP87.Quietize_NaN
  simp only [x86_runtime, classify_eq, h, bind, pure, Except.bind, Except.pure]
  simp only [x86_runtime, Bool.true_or, beq_self_eq_true]
  show Except.ok _ = _
  congr 1
  unfold F80_Type.setMantissa x87Quiet
  rw [f80Mantissa_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_setSlice _ _ _ _ _ hi]
  by_cases h64 : i < 64
  · simp only [show 0 ≤ i ∧ i < 0 + 64 from ⟨Nat.zero_le _, by omega⟩, BitVec.getLsbD_or,
      BitVec.getLsbD_cast, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofNat, Nat.sub_zero,
      Nat.zero_add]
    rfl
  · simp only [show ¬ (0 ≤ i ∧ i < 0 + 64) by omega, ite_false, BitVec.getLsbD_or]
    have hc : (4611686018427387904#80).getLsbD i = false := by
      simp only [BitVec.getLsbD, BitVec.toNat_ofNat]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 4611686018427387904 < 2 ^ 64)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hc, Bool.or_false]

/-! ### Stepping through a terminating `PartialResult` -/

theorem partialResult_bind_ok {ε α β : Type} {m : PartialResult ε α} {k : α → PartialResult ε β}
    (hm : ∃ a, m.run = some (.ok a)) (hk : ∀ a, ∃ v, (k a).run = some (.ok v)) :
    ∃ v, (m >>= k).run = some (.ok v) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨v, hv⟩ := hk a
  exact ⟨v, by simp only [ExceptT.run_bind, ha]; exact hv⟩

theorem partialResult_ite_ok {ε α : Type} {c : Prop} [Decidable c] {a b : PartialResult ε α}
    (ha : c → ∃ v, a.run = some (.ok v)) (hb : ¬ c → ∃ v, b.run = some (.ok v)) :
    ∃ v, (if c then a else b).run = some (.ok v) := by
  by_cases h : c
  · simp only [h, ite_true]
    exact ha h
  · simp only [h, ite_false]
    exact hb h

theorem partialResult_ite_bind_ok {ε α β : Type} {c : Prop} [Decidable c]
    {a b : PartialResult ε α} {k : α → PartialResult ε β}
    (ha : c → ∃ v, (a >>= k).run = some (.ok v)) (hb : ¬ c → ∃ v, (b >>= k).run = some (.ok v)) :
    ∃ v, ((if c then a else b) >>= k).run = some (.ok v) := by
  by_cases h : c
  · simp only [h, ite_true]
    exact ha h
  · simp only [h, ite_false]
    exact hb h

open Lean Meta Elab Tactic in
/-- One step of `partial_ok` on a goal `∃ v, m.run = some (.ok v)`: a bind of `FP87.Normalize`
by `fp87Normalize_ok`, a bind of a branch or a branch by cases on its condition, a bind of
anything else by its value (`rfl`), and a value by `rfl`. -/
elab "partial_ok_step" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  if tgt.isForall then
    evalTactic (← `(tactic| intro _))
    return
  let some (_, body) := tgt.app2? ``Exists | throwError "partial_ok: not an ∃ goal"
  let .lam _ _ eq _ := body | throwError "partial_ok: unexpected goal"
  let some (_, lhs, _) := eq.eq? | throwError "partial_ok: not an equation"
  let m := lhs.appArg!.consumeMData
  if m.isLet || m.isAppOf ``letFun || m.getAppFn.isLambda then
    evalTactic (← `(tactic| dsimp only))
    return
  let head := m.getAppFn.constName?.getD .anonymous
  if head == ``Bind.bind then
    let args := m.getAppArgs
    let first := (args[args.size - 2]!).consumeMData
    let fh := first.getAppFn.constName?.getD .anonymous
    if fh == ``X86.Helpers.FP87.Normalize then
      evalTactic (← `(tactic| refine partialResult_bind_ok (fp87Normalize_ok _) (fun _ => ?_)))
    else if fh == ``ite then
      evalTactic (← `(tactic| refine partialResult_ite_bind_ok (fun _ => ?_) (fun _ => ?_)))
    else
      evalTactic (← `(tactic| refine partialResult_bind_ok ⟨_, rfl⟩ (fun _ => ?_)))
  else if head == ``ite then
    evalTactic (← `(tactic| refine partialResult_ite_ok (fun _ => ?_) (fun _ => ?_)))
  else
    evalTactic (← `(tactic| exact ⟨_, rfl⟩))

/-- Prove that a lean-x86 `PartialResult` helper whose only loop is `FP87.Normalize` returns a
value. -/
macro "partial_ok" : tactic => `(tactic| repeat' partial_ok_step)

/-! ### Loads: to the 80-bit format -/

/-- The 80-bit value of the single (`size` 32) or double (`size` 64) `x` and whether `x` is
denormal, as lean-x86's `FP87.Convert_From_Float` computes them (exactly: every single and double
is an 80-bit value). -/
def x87FromFloat {size : Int} (x : BitVec size.toNat) : BitVec 80 × Bool :=
  match (FP87.Convert_From_Float (size := size) x).run with
  | some (.ok v) => v
  | _ => default

/-- The 80-bit value of the signed integer `x` (`size` 16, 32 or 64), as lean-x86's
`FP87.Convert_From_Integer` computes it (exactly). -/
def x87FromInt {size : Int} (x : BitVec size.toNat) : BitVec 80 :=
  match (FP87.Convert_From_Integer (size := size) x).run with
  | some (.ok v) => v
  | _ => default

theorem partialResult_eq_pure {ε α : Type} [Inhabited α] {m : PartialResult ε α} {v : α}
    (h : m.run = some (.ok v)) : m = pure v := h

theorem fp87ConvertFromFloat_eq32 (x : BitVec 32) :
    FP87.Convert_From_Float (size := 32) x = pure (x87FromFloat (size := 32) x) := by
  have h : ∃ v, (FP87.Convert_From_Float (size := 32) x).run = some (.ok v) := by
    unfold FP87.Convert_From_Float
    partial_ok
  obtain ⟨v, hv⟩ := h
  rw [partialResult_eq_pure hv]
  unfold x87FromFloat
  rw [hv]

theorem fp87ConvertFromFloat_eq64 (x : BitVec 64) :
    FP87.Convert_From_Float (size := 64) x = pure (x87FromFloat (size := 64) x) := by
  have h : ∃ v, (FP87.Convert_From_Float (size := 64) x).run = some (.ok v) := by
    unfold FP87.Convert_From_Float
    partial_ok
  obtain ⟨v, hv⟩ := h
  rw [partialResult_eq_pure hv]
  unfold x87FromFloat
  rw [hv]

theorem fp87ConvertFromInteger_eq16 (x : BitVec 16) :
    FP87.Convert_From_Integer (size := 16) x = pure (x87FromInt (size := 16) x) := by
  have h : ∃ v, (FP87.Convert_From_Integer (size := 16) x).run = some (.ok v) := by
    unfold FP87.Convert_From_Integer
    partial_ok
  obtain ⟨v, hv⟩ := h
  rw [partialResult_eq_pure hv]
  unfold x87FromInt
  rw [hv]

theorem fp87ConvertFromInteger_eq32 (x : BitVec 32) :
    FP87.Convert_From_Integer (size := 32) x = pure (x87FromInt (size := 32) x) := by
  have h : ∃ v, (FP87.Convert_From_Integer (size := 32) x).run = some (.ok v) := by
    unfold FP87.Convert_From_Integer
    partial_ok
  obtain ⟨v, hv⟩ := h
  rw [partialResult_eq_pure hv]
  unfold x87FromInt
  rw [hv]

theorem fp87ConvertFromInteger_eq64 (x : BitVec 64) :
    FP87.Convert_From_Integer (size := 64) x = pure (x87FromInt (size := 64) x) := by
  have h : ∃ v, (FP87.Convert_From_Integer (size := 64) x).run = some (.ok v) := by
    unfold FP87.Convert_From_Integer
    partial_ok
  obtain ⟨v, hv⟩ := h
  rw [partialResult_eq_pure hv]
  unfold x87FromInt
  rw [hv]

/-! ### Stores: from the 80-bit format -/

theorem convertToFloat_reads32 (x : BitVec 80) :
    ReadsFcw (FP87.Convert_To_Float x 32 : SpecM X86.Exception RamState _) := by
  unfold FP87.Convert_To_Float
  reads_fcw

theorem convertToFloat_reads64 (x : BitVec 80) :
    ReadsFcw (FP87.Convert_To_Float x 64 : SpecM X86.Exception RamState _) := by
  unfold FP87.Convert_To_Float
  reads_fcw

/-- `x` rounded to a single (`n` 32) or double (`n` 64) at control word `fcw`: the result,
whether its magnitude was rounded up, the exception flags (`FP87.Convert_To_Float`). -/
def x87ToFloat (n : Nat) (fcw : BitVec 16) (x : BitVec 80) : BitVec n × Bool × BitVec 6 :=
  laneVal (fcwRun (FP87.Convert_To_Float x n) fcw)

/-- lean-x86 returns a value for `x` rounded to `n` bits at control word `fcw`. -/
def X87ToFloatOk (n : Nat) (fcw : BitVec 16) (x : BitVec 80) : Prop :=
  LaneOk (fcwRun (FP87.Convert_To_Float x n) fcw)

theorem convertToFloat_run (n : Nat) (hn : n = 32 ∨ n = 64) (x : BitVec 80) (s : RamState)
    (hm : FcwMasked s.FP87_Control) (hok : X87ToFloatOk n s.FP87_Control x) :
    (FP87.Convert_To_Float x n : SpecM X86.Exception RamState _).run s =
      (.ok (x87ToFloat n s.FP87_Control x), s) := by
  have hr : ReadsFcw (FP87.Convert_To_Float x n : SpecM X86.Exception RamState _) := by
    rcases hn with rfl | rfl
    · exact convertToFloat_reads32 x
    · exact convertToFloat_reads64 x
  rw [hr.run_eq s hm]
  exact congrArg (fun r => (r, s)) hok.eq

/-- `x` rounded to an `n`-bit signed integer (`n` 16, 32 or 64) with rounding control `rc`: the
result (the integer indefinite `100…0` if out of range), whether it was rounded up, the exception
flags (`FP87.Convert_To_Integer`). -/
def x87ToInt (rc : BitVec 2) (n : Nat) (x : BitVec 80) : BitVec n × Bool × BitVec 6 :=
  match FP87.Convert_To_Integer x rc n true with
  | .ok v => v
  | .error _ => default

/-- lean-x86 returns a value for `x` rounded to an `n`-bit integer with rounding control `rc`. -/
def X87ToIntOk (rc : BitVec 2) (n : Nat) (x : BitVec 80) : Prop :=
  ∃ v, FP87.Convert_To_Integer x rc n true = .ok v

theorem X87ToIntOk.eq {rc : BitVec 2} {n : Nat} {x : BitVec 80} (h : X87ToIntOk rc n x) :
    FP87.Convert_To_Integer x rc n true = .ok (x87ToInt rc n x) := by
  obtain ⟨v, hv⟩ := h
  simp only [x87ToInt, hv]

theorem fcwMasked_bit {fcw : BitVec 16} (h : FcwMasked fcw) (i : Nat) (hi : i < 6) :
    fcw.extractLsb' i 1 = 1#1 := by
  unfold FcwMasked at h
  have h1 : fcw.getLsbD i = true := by
    have := congrArg (fun x => x.getLsbD i) h
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.zero_add] at this
    rw [this]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rcases (by omega : j = 0) with rfl
  simpa using h1

/-- With every exception masked, no exception is unmasked. -/
theorem isUnmaskedException_fcwMasked (f : BitVec 6) {fcw : BitVec 16} (hm : FcwMasked fcw) :
    FP87.Is_Unmasked_Exception f (fcw.extractLsb' 0 6) = .ok false := by
  unfold FcwMasked at hm
  rw [hm]
  exact isUnmaskedException_masked f

/-- With every exception masked, the overflow mask OM (bit 3) reads 1. -/
theorem fp87ControlOM_run_masked {σ : Type} (s : X86.State σ) (hm : FcwMasked s.FP87_Control) :
    (X86.FP87_Control.OM : SpecM X86.Exception (X86.State σ) _).run s = (.ok 1#1, s) := by
  rw [← fcwMasked_bit hm 3 (by decide)]
  simp [X86.FP87_Control.OM, x86_runtime]
  rfl

/-- With every exception masked, the underflow mask UM (bit 4) reads 1. -/
theorem fp87ControlUM_run_masked {σ : Type} (s : X86.State σ) (hm : FcwMasked s.FP87_Control) :
    (X86.FP87_Control.UM : SpecM X86.Exception (X86.State σ) _).run s = (.ok 1#1, s) := by
  rw [← fcwMasked_bit hm 4 (by decide)]
  simp [X86.FP87_Control.UM, x86_runtime]
  rfl

/-- The status word a store's conversion (`Operations.FST_Convert`, `Operations.FIST`) leaves:
C0, C2, C3 the oracle's next three bits, C1 := whether the result was rounded up (`up`), the
exception flags `ex` ORed in, as lean-x86 sets them. -/
def x87StoreStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up : Bool) (ex : BitVec 6) :
    BitVec 16 :=
  fswOrFlags (setSlice (fswSetC fsw (oBit o 0) 0 (oBit o 1) (oBit o 2)) 9 1
    (if up = true then 1 else 0)) ex

@[simp] theorem fswTop_x87StoreStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up : Bool)
    (ex : BitVec 6) : fswTop (x87StoreStatus fsw o up ex) = fswTop fsw := by
  simp (disch := omega) only [x87StoreStatus, fswTop_fswOrFlags, fswTop_setSlice, fswTop_fswSetC]

@[simp] theorem fswES_x87StoreStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up : Bool)
    (ex : BitVec 6) : fswES (x87StoreStatus fsw o up ex) = fswES fsw := by
  simp (disch := omega) only [x87StoreStatus, fswES_fswOrFlags, fswES_setSlice, fswES_fswSetC]

theorem fswRest_x87StoreStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up : Bool)
    (ex : BitVec 6) : fswRest (x87StoreStatus fsw o up ex) = fswOrFlags (fswRest fsw) ex := by
  unfold x87StoreStatus
  fsw_bits
  all_goals cases up <;> simp [getElem_setSlice]

theorem fswCC_x87StoreStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up : Bool)
    (ex : BitVec 6) : fswCC (x87StoreStatus fsw o up ex) &&& 2 = ccC1 up := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [x87StoreStatus, fswCC, ccC1, BitVec.getLsbD_and, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb']
  rcases lt4_cases hi with rfl | rfl | rfl | rfl <;>
    cases up <;> simp [fswOrFlags, fswSetC, getElem_setSlice]

/-- Committing a store's report (C1 := whether rounded up, the flags `ex` ORed in) is
`x87StoreStatus`. -/
theorem x87CommitFsw_store (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up : Bool) (ex : BitVec 6) :
    x87CommitFsw fsw (x87ReportFsw fsw (if up = true then 1 else 0) ex) o =
      x87StoreStatus fsw o up ex := by
  simp only [x87CommitFsw_eq, x87StoreStatus, x87ReportFsw, fswSetC1]
  fsw_bits
  all_goals cases up <;> simp [getElem_setSlice]

/-! ### Arithmetic and comparison with a converted operand -/

/-- lean-x86's helper for `op` as the memory forms call it, with whether `x` (`dx`) or `y` (`dy`)
was a denormal before its conversion (FADD and FMUL take only `dy`). -/
def x87OpMD (op : X87Op) (dx dy : Bool) (x y : BitVec 80) :
    SpecM X86.Exception RamState (BitVec 80 × Bool × BitVec 6) :=
  match op with
  | .add => FP87.Add x y dy
  | .sub => FP87.Subtract x y dx dy
  | .mul => FP87.Multiply x y dy
  | .div => FP87.Divide x y dx dy

theorem fp87AddD_reads (x y : BitVec 80) (dy : Bool) :
    ReadsFcw (FP87.Add x y dy : SpecM X86.Exception RamState _) := by
  reads_fcw

theorem fp87SubtractD_reads (x y : BitVec 80) (dx dy : Bool) :
    ReadsFcw (FP87.Subtract x y dx dy : SpecM X86.Exception RamState _) := by
  reads_fcw

theorem fp87MultiplyD_reads (x y : BitVec 80) (dy : Bool) :
    ReadsFcw (FP87.Multiply x y dy : SpecM X86.Exception RamState _) := by
  reads_fcw

theorem fp87DivideD_reads (x y : BitVec 80) (dx dy : Bool) :
    ReadsFcw (FP87.Divide x y dx dy : SpecM X86.Exception RamState _) := by
  reads_fcw

theorem x87OpMD_reads (op : X87Op) (dx dy : Bool) (x y : BitVec 80) :
    ReadsFcw (x87OpMD op dx dy x y) := by
  cases op
  · exact fp87AddD_reads x y dy
  · exact fp87SubtractD_reads x y dx dy
  · exact fp87MultiplyD_reads x y dy
  · exact fp87DivideD_reads x y dx dy

/-- `x op y` at FCW `fcw` with the denormal flags `dx`, `dy`: the result, whether it was rounded
up, the exception flags. -/
def x87ArithD (op : X87Op) (fcw : BitVec 16) (dx dy : Bool) (x y : BitVec 80) :
    BitVec 80 × Bool × BitVec 6 :=
  laneVal (fcwRun (x87OpMD op dx dy x y) fcw)

/-- lean-x86 returns a value for `x op y` at FCW `fcw` with the denormal flags `dx`, `dy`. -/
def X87ArithDOk (op : X87Op) (fcw : BitVec 16) (dx dy : Bool) (x y : BitVec 80) : Prop :=
  LaneOk (fcwRun (x87OpMD op dx dy x y) fcw)

theorem x87OpMD_run (op : X87Op) (dx dy : Bool) (x y : BitVec 80) (s : RamState)
    (hm : FcwMasked s.FP87_Control) (hok : X87ArithDOk op s.FP87_Control dx dy x y) :
    (x87OpMD op dx dy x y).run s = (.ok (x87ArithD op s.FP87_Control dx dy x y), s) := by
  rw [(x87OpMD_reads op dx dy x y).run_eq s hm]
  exact congrArg (fun r => (r, s)) hok.eq

/-- lean-x86's comparison of `x` with `y` (`FP87.Compare`, ordered or not) with whether `y` was a
denormal before its conversion (`d`): the result `C3 C2 C0` and the exception flags. -/
def x87CompareD (ordered d : Bool) (x y : BitVec 80) : BitVec 3 × BitVec 6 :=
  match FP87.Compare x y ordered d with
  | .ok v => v
  | .error _ => default

/-- lean-x86 returns a value for the comparison of `x` with `y` with denormal flag `d`. -/
def X87CompareDOk (ordered d : Bool) (x y : BitVec 80) : Prop :=
  ∃ v, FP87.Compare x y ordered d = .ok v

theorem X87CompareDOk.eq {ordered d : Bool} {x y : BitVec 80} (h : X87CompareDOk ordered d x y) :
    FP87.Compare x y ordered d = .ok (x87CompareD ordered d x y) := by
  obtain ⟨v, hv⟩ := h
  simp only [x87CompareD, hv]

end X86Proofs
