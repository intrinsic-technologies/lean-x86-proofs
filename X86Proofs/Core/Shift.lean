import X86Proofs.Core.Run
import X86Proofs.Core.Flags
import X86Proofs.Core.Oracle

/-!
# Shifts and rotates: shared lemmas

Shared by the shift and rotate family, not specific to one operation:

- `shiftCount`: the count a shift or rotate uses (the count operand masked to 6 bits at 64 bits,
  5 bits otherwise).
- Flags left unchanged: `StatusFlags.getLsbD_store_eq` (what `StatusFlags.store` does to each RFLAGS bit) and
  `setFlags_eq_of_store`. An operation that leaves some flags unchanged is stated as storing their
  old values (`StatusFlags.ofRFLAGS`; `StatusFlags.store_ofRFLAGS` and `setFlags_ofRFLAGS` in Core/Flags.lean
  for the case where all are unchanged).
- `rflags_ext`: a tactic closing `f.store r = R` for `R` built by lean-x86's one-bit flag writes.
- `unsigned_extractLsb'`: the count lean-x86 slices out of the count operand.
- `rotateLeft_run`, `rotateLeft_run_nat`: lean-x86's `Std.Bits.Rotate_Left` is `BitVec.rotateLeft`;
  `rotateRight_run`, `rotateRight_run_nat`: `Std.Bits.Rotate_Right` is `BitVec.rotateRight`.
- Rotate through carry (RCL, RCR): CF above the operand is `BitVec.cons` (`ofNat_concat_eq_cons`);
  lean-x86's one-bit-at-a-time loops (`rclStep`, `rcrStep`) rotate it (`rcl_fold`, `rcr_fold`).
- `topBit`: the top bit as lean-x86 slices it; `shiftRightArithmetic_one_run`: SAR's one-bit step.
- `shr_fold`, `shl_fold`, `sar_fold`: lean-x86's one-bit-at-a-time shift loops (SHR, SHL, SAR)
  as `>>>`, `<<<`, `sshiftRight` and the last bit shifted out (`shiftLoop_fold`: the general
  loop).
- `shiftLeftLogical_run`, `shiftRightLogical_run`, `shiftRightArithmetic_run`: lean-x86's
  `Shift_Left_Logical`, `Shift_Right_Logical`, `Shift_Right_Arithmetic` by any count (the packed
  shifts PSLL, PSRL, PSRA): `<<<` and `>>>` below the width and zero from it up, `sshiftRight` by
  the count capped at the width.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- The count a shift or rotate by `count` uses at operand size `n`: the low 6 bits of `count`
at 64 bits, the low 5 bits otherwise. -/
def shiftCount (n : Nat) (count : BitVec 8) : Nat :=
  if n = 64 then count.toNat % 64 else count.toNat % 32

/-- The count lean-x86 slices out of an 8-bit count operand, as an integer. -/
theorem unsigned_extractLsb' (count : BitVec 8) (w : Nat) :
    X86.Runtime.Unsigned (count.extractLsb' 0 w) = ((count.toNat % 2 ^ w : Nat) : Int) := by
  simp [x86_runtime, BitVec.extractLsb'_toNat]

theorem shiftCount_lt_64 (n : Nat) (count : BitVec 8) : shiftCount n count < 64 := by
  unfold shiftCount; split <;> omega

/-! ### Flags left unchanged -/

/-- Setting one bit at `lo`: bit `lo` is the new bit, every other bit unchanged. -/
theorem getLsbD_setSlice_one_eq {w : Nat} (r : BitVec w) (lo j : Nat) (v : BitVec 1)
    (hlo : lo < w) :
    (X86.Runtime.setSlice r lo 1 v).getLsbD j = if j = lo then v.getLsbD 0 else r.getLsbD j := by
  split
  · subst j; exact getLsbD_setSlice_one_self r lo v hlo
  · exact getLsbD_setSlice_one r lo j v ‹_›

/-- Each bit of RFLAGS after `StatusFlags.store`: the six status-flag bits from `f`, the rest unchanged. -/
theorem StatusFlags.getLsbD_store_eq (f : StatusFlags) (r : BitVec 64) (j : Nat) :
    (f.store r).getLsbD j =
      if j = 0 then f.CF else if j = 2 then f.PF else if j = 4 then f.AF else
      if j = 6 then f.ZF else if j = 7 then f.SF else if j = 11 then f.OF else r.getLsbD j := by
  simp only [StatusFlags.store, getLsbD_setSlice_one_eq _ _ _ _ (by decide : (0:Nat) < 64),
    getLsbD_setSlice_one_eq _ _ _ _ (by decide : (2:Nat) < 64),
    getLsbD_setSlice_one_eq _ _ _ _ (by decide : (4:Nat) < 64),
    getLsbD_setSlice_one_eq _ _ _ _ (by decide : (6:Nat) < 64),
    getLsbD_setSlice_one_eq _ _ _ _ (by decide : (7:Nat) < 64),
    getLsbD_setSlice_one_eq _ _ _ _ (by decide : (11:Nat) < 64), BitVec.getLsbD_ofBool]
  by_cases h0 : j = 0 <;> by_cases h2 : j = 2 <;> by_cases h4 : j = 4 <;> by_cases h6 : j = 6 <;>
    by_cases h7 : j = 7 <;> by_cases h11 : j = 11 <;> subst_vars <;> simp_all

/-- `setFlags` is a state with RFLAGS replaced: the form a flag computation that writes RFLAGS bit
by bit is compared against. -/
theorem setFlags_eq_of_store {σ : Type} {s : X86.State σ} {f : StatusFlags} {R : BitVec 64}
    (h : f.store s.RFLAGS = R) : setFlags s f = { s with RFLAGS := R } := by
  subst h; rfl

/--
Close `f.store r = R`, where `R` is `r` with some one-bit `setSlice`s (lean-x86's `RFLAGS.setXF`),
bit by bit: each of the six status-flag bits on both sides, and every other bit unchanged.
-/
macro "rflags_ext" : tactic => `(tactic| (
  have hgo (o : X86.Runtime.Oracle) := oracleTakeGo_one o
  simp only [← oracleTake_match_eq_oracleTakeCount] at hgo
  apply BitVec.eq_of_getLsbD_eq; intro j _
  simp (disch := decide) only [StatusFlags.getLsbD_store_eq, getLsbD_setSlice_one_eq,
    Int.reduceToNat, oracleTake_one, hgo]
  clear hgo
  by_cases h0 : j = 0 <;> by_cases h2 : j = 2 <;> by_cases h4 : j = 4 <;>
    by_cases h6 : j = 6 <;> by_cases h7 : j = 7 <;> by_cases h11 : j = 11 <;>
    subst_vars <;> simp_all [StatusFlags.ofRFLAGS, BitVec.msb_eq_getLsbD_last,
      beq_zero_eq_decide, oracleSkip] <;>
    (split <;> simp_all)))

/-! ### Rotate -/

/-- lean-x86's `Rotate_Left` (rotating a doubled copy of `x` and slicing) is `BitVec.rotateLeft`. -/
theorem rotateLeft_run {size : Int} (x : BitVec size.toNat) (c : Int) (hc : 0 ≤ c)
    (hsize : 0 < size) :
    Std.Bits.Rotate_Left (size := size) x c = .ok (x.rotateLeft c.toNat) := by
  have h0 : 0 ≤ size := by omega
  have hm0 : 0 ≤ c % size := Int.emod_nonneg _ (by omega)
  have hm1 : c % size < size := Int.emod_lt_of_pos _ hsize
  have h1 : c % size ≤ size := by omega
  have h2 : size - c % size ≤ size := by omega
  have h3 : size - c % size + size ≤ max (size + size) 0 := by omega
  unfold Std.Bits.Rotate_Left
  simp [x86_runtime, hc, hsize, X86.Runtime.CheckedSlice.read, bind, pure, Except.bind, Except.pure,
    h0, h1, h2, h3]
  obtain ⟨n, rfl⟩ : ∃ n : Nat, size = n := ⟨size.toNat, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k : Nat, c = k := ⟨c.toNat, by omega⟩
  have hn : 0 < n := by omega
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Int.toNat_natCast] at hi ⊢
  have hk : ((k : Int) % (n : Int)).toNat = k % n := by omega
  have hk' : ((n : Int) - (k : Int) % (n : Int)).toNat = n - k % n := by omega
  rw [hk']
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateLeft, BitVec.getLsbD_ofNat, hi]
  have hx : x.toNat < 2 ^ n := by simpa using x.isLt
  rw [Nat.shiftLeft_add_eq_or_of_lt hx]
  have hkn : k % n < n := Nat.mod_lt _ hn
  simp only [decide_true, Bool.true_and, Nat.testBit_or, Nat.testBit_shiftLeft,
    show ((n : Int) + n).toNat = n + n by omega]
  by_cases hik : i < k % n
  · simp [hik, show n - k % n + i < n + n by omega, show ¬ (n ≤ n - k % n + i) by omega]
    rfl
  · simp [hik, show n - k % n + i < n + n by omega, show n ≤ n - k % n + i by omega,
      show n - k % n + i - n = i - k % n by omega]
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide)
      (show n ≤ n - k % n + i by omega)))]
    simp
    rfl

/-- `Rotate_Left` by a count reduced modulo the operand size, as lean-x86's ROL calls it. -/
theorem rotateLeft_run_nat {n : Nat} (x : BitVec n) (c : Nat) (hn : 0 < n) :
    Std.Bits.Rotate_Left (size := (n : Int)) x ((c : Int) % (n : Int)) = .ok (x.rotateLeft c) := by
  rw [rotateLeft_run _ _ (by omega) (by omega)]
  rw [show ((c : Int) % (n : Int)).toNat = c % n by omega]
  exact congrArg _ BitVec.rotateLeft_mod_eq_rotateLeft

/-- lean-x86's `Rotate_Right` (slicing a doubled copy of `x` at the distance) is
`BitVec.rotateRight`. -/
theorem rotateRight_run {size : Int} (x : BitVec size.toNat) (c : Int) (hc : 0 ≤ c)
    (hsize : 0 < size) :
    Std.Bits.Rotate_Right (size := size) x c = .ok (x.rotateRight c.toNat) := by
  have h0 : 0 ≤ size := by omega
  have hm0 : 0 ≤ c % size := Int.emod_nonneg _ (by omega)
  have hm1 : c % size < size := Int.emod_lt_of_pos _ hsize
  have h1 : c % size ≤ size := by omega
  have h3 : c % size + size ≤ max (size + size) 0 := by omega
  unfold Std.Bits.Rotate_Right
  simp [x86_runtime, hc, hsize, X86.Runtime.CheckedSlice.read, bind, pure, Except.bind, Except.pure,
    h0, h1, h3, hm0]
  obtain ⟨n, rfl⟩ : ∃ n : Nat, size = n := ⟨size.toNat, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k : Nat, c = k := ⟨c.toNat, by omega⟩
  have hn : 0 < n := by omega
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Int.toNat_natCast] at hi ⊢
  have hk : ((k : Int) % (n : Int)).toNat = k % n := by omega
  rw [hk]
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight, BitVec.getLsbD_ofNat, hi]
  have hx : x.toNat < 2 ^ n := by simpa using x.isLt
  rw [Nat.shiftLeft_add_eq_or_of_lt hx]
  have hkn : k % n < n := Nat.mod_lt _ hn
  simp only [decide_true, Bool.true_and, Nat.testBit_or, Nat.testBit_shiftLeft,
    show ((n : Int) + n).toNat = n + n by omega]
  by_cases hik : i < n - k % n
  · simp [hik, show k % n + i < n + n by omega, show ¬ (k % n + i ≥ n) by omega]
    rfl
  · simp [hik, show k % n + i < n + n by omega, show k % n + i ≥ n by omega,
      show k % n + i - n = i - (n - k % n) by omega]
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide)
      (show n ≤ k % n + i by omega)))]
    simp
    rfl

/-- `Rotate_Right` by a count reduced modulo the operand size, as lean-x86's ROR calls it. -/
theorem rotateRight_run_nat {n : Nat} (x : BitVec n) (c : Nat) (hn : 0 < n) :
    Std.Bits.Rotate_Right (size := (n : Int)) x ((c : Int) % (n : Int)) =
      .ok (x.rotateRight c) := by
  rw [rotateRight_run _ _ (by omega) (by omega)]
  rw [show ((c : Int) % (n : Int)).toNat = c % n by omega]
  exact congrArg _ BitVec.rotateRight_mod_eq_rotateRight

/-! ### Shift loop -/

/-- lean-x86's SHR loop, run `k ≥ 1` times: each pass sets CF to bit 0 and shifts right by one,
so the value ends as `x >>> k` and CF as bit `k - 1` of `x`, the last bit shifted out. -/
theorem shr_fold {n : Nat} (x : BitVec n) (cf : BitVec 1) (k : Nat) (hk : 0 < k) :
    (Runtime.intRange 0 ((k : Int) - 1)).foldl
        (fun (acc : BitVec n × BitVec 1) (_ : Int) => (acc.1 >>> 1, acc.1.extractLsb' 0 1)) (x, cf) =
      (x >>> k, x.extractLsb' (k - 1) 1) := by
  have hr : Runtime.intRange 0 ((k : Int) - 1) = (List.range k).map (fun i : Nat => (0 : Int) + i) := by
    simp only [x86_runtime]
    congr 2
    omega
  rw [hr, List.foldl_map]
  clear hr
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  clear hk
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, Nat.add_sub_cancel, Prod.mk.injEq]
    constructor
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_ushiftRight]
      congr 1
      omega
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp [BitVec.getLsbD_extractLsb']

/-- A one-bit-at-a-time loop as lean-x86 writes SHL and SAR, run `k ≥ 1` times: each pass sets the
carry to `g` of the value and replaces the value by `f` of it. If `f` steps `F j` to `F (j + 1)`,
the value ends as `F k` and the carry as `g (F (k - 1))`. -/
theorem shiftLoop_fold {n : Nat} (f : BitVec n → BitVec n) (g : BitVec n → BitVec 1)
    (F : Nat → BitVec n) (hF : ∀ j, f (F j) = F (j + 1)) (cf : BitVec 1) (k : Nat)
    (hk : 0 < k) :
    (Runtime.intRange 0 ((k : Int) - 1)).foldl
        (fun (acc : BitVec n × BitVec 1) (_ : Int) => (f acc.1, g acc.1)) (F 0, cf) =
      (F k, g (F (k - 1))) := by
  have hr : Runtime.intRange 0 ((k : Int) - 1) =
      (List.range k).map (fun i : Nat => (0 : Int) + i) := by
    simp only [x86_runtime]
    congr 2
    omega
  rw [hr, List.foldl_map]
  clear hr
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  clear hk
  induction k with
  | zero => simp [hF]
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp [hF]

/-- The top bit of `x` as lean-x86 slices it (`x[n - 1 +: 1]`). -/
def topBit {n : Nat} (x : BitVec n) : BitVec 1 := x.extractLsb' (n - 1) 1

/-- lean-x86's SHL loop, run `k ≥ 1` times: each pass sets CF to the top bit and shifts left by
one, so the value ends as `x <<< k` and CF as the top bit of `x <<< (k - 1)`, the last bit shifted
out. -/
theorem shl_fold {n : Nat} (x : BitVec n) (cf : BitVec 1) (k : Nat) (hk : 0 < k) :
    (Runtime.intRange 0 ((k : Int) - 1)).foldl
        (fun (acc : BitVec n × BitVec 1) (_ : Int) => (acc.1 <<< 1, topBit acc.1)) (x, cf) =
      (x <<< k, topBit (x <<< (k - 1))) := by
  have := shiftLoop_fold (fun y => y <<< 1) topBit (fun j => x <<< j)
    (fun j => by simp only [BitVec.shiftLeft_add]) cf k hk
  simpa using this

/-- lean-x86's `Shift_Right_Arithmetic` by one (a step of SAR's loop) is `sshiftRight 1`. -/
theorem shiftRightArithmetic_one_run {size : Int} (x : BitVec size.toNat) (h : 1 < size) :
    Std.Bits.Shift_Right_Arithmetic (size := size) x 1 = .ok (x.sshiftRight 1) := by
  have h0 : 0 ≤ size := by omega
  have h1 : ¬ size ≤ 0 := by omega
  have h2 : 1 ≤ max size 0 := by omega
  unfold Std.Bits.Shift_Right_Arithmetic Std.Bits.Shift_Right_Arithmetic_Restricted
  simp [x86_runtime, X86.Runtime.shiftRightArithmetic, h, h0, h1, h2, bind, pure, Except.bind,
    Except.pure]

/-- lean-x86's SAR loop, run `k ≥ 1` times: each pass sets CF to bit 0 and shifts right
arithmetically by one, so the value ends as `x.sshiftRight k` and CF as bit 0 of
`x.sshiftRight (k - 1)`, the last bit shifted out. -/
theorem sar_fold {n : Nat} (x : BitVec n) (cf : BitVec 1) (k : Nat) (hk : 0 < k) :
    (Runtime.intRange 0 ((k : Int) - 1)).foldl
        (fun (acc : BitVec n × BitVec 1) (_ : Int) => (acc.1.sshiftRight 1, acc.1.extractLsb' 0 1))
        (x, cf) =
      (x.sshiftRight k, (x.sshiftRight (k - 1)).extractLsb' 0 1) := by
  have := shiftLoop_fold (fun y => y.sshiftRight 1) (fun y => y.extractLsb' 0 1)
    (fun j => x.sshiftRight j) (fun j => by simp only [BitVec.sshiftRight_add]) cf k hk
  simpa using this

/-! ### Rotate through carry -/

/-- `k + 1` modulo `w` from `k` modulo `w`: one more, or 0 when that reaches `w`. -/
theorem succ_mod_eq {k w : Nat} (hw : 0 < w) :
    (k + 1) % w = if k % w + 1 < w then k % w + 1 else 0 := by
  have h := Nat.mod_lt k hw
  have hk := Nat.div_add_mod k w
  generalize k % w = r at *
  generalize k / w = q at *
  subst hk
  split
  · rw [show w * q + r + 1 = (r + 1) + w * q by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt ‹_›]
  · rw [show w * q + r + 1 = w * (q + 1) by rw [Nat.mul_add]; omega, Nat.mul_mod_right]

/-- Rotating left by 0 changes nothing. -/
theorem rotateLeft_zero {w : Nat} (x : BitVec w) : x.rotateLeft 0 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

/-- Rotating right by 0 changes nothing. -/
theorem rotateRight_zero {w : Nat} (x : BitVec w) : x.rotateRight 0 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

/-- Rotating left by `k + 1` is rotating left by `k`, then by one. -/
theorem rotateLeft_succ {w : Nat} (x : BitVec w) (k : Nat) :
    x.rotateLeft (k + 1) = (x.rotateLeft k).rotateLeft 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hw : 0 < w := by omega
  have hr := Nat.mod_lt k hw
  simp only [BitVec.getLsbD_rotateLeft, succ_mod_eq hw]
  generalize k % w = r at *
  simp only [Nat.zero_mod, Nat.zero_add]
  repeat' split
  all_goals first
    | omega
    | (congr 1; omega)
    | (rw [decide_eq_true (by omega : _ < w), Bool.true_and]; congr 1; omega)
    | (rw [decide_eq_true (by omega : _ < w), Bool.true_and, decide_eq_true (by omega : _ < w),
        Bool.true_and]; congr 1; omega)

/-- Rotating right by `k + 1` is rotating right by `k`, then by one. -/
theorem rotateRight_succ {w : Nat} (x : BitVec w) (k : Nat) :
    x.rotateRight (k + 1) = (x.rotateRight k).rotateRight 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hw : 0 < w := by omega
  have hr := Nat.mod_lt k hw
  simp only [BitVec.getLsbD_rotateRight, succ_mod_eq hw]
  generalize k % w = r at *
  simp only [Nat.zero_mod, Nat.zero_add]
  repeat' split
  all_goals first
    | omega
    | (congr 1; omega)
    | (rw [decide_eq_true (by omega : _ < w), Bool.true_and]; congr 1; omega)
    | (rw [decide_eq_true (by omega : _ < w), Bool.true_and, decide_eq_true (by omega : _ < w),
        Bool.true_and]; congr 1; omega)

/-- A loop as lean-x86 writes RCL and RCR (`for _ in 1..k`), whose body replaces the value by `f`
of it, run from `F 0`: if `f` steps `F j` to `F (j + 1)`, it ends at `F k`. -/
theorem rotateLoop_fold {m : Nat} (f : BitVec m → BitVec m) (F : Nat → BitVec m)
    (hF : ∀ j, f (F j) = F (j + 1)) (k : Nat) :
    (Runtime.intRange 1 (k : Int)).foldl (fun (acc : BitVec m) (_ : Int) => f acc) (F 0) = F k := by
  have hr : Runtime.intRange 1 (k : Int) = (List.range k).map (fun i : Nat => (1 : Int) + i) := by
    simp only [x86_runtime]
    congr 2
    omega
  rw [hr, List.foldl_map]
  clear hr
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp [hF]

/-- lean-x86's concatenation of a bit `b` above `x` (`concatBits b x`) is `BitVec.cons`. -/
theorem ofNat_concat_eq_cons {m : Nat} (b : BitVec 1) (x : BitVec m) :
    BitVec.ofNat (m + 1) (b.toNat <<< m + x.toNat) = BitVec.cons (b.getLsbD 0) x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hx : x.toNat < 2 ^ m := x.isLt
  rw [BitVec.getLsbD_ofNat, Nat.shiftLeft_add_eq_or_of_lt hx]
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, BitVec.testBit_toNat, BitVec.getLsbD_cons]
  by_cases h : i = m
  · subst h
    simp [hi]
  · simp only [h, ↓reduceIte]
    by_cases h' : m ≤ i
    · omega
    · simp [h', hi]

/-- One pass of RCL's loop on the `m + 1`-bit value `y` (CF above the operand), as lean-x86
writes it: the low `m` bits move up one, the top bit moves to bit 0. -/
def rclStep {m : Nat} (y : BitVec (m + 1)) : BitVec (m + 1) :=
  BitVec.ofNat (m + 1) ((y.extractLsb' 0 m).toNat <<< 1 + (y.extractLsb' m 1).toNat)

/-- A pass of RCL's loop rotates the `m + 1`-bit value left by one. -/
theorem rclStep_eq {m : Nat} (y : BitVec (m + 1)) : rclStep y = y.rotateLeft 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold rclStep
  have hb : (y.extractLsb' m 1).toNat < 2 ^ 1 := (y.extractLsb' m 1).isLt
  rw [BitVec.getLsbD_ofNat, Nat.shiftLeft_add_eq_or_of_lt hb]
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, BitVec.getLsbD_rotateLeft, BitVec.testBit_toNat,
    BitVec.getLsbD_extractLsb']
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : i = 0 := by omega
    subst_vars
    simp
  · rw [Nat.mod_eq_of_lt (by omega : 1 < m + 1)]
    by_cases h0 : i = 0
    · subst h0
      simp
    · simp [show i ≥ 1 by omega, show ¬ i < 1 by omega, hi, show i - 1 < m by omega]

/-- One pass of RCR's loop on the `m + 1`-bit value `y` (CF above the operand), as lean-x86
writes it: the high `m` bits move down one, bit 0 moves to the top. -/
def rcrStep {m : Nat} (y : BitVec (m + 1)) : BitVec (m + 1) :=
  BitVec.ofNat (m + 1) ((y.extractLsb' 0 1).toNat <<< m + (y.extractLsb' 1 m).toNat)

/-- A pass of RCR's loop rotates the `m + 1`-bit value right by one. -/
theorem rcrStep_eq {m : Nat} (y : BitVec (m + 1)) : rcrStep y = y.rotateRight 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold rcrStep
  have hb : (y.extractLsb' 1 m).toNat < 2 ^ m := (y.extractLsb' 1 m).isLt
  rw [BitVec.getLsbD_ofNat, Nat.shiftLeft_add_eq_or_of_lt hb]
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, BitVec.getLsbD_rotateRight,
    BitVec.testBit_toNat, BitVec.getLsbD_extractLsb']
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : i = 0 := by omega
    subst_vars
    simp
  · rw [Nat.mod_eq_of_lt (by omega : 1 < m + 1)]
    by_cases h0 : i = m
    · subst h0
      simp
    · simp [show ¬ i ≥ m by omega, hi, show i < m by omega,
        Nat.add_comm 1 i]

/-- RCL's loop, run `k` times on CF above the operand, rotates it left by `k`. -/
theorem rcl_fold {m : Nat} (y : BitVec (m + 1)) (k : Int) (hk : 0 ≤ k) :
    (Runtime.intRange 1 k).foldl (fun (acc : BitVec (m + 1)) (_ : Int) => rclStep acc) y =
      y.rotateLeft k.toNat := by
  obtain ⟨k, rfl⟩ : ∃ j : Nat, k = j := ⟨k.toNat, by omega⟩
  have := rotateLoop_fold rclStep (fun j => y.rotateLeft j)
    (fun j => by rw [rclStep_eq, ← rotateLeft_succ]) k
  simpa [rotateLeft_zero] using this

/-- RCR's loop, run `k` times on CF above the operand, rotates it right by `k`. -/
theorem rcr_fold {m : Nat} (y : BitVec (m + 1)) (k : Int) (hk : 0 ≤ k) :
    (Runtime.intRange 1 k).foldl (fun (acc : BitVec (m + 1)) (_ : Int) => rcrStep acc) y =
      y.rotateRight k.toNat := by
  obtain ⟨k, rfl⟩ : ∃ j : Nat, k = j := ⟨k.toNat, by omega⟩
  have := rotateLoop_fold rcrStep (fun j => y.rotateRight j)
    (fun j => by rw [rcrStep_eq, ← rotateRight_succ]) k
  simpa [rotateRight_zero] using this

/-- The top bit of `BitVec.cons b x`, as lean-x86 slices it, is `b`. -/
theorem extractLsb'_cons_top {n : Nat} (b : Bool) (x : BitVec n) :
    (BitVec.cons b x).extractLsb' n 1 = BitVec.ofBool b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have : i = 0 := by omega
  subst this
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_cons, BitVec.getLsbD_ofBool]
  simp

/-- Bit 0 of RFLAGS, as lean-x86 reads CF, is the status flags' CF. -/
theorem cf_ofRFLAGS (r : BitVec 64) :
    (BitVec.extractLsb' 0 1 r).getLsbD 0 = (StatusFlags.ofRFLAGS r).CF := by
  simp [StatusFlags.ofRFLAGS]

/-! ### Shifts by any count -/

/-- lean-x86's `Shift_Left_Logical` by `k` (any count): `x <<< k` below the width, zero from the
width up (as the packed shifts PSLLW, PSLLD, PSLLQ use it). -/
theorem shiftLeftLogical_run {size : Int} (x : BitVec size.toNat) (k : Nat) (h : 0 ≤ size) :
    Std.Bits.Shift_Left_Logical (size := size) x (k : Int) =
      .ok (if k < size.toNat then x <<< k else 0) := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, size = n := ⟨size.toNat, by omega⟩
  unfold Std.Bits.Shift_Left_Logical Std.Bits.Shift_Left_Logical_Restricted
  simp only [Int.toNat_natCast] at x ⊢
  by_cases hk : k < n
  · simp [x86_runtime, X86.Runtime.shiftLeftLogical, hk, bind, pure, Except.bind, Except.pure,
      show ¬ (n ≤ k) by omega]
  · simp [x86_runtime, hk, bind, pure, Except.bind, Except.pure]

/-- lean-x86's `Shift_Right_Logical` by `k` (any count): `x >>> k` below the width, zero from the
width up. -/
theorem shiftRightLogical_run {size : Int} (x : BitVec size.toNat) (k : Nat) (h : 0 ≤ size) :
    Std.Bits.Shift_Right_Logical (size := size) x (k : Int) =
      .ok (if k < size.toNat then x >>> k else 0) := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, size = n := ⟨size.toNat, by omega⟩
  unfold Std.Bits.Shift_Right_Logical Std.Bits.Shift_Right_Logical_Restricted
  simp only [Int.toNat_natCast] at x ⊢
  by_cases hk : k < n
  · simp [x86_runtime, X86.Runtime.shiftRightLogical, hk, bind, pure, Except.bind, Except.pure,
      show ¬ (n ≤ k) by omega]
  · simp [x86_runtime, hk, bind, pure, Except.bind, Except.pure]

/-- lean-x86's `Shift_Right_Arithmetic` by `k` (any count): `sshiftRight` by `k`, capped at the
width (from the width up every bit is the sign bit). -/
theorem shiftRightArithmetic_run {size : Int} (x : BitVec size.toNat) (k : Nat) (h : 0 < size) :
    Std.Bits.Shift_Right_Arithmetic (size := size) x (k : Int) =
      .ok (x.sshiftRight (min k size.toNat)) := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, size = n := ⟨size.toNat, by omega⟩
  unfold Std.Bits.Shift_Right_Arithmetic Std.Bits.Shift_Right_Arithmetic_Restricted
  simp only [Int.toNat_natCast] at x ⊢
  by_cases hk : k < n
  · simp [x86_runtime, X86.Runtime.shiftRightArithmetic, hk, bind, pure, Except.bind,
      Except.pure, show ¬ n = 0 by omega, Nat.min_eq_left (Nat.le_of_lt hk)]
    by_cases hk0 : k = 0
    · simp [hk0]
    · simp [hk0, x86_runtime, show k ≤ n by omega]
      rfl
  · simp [x86_runtime, hk, bind, pure, Except.bind, Except.pure, X86.Runtime.CheckedSlice.read,
      Nat.min_eq_right (Nat.le_of_not_lt hk)]
    rw [slice_eq_pure _ (by omega) (by omega) (by omega)]
    simp only [pure, Except.pure]
    have hmsb : x.extractLsb' (n - 1) 1 = BitVec.ofBool x.msb := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      obtain rfl : i = 0 := by omega
      simp [BitVec.msb_eq_getLsbD_last]
    have : ((n : Int) - 1).toNat = n - 1 := by omega
    rw [this]
    erw [hmsb]
    cases hm : x.msb
    · refine congrArg Except.ok (BitVec.eq_of_getLsbD_eq fun i hi => ?_)
      simp [BitVec.getElem_sshiftRight, hi, hm]
      omega
    · refine congrArg Except.ok (BitVec.eq_of_getLsbD_eq fun i hi => ?_)
      simp [BitVec.getElem_sshiftRight, hi, hm]
      omega

end X86Proofs
