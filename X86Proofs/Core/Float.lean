import X86Proofs.Core.Run
import X86Proofs.Core.Lanes
import X86Proofs.Core.Shift
import X86.Instructions.ADDSS
import X86.Instructions.MINSS
import X86.Instructions.SQRTSS
import X86.Helpers.FP.Convert
import X86.Helpers.FP.From_Int
import X86.Helpers.FP.To_Int
import X86.Helpers.FP.Reciprocal
import X86.Helpers.FP.Reciprocal_Sqrt
import X86Proofs.Core.ReadOnly

/-!
# SSE floating point: MXCSR and lean-x86's per-lane float functions

The SSE/SSE2 floating-point forms (ADDSS, MULPD, SQRTSD, …) compute each lane with lean-x86's
float model: `FP.Unpack` to an unpacked `UFloat`, `UFloatAdd`/`UFloatMul`/`UFloatDiv`/`UFloatSqrt`
on exact integers, rounding once by `FP.Rounding_Context`, `FP.Pack`. They read MXCSR (DAZ, FTZ, the
rounding control RC, the overflow and underflow masks) and return, besides the lane, its six
exception flags (`FP_Exception_Flags_Type`: IE, DE, ZE, OE, UE, PE in bits 0–5). The form then
calls `FP.Check_Exceptions`, which ORs the flags into MXCSR (they are sticky) and raises #XM
(`Report_SIMD_FP_Exception`, or #UD if `CR4.OSXMMEXCPT = 0`) for an exception whose mask is clear.

There is no independent IEEE-754 library to state these lanes against, so the library states them
as lean-x86's own functions, evaluated at the MXCSR value the instruction reads:

- `mxRun m mx`: the result of `m` (a lean-x86 computation that reads nothing but MXCSR and changes
  nothing, `ReadsMxcsr m`) at MXCSR = `mx`. `ReadsMxcsr.run_eq`: such an `m` returns `mxRun m
  s.MXCSR` from any state `s` and leaves it unchanged. `reads_mxcsr` proves `ReadsMxcsr` of a
  lean-x86 helper by stepping through its body (binds, `pure`, `liftM` of total helpers, `assert`,
  `readInitialized`, branches, the MXCSR field reads).
- The lanes: `fpArith e op mx x y` (`FP.Arithmetic`: ADD, SUB, MUL, DIV), `fpMinMax e isMax mx x
  y` (`FP.Min_Max`), `fpSqrt e mx x` (`FP.Sqrt`), `fpCompare e signalling mx x y` (`FP.Compare`,
  COMISS/UCOMISS: ZF, PF, CF), `fpCompare5 e pred mx x y` (`FP.Compare5`, CMPPS/CMPSS),
  `fpConvert e r rm ftz mx x` (`FP.Convert`, between single and double precision) and `fpFromInt
  e r mx x` (`FP.From_Int`, a signed integer to a float), each the pair (result, exception flags),
  with DAZ, RC, FTZ and the underflow mask taken from `mx` as the forms take them (`mxDaz`, `mxRc`,
  `mxFtz`, `mxUm`). lean-x86's helpers are written in a monad with runtime errors (an assertion or
  a read of an uninitialized local could fail); the library does not prove that they never do, so
  each lane comes with a definedness predicate (`FpArithOk`, `FpMinMaxOk`, `FpSqrtOk`,
  `FpCompareOk`, `FpCompare5Ok`, `FpConvertOk`, `FpFromIntOk`: lean-x86 returns a value, `LaneOk`)
  that the triples take as a precondition, and the lane function is that value (`laneVal`).
  `fpArith_run`, `fpMinMax_run`, …, `fpFromInt_run`: the helper, run from a state whose MXCSR is
  `mx`, returns the lane and leaves the state alone.
- Packed forms: lean-x86's lane loop is a fold (`specM_forIn_lanes`); `fpPacked w f`,
  `fpPackedFlags w f` are its result (lane `i` is `(f i).1`, `fpPacked_eq`) and its flags (every
  lane's ORed, `fpPackedFlags_eq`), `fpLanes k w f`, `fpLanesFlags k w f` the same for the first
  `k` lanes only, the rest zero (CVTPD2PS), and `fpLanesOnto k w f init` the first `k` lanes and
  their flags into `init`, of any width (the conversions to and from MMX registers).
  `fpOperandPrio` is `FP.Prioritize_Operand_Exceptions` with every exception masked (MIN/MAX,
  CMP, CVTPS2PD). The tactics `fp_packed_loop`,
  `fp_packed_loop_split` and `fp_cvt_loop` step through a loop, `fp_scalar_arith`,
  `fp_scalar_minmax`, `fp_scalar_sqrt` and `fp_packed_start…` through the MXCSR reads before it.
- Conversions to integers (CVTSS2SI, CVTTPD2DQ, …): `fpToInt e r rm mx x` (`FP.To_Int`, the
  float `x` to a signed `r`-bit integer, rounding mode `rm`, DAZ from `mx`; lean-x86's integer
  indefinite value for a NaN or an out-of-range value), with `FpToIntOk` and `fpToInt_run`. Unlike
  the other lanes it is a `PartialResult` (it may diverge: `FP87.Convert_From_Float` normalizes a
  denormal with a loop), so `FpToIntOk` says that it terminates with a value, the forms and their
  operations are `PartialSpecM`, and `partialSpecM_forIn_lanes`, `fp_cvt_loop_partial` are the
  packed loop's lemma and tactic in `PartialSpecM`.
- Reciprocal approximations (RCPSS, RSQRTPS, …): `fpRcp x`, `fpRsqrt x` (`FP.Reciprocal`,
  `FP.Reciprocal_Sqrt` on a single-precision `x`), which read no MXCSR, return no flags and send a
  normal `x` to the machine's numerical binding (`Emulate_RCPSS`, `Emulate_RSQRTSS`), which may
  read the whole state. `FpRcpOk x`, `FpRsqrtOk x`: lean-x86 returns a value on `x`, the same from
  every state. `fpRcp_reads`, `fpRsqrt_reads`: the helpers leave the state alone (`ReadOnly` for no
  relation, by `keeps_state`); `fpRcp_run`, `fpRsqrt_run`.
- `MxcsrPre s`: the six exception masks (MXCSR bits 7–12) are set. Then `FP.Check_Exceptions`
  raises nothing and only ORs the flags into MXCSR (`checkExceptions_run`: MXCSR becomes `mxOr mx
  flags`); `MxcsrPre.mxOr` keeps the masks set.
- The other MXCSR reads the forms make: `getDAZ_run`, `getFTZ_run` (`FP.Get_DAZ`, `FP.Get_FTZ`
  at 32 and 64 bits), `mxcsrUM_run`, `mxcsrMasks_run`, `mxcsrRC_run`, `mxcsrFlags_run`,
  `mxcsrSetFlags_run`; `decodeRoundingMode_eq` (`FP.Decode_Rounding_Mode rc = .ok (rcMode rc)`).
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers X86.Runtime
open scoped X86.Runtime.Syntax

/-! ### MXCSR fields -/

/-- DAZ (MXCSR bit 6): denormal source operands are read as zero. -/
abbrev mxDaz (mx : BitVec 32) : Bool := mx.extractLsb' 6 1 == 1

/-- FTZ (MXCSR bit 15): denormal results are flushed to zero. -/
abbrev mxFtz (mx : BitVec 32) : Bool := mx.extractLsb' 15 1 == 1

/-- UM (MXCSR bit 11): the underflow exception is masked. -/
abbrev mxUm (mx : BitVec 32) : Bool := mx.extractLsb' 11 1 == 1

/-- RC (MXCSR bits 13–14): the rounding control. -/
abbrev mxRc (mx : BitVec 32) : BitVec 2 := mx.extractLsb' 13 2

/-- The rounding mode of rounding control `rc`: 0 to nearest (even), 1 down, 2 up, 3 toward
zero. -/
def rcMode (rc : BitVec 2) : Rounding_Mode :=
  if rc = 0 then .Rounding_Mode_RNE else if rc = 1 then .Rounding_Mode_RTN
  else if rc = 2 then .Rounding_Mode_RTP else .Rounding_Mode_RTZ

/-- MXCSR with the exception flags `f` ORed into bits 0–5, as `FP.Check_Exceptions` leaves it. -/
def mxOr (mx : BitVec 32) (f : BitVec 6) : BitVec 32 := mx ||| f.setWidth 32

/-- All six SIMD floating-point exceptions are masked (MXCSR bits 7–12 set): a floating-point SSE
form raises no #XM (nor #UD for `CR4.OSXMMEXCPT = 0`) and only records the exception flags. -/
def MxcsrPre (s : RamState) : Prop := s.MXCSR.extractLsb' 7 6 = 0x3F

/-- ORing in exception flags keeps the masks. -/
theorem MxcsrPre.mxOr {s t : RamState} (h : MxcsrPre s) (f : BitVec 6)
    (ht : t.MXCSR = X86Proofs.mxOr s.MXCSR f) : MxcsrPre t := by
  unfold MxcsrPre at *
  rw [ht, ← h]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [X86Proofs.mxOr, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or]
  simp [BitVec.getLsbD_of_ge f (7 + i) (by omega)]

/-! ### The MXCSR reads and writes of the forms -/

theorem getDAZ_run [Bindings] (size : Int) (h : (size == 16) = false) (s : RamState) :
    (FP.Get_DAZ size : SpecM X86.Exception RamState Bool).run s = (.ok (mxDaz s.MXCSR), s) := by
  unfold FP.Get_DAZ
  simp only [h, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem getFTZ_run [Bindings] (size : Int) (h : (size == 16) = false) (s : RamState) :
    (FP.Get_FTZ size : SpecM X86.Exception RamState Bool).run s = (.ok (mxFtz s.MXCSR), s) := by
  unfold FP.Get_FTZ
  simp only [h, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem mxcsrUM_run (s : RamState) :
    (X86.MXCSR.UM : SpecM X86.Exception RamState _).run s =
      (.ok (s.MXCSR.extractLsb' 11 1), s) := rfl

theorem mxcsrRC_run (s : RamState) :
    (X86.MXCSR.RC : SpecM X86.Exception RamState _).run s = (.ok (mxRc s.MXCSR), s) := rfl

theorem mxcsrMasks_run (s : RamState) :
    (X86.MXCSR.Exception_Masks : SpecM X86.Exception RamState _).run s =
      (.ok (s.MXCSR.extractLsb' 7 6), s) := rfl

theorem mxcsrFlags_run (s : RamState) :
    (X86.MXCSR.Exception_Flags : SpecM X86.Exception RamState _).run s =
      (.ok (s.MXCSR.extractLsb' 0 6), s) := rfl

theorem mxcsrSetFlags_run (s : RamState) (v : BitVec 6) :
    (X86.MXCSR.setException_Flags v : SpecM X86.Exception RamState _).run s =
      (.ok (), { s with MXCSR := setSlice s.MXCSR 0 6 v }) := rfl

theorem decodeRoundingMode_eq (rc : BitVec 2) : FP.Decode_Rounding_Mode rc = .ok (rcMode rc) := by
  obtain ⟨i, rfl⟩ : ∃ i : Fin 4, rc = BitVec.ofNat 2 i.val := ⟨⟨rc.toNat, rc.isLt⟩, by simp⟩
  finite_cases i <;> rfl

/-- `false and b` (lean-x86's `and`, `HAnd` on `Bool`). -/
theorem and_false_left (b : Bool) : (false &&& b) = false := rfl

/-- The flags, ORed into bits 0–5 by `setSlice`, are `mxOr`. -/
theorem setSlice_flags_or (mx : BitVec 32) (f : BitVec 6) :
    setSlice mx 0 6 (mx.extractLsb' 0 6 ||| f) = mxOr mx f := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [getLsbD_setSlice _ _ _ _ _ hk]
  unfold mxOr
  by_cases h : k < 6
  · simp [h, hk]
  · simp [h, show 6 ≤ k by omega]

theorem prioritizeExceptions_masked (f : BitVec 6) : FP.Prioritize_Exceptions f 63 = .ok f := by
  unfold FP.Prioritize_Exceptions
  have h : ~~~(BitVec.extractLsb' 0 3 (63 : BitVec 6)) = 0 := by decide
  have h0 : (BitVec.extractLsb' 0 3 f &&& ~~~BitVec.extractLsb' 0 3 (63 : BitVec 6)) = 0 := by
    rw [h]
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp
  simp (config := { decide := true }) only [x86_runtime, stdIsZero_eq_ok,
    bind_pure_comp, map_pure, pure_bind, h0]
  rfl

theorem isZero_masked (f : BitVec 6) :
    Std.Bits.Is_Zero (size := 6) (f &&& ~~~(63 : BitVec 6)) = .ok true := by
  have h0 : (f &&& ~~~(63 : BitVec 6)) = 0 := by
    rw [show ~~~(63 : BitVec 6) = 0 by decide]
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp
  rw [stdIsZero_eq_ok _ (by decide), h0]
  rfl

/-- With every exception masked, `FP.Check_Exceptions f` ORs the flags `f` into MXCSR and
raises nothing. -/
theorem checkExceptions_run (s : RamState) (f : BitVec 6) (hm : MxcsrPre s) :
    (FP.Check_Exceptions f (s.MXCSR.extractLsb' 7 6) : SpecM X86.Exception RamState Unit).run s =
      (.ok (), { s with MXCSR := mxOr s.MXCSR f }) := by
  unfold MxcsrPre at hm
  unfold FP.Check_Exceptions
  rw [hm]
  refine (specM_bind_run _ _ (mxcsrFlags_run s)).trans ?_
  refine (specM_bind_run _ _ (liftM_run_of_ok (prioritizeExceptions_masked f) s)).trans ?_
  refine (specM_bind_run _ _ (mxcsrSetFlags_run s _)).trans ?_
  refine (specM_bind_run _ _ (liftM_run_of_ok (isZero_masked f) _)).trans ?_
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  show (Except.ok (), { s with MXCSR := setSlice s.MXCSR 0 6 (s.MXCSR.extractLsb' 0 6 ||| f) }) = _
  rw [setSlice_flags_or]

/-- The result of a scalar float operation (ADDSS, SQRTSD, …) on destination `a`: the low `e` bits
replaced by the lane `r`, bits `e` to 127 of `a` kept. -/
def fpScalar (e : Nat) (a : BitVec 128) (r : BitVec e) : BitVec 128 := setSlice a 0 e r

/-- The whole of `x` as a slice. -/
theorem extractLsb'_zero_self {n : Nat} (x : BitVec n) : x.extractLsb' 0 n = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

/-- How lean-x86's scalar operations assemble their result: `r` in the low `e` bits of zero, then
bits `e` to 127 of `a`. -/
theorem setSlice_scalar (e : Nat) (he : e < 128) (a : BitVec 128) (r : BitVec e) :
    setSlice (setSlice 0 0 e r) e (128 - e) (a.extractLsb' e (128 - e)) = fpScalar e a r := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  unfold fpScalar
  rw [getLsbD_setSlice _ _ _ _ _ hk, getLsbD_setSlice _ _ _ _ _ hk, getLsbD_setSlice _ _ _ _ _ hk]
  by_cases h : k < e
  · simp [h, show ¬ e ≤ k by omega]
  · simp [h, show e ≤ k by omega, show k < e + (128 - e) by omega, show e + (k - e) = k by omega]
    omega

/-! ### Computations that read only MXCSR -/

/-- A state whose MXCSR is `mx` (the rest is lean-x86's default state; a computation that reads
only MXCSR does not look at it). -/
def mxState (mx : BitVec 32) : RamState := { (default : RamState) with MXCSR := mx }

/-- The result of `m` at MXCSR = `mx`. -/
def mxRun {α : Type} (m : SpecM X86.Exception RamState α) (mx : BitVec 32) :
    Except (Error X86.Exception) α :=
  (m.run (mxState mx)).1

/-- `m` reads nothing but MXCSR and changes nothing: from any state it returns its result at that
state's MXCSR and leaves the state as it was. -/
structure ReadsMxcsr {α : Type} (m : SpecM X86.Exception RamState α) : Prop where
  run_eq : ∀ s : RamState, m.run s = (mxRun m s.MXCSR, s)

theorem specM_run_bind {ε σ α β : Type} (m : SpecM ε σ α) (k : α → SpecM ε σ β) (s : σ) :
    (m >>= k).run s = match m.run s with
      | (.ok a, t) => (k a).run t
      | (.error e, t) => (.error e, t) := by
  simp only [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind, ExceptT.bindCont]
  rcases m s with ⟨r, t⟩
  cases r <;> rfl

namespace ReadsMxcsr

theorem pure' {α : Type} (a : α) : ReadsMxcsr (pure a : SpecM X86.Exception RamState α) :=
  ⟨fun _ => rfl⟩

theorem bind' {α β : Type} {m : SpecM X86.Exception RamState α}
    {k : α → SpecM X86.Exception RamState β} (hm : ReadsMxcsr m) (hk : ∀ a, ReadsMxcsr (k a)) :
    ReadsMxcsr (m >>= k) := by
  refine ⟨fun s => ?_⟩
  have h2 := hm.run_eq (mxState s.MXCSR)
  have hmx : (mxState s.MXCSR).MXCSR = s.MXCSR := rfl
  rw [hmx] at h2
  unfold mxRun
  rw [specM_run_bind, specM_run_bind, hm.run_eq s, h2]
  cases mxRun m s.MXCSR with
  | error e => rfl
  | ok a =>
    simp only
    rw [(hk a).run_eq s, (hk a).run_eq (mxState s.MXCSR), hmx]

theorem lift {α : Type} (e : Except (Error Empty) α) :
    ReadsMxcsr (liftM e : SpecM X86.Exception RamState α) := by
  refine ⟨fun s => ?_⟩
  cases e <;> rfl

theorem ite' {α : Type} {c : Prop} [Decidable c] {a b : SpecM X86.Exception RamState α}
    (ha : c → ReadsMxcsr a) (hb : ¬ c → ReadsMxcsr b) : ReadsMxcsr (if c then a else b) := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

theorem dite' {α : Type} {c : Prop} [Decidable c] {a : c → SpecM X86.Exception RamState α}
    {b : ¬ c → SpecM X86.Exception RamState α}
    (ha : ∀ h, ReadsMxcsr (a h)) (hb : ∀ h, ReadsMxcsr (b h)) : ReadsMxcsr (dite c a b) := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

theorem throw' {α : Type} (e : Error X86.Exception) :
    ReadsMxcsr (throw e : SpecM X86.Exception RamState α) := ⟨fun _ => rfl⟩

theorem assert' (c : Bool) : ReadsMxcsr (assert c : SpecM X86.Exception RamState Unit) := by
  refine ⟨fun s => ?_⟩
  cases c <;> rfl

theorem readInitialized' {α : Type} (o : Option α) :
    ReadsMxcsr (readInitialized o : SpecM X86.Exception RamState α) := by
  refine ⟨fun s => ?_⟩
  cases o <;> rfl

theorem om : ReadsMxcsr (X86.MXCSR.OM : SpecM X86.Exception RamState _) := ⟨fun _ => rfl⟩
theorem um : ReadsMxcsr (X86.MXCSR.UM : SpecM X86.Exception RamState _) := ⟨fun _ => rfl⟩
theorem rc : ReadsMxcsr (X86.MXCSR.RC : SpecM X86.Exception RamState _) := ⟨fun _ => rfl⟩
theorem daz : ReadsMxcsr (X86.MXCSR.DAZ : SpecM X86.Exception RamState _) := ⟨fun _ => rfl⟩
theorem ftz : ReadsMxcsr (X86.MXCSR.FTZ : SpecM X86.Exception RamState _) := ⟨fun _ => rfl⟩

end ReadsMxcsr

open Lean Meta Elab Tactic in
/-- One step of `reads_mxcsr`: introduce a bound value, or apply the `ReadsMxcsr` rule for the head
of the computation (bind, `pure`, `liftM`, `assert`, `readInitialized`, `if`, `throw`, an MXCSR
field read), split a `match`, or unfold the head definition. -/
elab "reads_mxcsr_step" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  if tgt.isForall then
    evalTactic (← `(tactic| intro _))
    return
  unless tgt.isAppOf ``ReadsMxcsr do throwError "reads_mxcsr: not a ReadsMxcsr goal"
  let some m := tgt.getAppArgs.back? | throwError "reads_mxcsr: unexpected goal"
  let m := m.consumeMData
  if m.isLet || m.isAppOf ``letFun then
    evalTactic (← `(tactic| dsimp only))
    return
  let head := m.getAppFn.constName?.getD .anonymous
  let run (t : TSyntax `tactic) : TacticM Unit := evalTactic t
  if head == ``Bind.bind then run (← `(tactic| refine ReadsMxcsr.bind' ?_ ?_))
  else if head == ``Pure.pure then run (← `(tactic| exact ReadsMxcsr.pure' _))
  else if head == ``liftM then run (← `(tactic| exact ReadsMxcsr.lift _))
  else if head == ``X86.Runtime.assert then run (← `(tactic| exact ReadsMxcsr.assert' _))
  else if head == ``X86.Runtime.readInitialized then
    run (← `(tactic| exact ReadsMxcsr.readInitialized' _))
  else if head == ``ite then run (← `(tactic| refine ReadsMxcsr.ite' ?_ ?_))
  else if head == ``dite then run (← `(tactic| refine ReadsMxcsr.dite' ?_ ?_))
  else if head == ``MonadExcept.throw || head == ``throw || head == ``throwThe then
    run (← `(tactic| exact ReadsMxcsr.throw' _))
  else if head == ``X86.MXCSR.OM then run (← `(tactic| exact ReadsMxcsr.om))
  else if head == ``X86.MXCSR.UM then run (← `(tactic| exact ReadsMxcsr.um))
  else if head == ``X86.MXCSR.RC then run (← `(tactic| exact ReadsMxcsr.rc))
  else if head == ``X86.MXCSR.DAZ then run (← `(tactic| exact ReadsMxcsr.daz))
  else if head == ``X86.MXCSR.FTZ then run (← `(tactic| exact ReadsMxcsr.ftz))
  else if (← isMatcherApp m) then run (← `(tactic| split))
  else if head != .anonymous then run (← `(tactic| unfold $(mkIdent head):ident))
  else throwError "reads_mxcsr: cannot step {m}"

/-- Prove `ReadsMxcsr m` for a lean-x86 computation `m` built from binds, `pure`, `liftM` of total
helpers, `assert`, `readInitialized`, branches, `throw` and MXCSR field reads (unfolding the
helpers it calls). -/
macro "reads_mxcsr" : tactic => `(tactic| repeat' reads_mxcsr_step)

/-! ### The lanes -/

/-- lean-x86's `FP.Arithmetic op x y` (`op`: ADD, SUB, MUL, DIV) on `e`-bit floats at MXCSR `mx`:
DAZ, the rounding mode, FTZ and the underflow mask from `mx`. -/
def fpArithRun (e : Nat) (op : «FP::Arithmetic_Op_Type») (mx : BitVec 32) (x y : BitVec e) :
    Except (Error X86.Exception) (BitVec e × BitVec 6) :=
  mxRun (FP.Arithmetic (N := e) op x y (mxDaz mx) (rcMode (mxRc mx)) (mxFtz mx) (mxUm mx)) mx

/-- lean-x86's `FP.Min_Max isMax x y` at MXCSR `mx` (DAZ from `mx`). -/
def fpMinMaxRun (e : Nat) (isMax : Bool) (mx : BitVec 32) (x y : BitVec e) :
    Except (Error X86.Exception) (BitVec e × BitVec 6) :=
  mxRun (FP.Min_Max (N := e) isMax x y (mxDaz mx)) mx

/-- lean-x86's `FP.Sqrt x` at MXCSR `mx` (DAZ, the rounding mode and FTZ from `mx`). -/
def fpSqrtRun (e : Nat) (mx : BitVec 32) (x : BitVec e) :
    Except (Error X86.Exception) (BitVec e × BitVec 6) :=
  mxRun (FP.Sqrt (N := e) x (mxDaz mx) (rcMode (mxRc mx)) (mxFtz mx)) mx

/-- The value of a lane computation, or `default` if lean-x86 returned none (excluded by the
`…Ok` preconditions). -/
def laneVal {α : Type} [Inhabited α] : Except (Error X86.Exception) α → α
  | .ok v => v
  | .error _ => default

/-- lean-x86 returns a value. -/
def LaneOk {α : Type} (r : Except (Error X86.Exception) α) : Prop := ∃ v, r = .ok v

theorem LaneOk.eq {α : Type} [Inhabited α] {r : Except (Error X86.Exception) α}
    (h : LaneOk r) : r = .ok (laneVal r) := by
  obtain ⟨v, rfl⟩ := h
  rfl

/-- `x op y` (ADD, SUB, MUL, DIV) and its exception flags, as lean-x86 computes them at MXCSR
`mx`. -/
def fpArith (e : Nat) (op : «FP::Arithmetic_Op_Type») (mx : BitVec 32) (x y : BitVec e) :
    BitVec e × BitVec 6 :=
  laneVal (fpArithRun e op mx x y)

/-- lean-x86's `FP.Arithmetic` returns a value on `x`, `y` at MXCSR `mx`. -/
def FpArithOk (e : Nat) (op : «FP::Arithmetic_Op_Type») (mx : BitVec 32) (x y : BitVec e) :
    Prop :=
  LaneOk (fpArithRun e op mx x y)

/-- The minimum (`isMax = false`) or maximum of `x` and `y` and the exception flags, as lean-x86
computes them at MXCSR `mx`. -/
def fpMinMax (e : Nat) (isMax : Bool) (mx : BitVec 32) (x y : BitVec e) : BitVec e × BitVec 6 :=
  laneVal (fpMinMaxRun e isMax mx x y)

/-- lean-x86's `FP.Min_Max` returns a value on `x`, `y` at MXCSR `mx`. -/
def FpMinMaxOk (e : Nat) (isMax : Bool) (mx : BitVec 32) (x y : BitVec e) : Prop :=
  LaneOk (fpMinMaxRun e isMax mx x y)

/-- The square root of `x` and the exception flags, as lean-x86 computes them at MXCSR `mx`. -/
def fpSqrt (e : Nat) (mx : BitVec 32) (x : BitVec e) : BitVec e × BitVec 6 :=
  laneVal (fpSqrtRun e mx x)

/-- lean-x86's `FP.Sqrt` returns a value on `x` at MXCSR `mx`. -/
def FpSqrtOk (e : Nat) (mx : BitVec 32) (x : BitVec e) : Prop := LaneOk (fpSqrtRun e mx x)

/-- lean-x86's `FP.Compare5 x y pred` (CMPPS, CMPSS: the comparison predicate `pred`, 0–31) at
MXCSR `mx` (DAZ from `mx`): whether the predicate holds, and the exception flags. -/
def fpCompare5Run (e : Nat) (pred : BitVec 5) (mx : BitVec 32) (x y : BitVec e) :
    Except (Error X86.Exception) (Bool × BitVec 6) :=
  mxRun (FP.Compare5 (N := e) x y pred (mxDaz mx)) mx

/-- Whether comparison predicate `pred` holds of `x` and `y`, and the exception flags, as lean-x86
computes them at MXCSR `mx` (the legacy CMPPS/CMPSS predicates are 0–7: EQ, LT, LE, UNORD, NEQ,
NLT, NLE, ORD). -/
def fpCompare5 (e : Nat) (pred : BitVec 5) (mx : BitVec 32) (x y : BitVec e) : Bool × BitVec 6 :=
  laneVal (fpCompare5Run e pred mx x y)

/-- lean-x86's `FP.Compare5` returns a value on `x`, `y` at MXCSR `mx`. -/
def FpCompare5Ok (e : Nat) (pred : BitVec 5) (mx : BitVec 32) (x y : BitVec e) : Prop :=
  LaneOk (fpCompare5Run e pred mx x y)

/-- lean-x86's `FP.Compare x y signalling` at MXCSR `mx` (DAZ from `mx`): the comparison as ZF, PF,
CF bits (bits 2, 1, 0: unordered 111, greater 000, less 001, equal 100) and the exception
flags. -/
def fpCompareRun (e : Nat) (signalling : Bool) (mx : BitVec 32) (x y : BitVec e) :
    Except (Error X86.Exception) (BitVec 3 × BitVec 6) :=
  mxRun (FP.Compare (N := e) x y signalling (mxDaz mx)) mx

/-- The comparison of `x` and `y` (ZF, PF, CF as bits 2, 1, 0) and its exception flags, as
lean-x86 computes them at MXCSR `mx` (`signalling`: a QNaN operand raises the invalid exception,
COMISS; otherwise only an SNaN does, UCOMISS). -/
def fpCompare (e : Nat) (signalling : Bool) (mx : BitVec 32) (x y : BitVec e) :
    BitVec 3 × BitVec 6 :=
  laneVal (fpCompareRun e signalling mx x y)

/-- lean-x86's `FP.Compare` returns a value on `x`, `y` at MXCSR `mx`. -/
def FpCompareOk (e : Nat) (signalling : Bool) (mx : BitVec 32) (x y : BitVec e) : Prop :=
  LaneOk (fpCompareRun e signalling mx x y)

theorem fpArith_reads (N : Int) (hN : N = 32 ∨ N = 64) (op : «FP::Arithmetic_Op_Type»)
    (x y : Bits N) (daz : Bool) (rm : Rounding_Mode) (ftz mu : Bool) :
    ReadsMxcsr (FP.Arithmetic (N := N) op x y daz rm ftz mu : SpecM X86.Exception RamState _) := by
  rcases hN with rfl | rfl <;>
  · unfold FP.Arithmetic
    reads_mxcsr

theorem fpMinMax_reads (N : Int) (hN : N = 32 ∨ N = 64) (isMax : Bool) (x y : Bits N)
    (daz : Bool) :
    ReadsMxcsr (FP.Min_Max (N := N) isMax x y daz : SpecM X86.Exception RamState _) := by
  rcases hN with rfl | rfl <;>
  · unfold FP.Min_Max
    reads_mxcsr

theorem fpSqrt_reads (N : Int) (hN : N = 32 ∨ N = 64) (x : Bits N) (daz : Bool)
    (rm : Rounding_Mode) (ftz : Bool) :
    ReadsMxcsr (FP.Sqrt (N := N) x daz rm ftz : SpecM X86.Exception RamState _) := by
  rcases hN with rfl | rfl <;>
  · unfold FP.Sqrt
    reads_mxcsr

theorem fpCompare_reads (N : Int) (hN : N = 32 ∨ N = 64) (x y : Bits N) (signalling daz : Bool) :
    ReadsMxcsr (FP.Compare (N := N) x y signalling daz : SpecM X86.Exception RamState _) := by
  rcases hN with rfl | rfl <;>
  · unfold FP.Compare
    reads_mxcsr

theorem fpCompare5_reads (N : Int) (hN : N = 32 ∨ N = 64) (x y : Bits N) (pred : BitVec 5)
    (daz : Bool) :
    ReadsMxcsr (FP.Compare5 (N := N) x y pred daz : SpecM X86.Exception RamState _) := by
  rcases hN with rfl | rfl <;>
  · unfold FP.Compare5
    reads_mxcsr

theorem natCast_32_or_64 {e : Nat} (he : e = 32 ∨ e = 64) : (e : Int) = 32 ∨ (e : Int) = 64 := by
  rcases he with rfl | rfl <;> decide

/-- `FP.Arithmetic`, run with MXCSR `mx`'s settings from a state whose MXCSR is `mx`, returns
`fpArith` and leaves the state alone. -/
theorem fpArith_run (e : Nat) (he : e = 32 ∨ e = 64) (op : «FP::Arithmetic_Op_Type»)
    (x y : BitVec e) (s : RamState) (hok : FpArithOk e op s.MXCSR x y) :
    (FP.Arithmetic (N := e) op x y (mxDaz s.MXCSR) (rcMode (mxRc s.MXCSR)) (mxFtz s.MXCSR)
      (mxUm s.MXCSR) : SpecM X86.Exception RamState _).run s =
      (.ok (fpArith e op s.MXCSR x y), s) := by
  rw [(fpArith_reads e (natCast_32_or_64 he) _ _ _ _ _ _ _).run_eq s]
  exact congrArg (fun r => (r, s)) hok.eq

theorem fpMinMax_run (e : Nat) (he : e = 32 ∨ e = 64) (isMax : Bool) (x y : BitVec e)
    (s : RamState) (hok : FpMinMaxOk e isMax s.MXCSR x y) :
    (FP.Min_Max (N := e) isMax x y (mxDaz s.MXCSR) : SpecM X86.Exception RamState _).run s =
      (.ok (fpMinMax e isMax s.MXCSR x y), s) := by
  rw [(fpMinMax_reads e (natCast_32_or_64 he) _ _ _ _).run_eq s]
  exact congrArg (fun r => (r, s)) hok.eq

theorem fpSqrt_run (e : Nat) (he : e = 32 ∨ e = 64) (x : BitVec e) (s : RamState)
    (hok : FpSqrtOk e s.MXCSR x) :
    (FP.Sqrt (N := e) x (mxDaz s.MXCSR) (rcMode (mxRc s.MXCSR)) (mxFtz s.MXCSR) :
      SpecM X86.Exception RamState _).run s = (.ok (fpSqrt e s.MXCSR x), s) := by
  rw [(fpSqrt_reads e (natCast_32_or_64 he) _ _ _ _).run_eq s]
  exact congrArg (fun r => (r, s)) hok.eq

theorem fpCompare_run (e : Nat) (he : e = 32 ∨ e = 64) (signalling : Bool) (x y : BitVec e)
    (s : RamState) (hok : FpCompareOk e signalling s.MXCSR x y) :
    (FP.Compare (N := e) x y signalling (mxDaz s.MXCSR) : SpecM X86.Exception RamState _).run s =
      (.ok (fpCompare e signalling s.MXCSR x y), s) := by
  rw [(fpCompare_reads e (natCast_32_or_64 he) _ _ _ _).run_eq s]
  exact congrArg (fun r => (r, s)) hok.eq

theorem fpCompare5_run (e : Nat) (he : e = 32 ∨ e = 64) (pred : BitVec 5) (x y : BitVec e)
    (s : RamState) (hok : FpCompare5Ok e pred s.MXCSR x y) :
    (FP.Compare5 (N := e) x y pred (mxDaz s.MXCSR) : SpecM X86.Exception RamState _).run s =
      (.ok (fpCompare5 e pred s.MXCSR x y), s) := by
  rw [(fpCompare5_reads e (natCast_32_or_64 he) _ _ _ _).run_eq s]
  exact congrArg (fun r => (r, s)) hok.eq

/-- lean-x86's `FP.Convert x r` (an `e`-bit float to an `r`-bit one) at MXCSR `mx`, with DAZ from
`mx`, rounding mode `rm` and flush-to-zero `ftz` as the form passes them (CVTSS2SD: RNE and
`true`; CVTSD2SS: MXCSR.RC and FTZ). -/
def fpConvertRun (e r : Nat) (rm : Rounding_Mode) (ftz : Bool) (mx : BitVec 32) (x : BitVec e) :
    Except (Error X86.Exception) (BitVec r × BitVec 6) :=
  mxRun (FP.Convert (N := e) x r (mxDaz mx) rm ftz) mx

/-- `x` converted to an `r`-bit float and the exception flags, as lean-x86 computes them at MXCSR
`mx` (rounding mode `rm`, flush-to-zero `ftz`). -/
def fpConvert (e r : Nat) (rm : Rounding_Mode) (ftz : Bool) (mx : BitVec 32) (x : BitVec e) :
    BitVec r × BitVec 6 :=
  laneVal (fpConvertRun e r rm ftz mx x)

/-- lean-x86's `FP.Convert` returns a value on `x` at MXCSR `mx`. -/
def FpConvertOk (e r : Nat) (rm : Rounding_Mode) (ftz : Bool) (mx : BitVec 32) (x : BitVec e) :
    Prop :=
  LaneOk (fpConvertRun e r rm ftz mx x)

/-- lean-x86's `FP.From_Int x true r` (the signed `e`-bit integer `x` to an `r`-bit float) at
MXCSR `mx`, rounded as MXCSR.RC says. -/
def fpFromIntRun (e r : Nat) (mx : BitVec 32) (x : BitVec e) :
    Except (Error X86.Exception) (BitVec r × BitVec 6) :=
  mxRun (FP.From_Int (source_size := e) x true r (rcMode (mxRc mx))) mx

/-- The signed integer `x` as an `r`-bit float and the exception flags, as lean-x86 computes them
at MXCSR `mx`. -/
def fpFromInt (e r : Nat) (mx : BitVec 32) (x : BitVec e) : BitVec r × BitVec 6 :=
  laneVal (fpFromIntRun e r mx x)

/-- lean-x86's `FP.From_Int` returns a value on `x` at MXCSR `mx`. -/
def FpFromIntOk (e r : Nat) (mx : BitVec 32) (x : BitVec e) : Prop :=
  LaneOk (fpFromIntRun e r mx x)

theorem fpConvert_reads (N M : Int) (h : N = 32 ∧ M = 64 ∨ N = 64 ∧ M = 32) (x : Bits N)
    (daz : Bool) (rm : Rounding_Mode) (ftz : Bool) :
    ReadsMxcsr (FP.Convert (N := N) x M daz rm ftz : SpecM X86.Exception RamState _) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · unfold FP.Convert
    reads_mxcsr

theorem fpFromInt_reads (N M : Int) (hN : N = 32 ∨ N = 64) (hM : M = 32 ∨ M = 64) (x : Bits N)
    (rm : Rounding_Mode) :
    ReadsMxcsr (FP.From_Int (source_size := N) x true M rm : SpecM X86.Exception RamState _) := by
  rcases hN with rfl | rfl <;> rcases hM with rfl | rfl <;>
  · unfold FP.From_Int
    reads_mxcsr

/-- `FP.Convert`, run with DAZ from MXCSR `mx` from a state whose MXCSR is `mx`, returns
`fpConvert` and leaves the state alone. -/
theorem fpConvert_run (e r : Nat) (h : e = 32 ∧ r = 64 ∨ e = 64 ∧ r = 32) (rm : Rounding_Mode)
    (ftz : Bool) (x : BitVec e) (s : RamState) (hok : FpConvertOk e r rm ftz s.MXCSR x) :
    (FP.Convert (N := e) x r (mxDaz s.MXCSR) rm ftz : SpecM X86.Exception RamState _).run s =
      (.ok (fpConvert e r rm ftz s.MXCSR x), s) := by
  have h' : (e : Int) = 32 ∧ (r : Int) = 64 ∨ (e : Int) = 64 ∧ (r : Int) = 32 := by omega
  rw [(fpConvert_reads e r h' _ _ _ _).run_eq s]
  exact congrArg (fun r => (r, s)) hok.eq

/-- `FP.From_Int`, run with MXCSR `mx`'s rounding mode from a state whose MXCSR is `mx`, returns
`fpFromInt` and leaves the state alone. -/
theorem fpFromInt_run (e r : Nat) (he : e = 32 ∨ e = 64) (hr : r = 32 ∨ r = 64) (x : BitVec e)
    (s : RamState) (hok : FpFromIntOk e r s.MXCSR x) :
    (FP.From_Int (source_size := e) x true r (rcMode (mxRc s.MXCSR)) :
      SpecM X86.Exception RamState _).run s = (.ok (fpFromInt e r s.MXCSR x), s) := by
  rw [(fpFromInt_reads e r (natCast_32_or_64 he) (natCast_32_or_64 hr) _ _).run_eq s]
  exact congrArg (fun r => (r, s)) hok.eq

/-- The status flags of a COMISS-style comparison `z` (ZF, PF, CF as bits 2, 1, 0): those three
set from `z`, OF, SF and AF clear. -/
def fpCompareFlags (z : BitVec 3) : StatusFlags :=
  { CF := z.getLsbD 0, PF := z.getLsbD 1, AF := false, ZF := z.getLsbD 2, SF := false,
    OF := false }

/-- lean-x86's flag writes at the end of COMISf/UCOMISf store `fpCompareFlags z`. -/
theorem compareRflags_run {σ : Type} (s : X86.State σ) (z : BitVec 3) :
    (do
      RFLAGS.setSF 0
      RFLAGS.setZF (z.extractLsb' 2 1)
      RFLAGS.setPF (z.extractLsb' 1 1)
      RFLAGS.setOF 0
      RFLAGS.setAF 0
      RFLAGS.setCF (z.extractLsb' 0 1) : SpecM X86.Exception (X86.State σ) Unit).run s =
      (.ok (), setFlags s (fpCompareFlags z)) := by
  rw [setFlags_eq_of_store (R := setSlice (setSlice (setSlice (setSlice (setSlice (setSlice
    s.RFLAGS 7 1 0) 6 1 (z.extractLsb' 2 1)) 2 1 (z.extractLsb' 1 1)) 11 1 0) 4 1 0) 0 1
    (z.extractLsb' 0 1))]
  · rfl
  · unfold fpCompareFlags
    rflags_ext

/-! ### Packed operations -/

/-- A packed float operation's lanes and flags as lean-x86's loop builds them: lane `i` of the
result is `(f i).1`, and the flags are every lane's `(f i).2` ORed in lane order. -/
def fpPackedRun (w : Nat) (f : Nat → BitVec w × BitVec 6) : BitVec 6 × BitVec 128 :=
  (List.range (128 / w)).foldl (fun r i => (r.1 ||| (f i).2, setSlice r.2 (i * w) w (f i).1)) (0, 0)

/-- The lanes of a packed float result: lane `i` is `(f i).1` (`fpPacked_eq`). -/
def fpPacked (w : Nat) (f : Nat → BitVec w × BitVec 6) : BitVec 128 := (fpPackedRun w f).2

/-- The exception flags of a packed float operation: those of every lane, ORed. -/
def fpPackedFlags (w : Nat) (f : Nat → BitVec w × BitVec 6) : BitVec 6 := (fpPackedRun w f).1

/-- A `for i in [0, k)` loop in `SpecM` whose every pass yields `g i` of the accumulator and leaves
the state alone (lean-x86's packed float loops, once their checks pass) is a `foldl`. -/
theorem specM_forIn_lanes {ε σ β : Type} (k : Nat) (init : β)
    (body : Int → β → SpecM ε σ (ForInStep β)) (g : Nat → β → β) (s : σ)
    (h : ∀ i < k, ∀ r, (body (0 + (i : Int)) r).run s = (.ok (.yield (g i r)), s)) :
    (forIn ((List.range k).map (fun i : Nat => (0 : Int) + (i : Int))) init body).run s =
      (.ok ((List.range k).foldl (fun r i => g i r) init), s) := by
  rw [List.forIn_map]
  have : ∀ l : List Nat, (∀ i ∈ l, i < k) → ∀ init,
      (forIn l init (fun (i : Nat) (r : β) => body (0 + (i : Int)) r)).run s =
      (.ok (l.foldl (fun r i => g i r) init), s) := by
    intro l hl
    induction l with
    | nil => intro; rfl
    | cons a l ih =>
      intro init
      rw [List.forIn_cons, specM_bind_run _ _ (h a (hl a (by simp)) init)]
      exact ih (fun i hi => hl i (by simp [hi])) _
  exact this _ (fun i hi => List.mem_range.mp hi) init

/-- A choice between two returned values, then the rest: the rest of the chosen value (CMPPS's
all-ones-or-zero lane). -/
theorem bind_ite_pure {ε σ α β : Type} (c : Prop) [Decidable c] (x y : α)
    (k : α → SpecM ε σ β) :
    ((if c then pure x else pure y : SpecM ε σ α) >>= k) = k (if c then x else y) := by
  split <;> rfl

/-- Lane `i` of `x` as lean-x86's loops slice it. -/
theorem extractLsb'_eq_lane {n : Nat} (w : Nat) (x : BitVec n) (i : Nat) :
    x.extractLsb' (i * w) w = lane w x i := rfl

/-- With every exception masked, `FP.Prioritize_Operand_Exceptions f` keeps only the invalid
exception when it is raised (and the divide-by-zero one when it is), else `f`. -/
def fpOperandPrio (f : BitVec 6) : BitVec 6 :=
  if f.extractLsb' 0 1 == 1 then 1 else if f.extractLsb' 2 1 == 1 then 4 else f

theorem prioritizeOperandExceptions_masked (f : BitVec 6) {m : BitVec 6} (hm : m = 63) :
    FP.Prioritize_Operand_Exceptions f m = .ok (fpOperandPrio f) := by
  subst hm
  unfold FP.Prioritize_Operand_Exceptions fpOperandPrio
  have h : (f &&& ~~~(63 : BitVec 6)) = 0 := by
    rw [show ~~~(63 : BitVec 6) = 0 by decide]
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp
  simp only [h, FP_Exception_Flags_Type.IE, FP_Exception_Flags_Type.ZE,
    FP_Exception_Flags_Type.DE]
  have h1 : (BitVec.extractLsb' 1 1 (0 : BitVec 6) == 1) = false := by decide
  rw [h1]
  generalize (BitVec.extractLsb' 0 1 f == 1) = c0
  generalize (BitVec.extractLsb' 2 1 f == 1) = c2
  cases c0 <;> cases c2 <;> rfl

/-- The packed loop's accumulator (the flags ORed so far, the result so far) is the pair of the two
folds. -/
theorem foldl_fpLanes {n : Nat} (w : Nat) (F : Nat → BitVec w × BitVec 6) (l : List Nat)
    (x : BitVec 6) (y : BitVec n) :
    l.foldl (fun r i => (r.1 ||| (F i).2, setSlice r.2 (i * w) w (F i).1)) (x, y) =
      (l.foldl (fun acc i => acc ||| (F i).2) x,
        l.foldl (fun r i => setSlice r (i * w) w (F i).1) y) := by
  induction l generalizing x y with
  | nil => rfl
  | cons a l ih => exact ih _ _

/-- The packed result is the value whose `w`-bit lanes are the lanes' results. -/
theorem fpPacked_eq (w : Nat) (f : Nat → BitVec w × BitVec 6) :
    fpPacked w f = ofLanes 128 w fun i => (f i).1 := by
  unfold fpPacked fpPackedRun
  rw [foldl_fpLanes]
  rfl

/-- The packed flags are the lanes' flags ORed in lane order. -/
theorem fpPackedFlags_eq (w : Nat) (f : Nat → BitVec w × BitVec 6) :
    fpPackedFlags w f = (List.range (128 / w)).foldl (fun acc i => acc ||| (f i).2) 0 := by
  unfold fpPackedFlags fpPackedRun
  rw [foldl_fpLanes]

/-- A float operation's first `k` lanes and flags as lean-x86's loop builds them, the rest of the
result zero (CVTPD2PS: two single-precision lanes from two double-precision ones): lane `i < k` of
the result is `(f i).1`, and the flags are those `(f i).2` ORed in lane order. -/
def fpLanesRun (k w : Nat) (f : Nat → BitVec w × BitVec 6) : BitVec 6 × BitVec 128 :=
  (List.range k).foldl (fun r i => (r.1 ||| (f i).2, setSlice r.2 (i * w) w (f i).1)) (0, 0)

/-- The result of `fpLanesRun`: lanes `i < k` are `(f i).1`, the rest zero (`fpLanes_eq`). -/
def fpLanes (k w : Nat) (f : Nat → BitVec w × BitVec 6) : BitVec 128 := (fpLanesRun k w f).2

/-- The flags of `fpLanesRun`: those of lanes `i < k`, ORed. -/
def fpLanesFlags (k w : Nat) (f : Nat → BitVec w × BitVec 6) : BitVec 6 := (fpLanesRun k w f).1

/-- `fpLanesRun` into an `n`-bit value `init` (the conversions to and from MMX registers: two
lanes into zero for CVTPS2PI, into the old XMM value for CVTPI2PS). -/
def fpLanesOnto {n : Nat} (k w : Nat) (f : Nat → BitVec w × BitVec 6) (init : BitVec n) :
    BitVec 6 × BitVec n :=
  (List.range k).foldl (fun r i => (r.1 ||| (f i).2, setSlice r.2 (i * w) w (f i).1)) (0, init)

/-- The first `k` lanes, written into zero one by one. -/
theorem fpLanes_eq (k w : Nat) (f : Nat → BitVec w × BitVec 6) :
    fpLanes k w f = (List.range k).foldl (fun r i => setSlice r (i * w) w (f i).1) 0 := by
  unfold fpLanes fpLanesRun
  rw [foldl_fpLanes]

/-- The flags of the first `k` lanes, ORed in lane order. -/
theorem fpLanesFlags_eq (k w : Nat) (f : Nat → BitVec w × BitVec 6) :
    fpLanesFlags k w f = (List.range k).foldl (fun acc i => acc ||| (f i).2) 0 := by
  unfold fpLanesFlags fpLanesRun
  rw [foldl_fpLanes]

/-- Step through a scalar ADD/SUB/MUL/DIV operation (lean-x86's `ADDSf`, …, unfolded, at a literal
element size): `hb` the legacy context's `evex_b = 0`, `hm : MxcsrPre s`, `hok` the lane's
definedness. -/
macro "fp_scalar_arith" hb:term:max hm:term:max hok:term:max : tactic => `(tactic| (
  simp (config := { decide := true }) only [x86_runtime, $hb:term, Int.reduceBEq, Bool.true_or,
    pure_bind, BitVec.reduceBEq]
  refine (specM_bind_run _ _ (getDAZ_run _ (by decide) _)).trans ?_
  refine (specM_bind_run _ _ (getFTZ_run _ (by decide) _)).trans ?_
  refine (specM_bind_run _ _ (mxcsrUM_run _)).trans ?_
  refine (specM_bind_run _ _ (mxcsrMasks_run _)).trans ?_
  simp only [and_false_left, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run _ _ (mxcsrRC_run _)).trans ?_
  refine (specM_bind_run _ _ (liftM_run_of_ok (decodeRoundingMode_eq _) _)).trans ?_
  refine (specM_bind_run _ _ (fpArith_run _ (by decide) _ _ _ _ $hok)).trans ?_
  refine (specM_bind_run _ _ (checkExceptions_run _ _ $hm)).trans ?_
  simp only [x86_runtime, BitVec.cast_eq, pure_bind]
  rw [setSlice_scalar _ (by decide)]
  rfl))


/-- Step through a scalar MIN/MAX operation (lean-x86's `MINSf`, `MAXSf`, unfolded, at a literal
element size): `hm : MxcsrPre s`, `hok` the lane's definedness. -/
macro "fp_scalar_minmax" hm:term:max hok:term:max : tactic => `(tactic| (
  simp (config := { decide := true }) only [x86_runtime, Int.reduceBEq, Bool.true_or, pure_bind,
    BitVec.reduceBEq]
  refine (specM_bind_run _ _ (getDAZ_run _ (by decide) _)).trans ?_
  refine (specM_bind_run _ _ (mxcsrMasks_run _)).trans ?_
  refine (specM_bind_run _ _ (fpMinMax_run _ (by decide) _ _ _ _ $hok)).trans ?_
  refine (specM_bind_run _ _ (checkExceptions_run _ _ $hm)).trans ?_
  simp only [x86_runtime, BitVec.cast_eq, pure_bind]
  rw [setSlice_scalar _ (by decide)]
  rfl))

/-- Step through a scalar SQRT operation (lean-x86's `SQRTSf`, unfolded, at a literal element
size): `hb` the legacy context's `evex_b = 0`, `hm : MxcsrPre s`, `hok` the lane's
definedness. -/
macro "fp_scalar_sqrt" hb:term:max hm:term:max hok:term:max : tactic => `(tactic| (
  simp (config := { decide := true }) only [x86_runtime, $hb:term, Int.reduceBEq, Bool.true_or,
    pure_bind, BitVec.reduceBEq]
  refine (specM_bind_run _ _ (getDAZ_run _ (by decide) _)).trans ?_
  refine (specM_bind_run _ _ (getFTZ_run _ (by decide) _)).trans ?_
  refine (specM_bind_run _ _ (mxcsrMasks_run _)).trans ?_
  simp only [and_false_left, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run _ _ (mxcsrRC_run _)).trans ?_
  refine (specM_bind_run _ _ (liftM_run_of_ok (decodeRoundingMode_eq _) _)).trans ?_
  refine (specM_bind_run _ _ (fpSqrt_run _ (by decide) _ _ $hok)).trans ?_
  refine (specM_bind_run _ _ (checkExceptions_run _ _ $hm)).trans ?_
  simp only [x86_runtime, BitVec.cast_eq, pure_bind]
  rw [setSlice_scalar _ (by decide)]
  rfl))


/-- The first steps of a packed ADD/SUB/MUL/DIV operation (lean-x86's `ADDPf`, …, unfolded, at
a literal lane width): the MXCSR reads (DAZ, FTZ, UM, the masks, RC) up to the lane loop. `hb` is
the legacy context's `evex_b = 0`. -/
macro "fp_packed_start" hb:term:max : tactic => `(tactic| (
  simp (config := { decide := true }) only [x86_runtime, $hb:term, Int.reduceBEq, Bool.true_or,
    Bool.or_true, pure_bind, BitVec.reduceBEq]
  refine (specM_bind_run _ _ (getDAZ_run _ (by decide) _)).trans ?_
  refine (specM_bind_run _ _ (getFTZ_run _ (by decide) _)).trans ?_
  refine (specM_bind_run _ _ (mxcsrUM_run _)).trans ?_
  refine (specM_bind_run _ _ (mxcsrMasks_run _)).trans ?_
  simp only [and_false_left, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run _ _ (mxcsrRC_run _)).trans ?_
  refine (specM_bind_run _ _ (liftM_run_of_ok (decodeRoundingMode_eq _) _)).trans ?_))

/-- The first steps of a packed MIN/MAX operation (lean-x86's `MINPf`, `MAXPf`): DAZ and the
masks. -/
macro "fp_packed_start_minmax" : tactic => `(tactic| (
  simp (config := { decide := true }) only [x86_runtime, Int.reduceBEq, Bool.true_or,
    Bool.or_true, pure_bind, BitVec.reduceBEq, bind_ite_pure]
  refine (specM_bind_run _ _ (getDAZ_run _ (by decide) _)).trans ?_
  refine (specM_bind_run _ _ (mxcsrMasks_run _)).trans ?_))

/-- The first steps of a packed SQRT operation (lean-x86's `SQRTPf`): DAZ, FTZ, the masks, RC. -/
macro "fp_packed_start_sqrt" hb:term:max : tactic => `(tactic| (
  simp (config := { decide := true }) only [x86_runtime, $hb:term, Int.reduceBEq, Bool.true_or,
    Bool.or_true, pure_bind, BitVec.reduceBEq]
  refine (specM_bind_run _ _ (getDAZ_run _ (by decide) _)).trans ?_
  refine (specM_bind_run _ _ (getFTZ_run _ (by decide) _)).trans ?_
  refine (specM_bind_run _ _ (mxcsrMasks_run _)).trans ?_
  simp only [and_false_left, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run _ _ (mxcsrRC_run _)).trans ?_
  refine (specM_bind_run _ _ (liftM_run_of_ok (decodeRoundingMode_eq _) _)).trans ?_))

/-- Pass `i` of a packed float lane loop of `w`-bit lanes: the bounds checks, the operands' lanes,
the lane's float function by `lanerun i hi` (`hi : i < 128 / w`), then (`masked hm`) lean-x86's
`FP.Prioritize_Operand_Exceptions` with every exception masked (`hm`), and the lane written into
the result. -/
syntax "fp_lane " num term:max (" masked " term:max)? : tactic
macro_rules
  | `(tactic| fp_lane $w $lanerun $[masked $hm]?) => do
    let prio ← match hm with
      | some hm => `(tactic| refine (specM_bind_run _ _
          (liftM_run_of_ok (prioritizeOperandExceptions_masked _ $hm) _)).trans ?_)
      | none => `(tactic| skip)
    `(tactic| (
      intro i hi r
      have hik : i < 128 / $w := by simpa using hi
      have h0 : (0 : Int) ≤ (i : Int) * $w := by omega
      have h1 : (i : Int) * $w + $w ≤ 128 := by omega
      have h2 : (i : Int) * $w ≤ 128 - $w := by omega
      simp only [Int.reduceSub] at h2
      simp only [Int.zero_add, h2, decide_true, assert_of_true, pure_bind,
        sliceElement_bitVec_eq_pure _ h0 (by decide) h1, natCast_mul_toNat i $w (by decide),
        Int.reduceToNat, extractLsb'_eq_lane]
      refine (specM_bind_run _ _ ($lanerun i hik)).trans ?_
      try simp only [bind_ite_pure]
      $prio:tactic
      rw [setSliceChecked_eq_pure _ _ h0 (by decide) h1]
      simp only [pure_bind, natCast_mul_toNat i $w (by decide), Int.reduceToNat]
      rfl))

/-- A packed float operation's lane loop and what follows it: each pass by `fp_lane w lanerun`
(with `masked hm` for `FP.Prioritize_Operand_Exceptions`), then the flags ORed into MXCSR
(`hm : MxcsrPre s`) and the lanes returned. -/
syntax "fp_packed_loop " num term:max term:max (" masked")? : tactic
macro_rules
  | `(tactic| fp_packed_loop $w $lanerun $hm $[masked%$m]?) => do
    let lane ← match m with
      | some _ => `(tactic| fp_lane $w $lanerun masked $hm)
      | none => `(tactic| fp_lane $w $lanerun)
    `(tactic| (
      refine (specM_bind_run _ _ (specM_forIn_lanes _ _ _ ?g _ ?h)).trans ?k
      case h => $lane:tactic
      case k =>
        try simp only [and_false_left, Bool.false_eq_true, ↓reduceIte]
        refine (specM_bind_run _ _ (checkExceptions_run _ _ $hm)).trans ?_
        rfl))


/-- `fp_packed_loop` for a loop whose lane is chosen by a test (CMPPS: all ones or zero, by the
comparison): the accumulator step `g` is given, and each pass splits on the test. -/
macro "fp_packed_loop_split " w:num g:term:max lanerun:term:max hm:term:max : tactic => `(tactic| (
  refine (specM_bind_run _ _ (specM_forIn_lanes _ _ _ $g _ ?h)).trans ?k
  case h =>
    intro i hi r
    have hik : i < 128 / $w := by simpa using hi
    have h0 : (0 : Int) ≤ (i : Int) * $w := by omega
    have h1 : (i : Int) * $w + $w ≤ 128 := by omega
    have h2 : (i : Int) * $w ≤ 128 - $w := by omega
    simp only [Int.reduceSub] at h2
    simp only [Int.zero_add, h2, decide_true, assert_of_true, pure_bind,
      sliceElement_bitVec_eq_pure _ h0 (by decide) h1, natCast_mul_toNat i $w (by decide),
      Int.reduceToNat, extractLsb'_eq_lane]
    refine (specM_bind_run _ _ ($lanerun i hik)).trans ?_
    split <;> rename_i htest <;>
      refine (specM_bind_run _ _
        (liftM_run_of_ok (prioritizeOperandExceptions_masked _ $hm) _)).trans ?_ <;>
      rw [setSliceChecked_eq_pure _ _ h0 (by decide) h1] <;>
      simp only [pure_bind, natCast_mul_toNat i $w (by decide), Int.reduceToNat, htest,
        ↓reduceIte] <;>
      rfl
  case k =>
    refine (specM_bind_run _ _ (checkExceptions_run _ _ $hm)).trans ?_
    rfl))

/-- Pass `i` of a converting lane loop (CVTPS2PD, CVTDQ2PS, …): `k` lanes, each reading a
`ws`-bit lane of the `n`-bit source and writing a `w`-bit lane of the 128-bit result (`into
rs`: of the `rs`-bit result, CVTPS2PI's 64). The bounds
checks, the source lane, the lane's function by `lanerun i hi` (`hi : i < k`), then (`masked hm`)
lean-x86's `FP.Prioritize_Operand_Exceptions` with every exception masked (`hm`), and the lane
written into the result. -/
syntax "fp_cvt_lane " num num num num term:max (" masked " term:max)? (" into " num)? : tactic
macro_rules
  | `(tactic| fp_cvt_lane $k $ws $n $w $lanerun $[masked $hm]? $[into $rs]?) => do
    let rs := rs.getD (Lean.Syntax.mkNumLit "128")
    let prio ← match hm with
      | some hm => `(tactic| refine (specM_bind_run _ _
          (liftM_run_of_ok (prioritizeOperandExceptions_masked _ $hm) _)).trans ?_)
      | none => `(tactic| skip)
    `(tactic| (
      intro i hi r
      have hik : i < $k := by simpa using hi
      have h0s : (0 : Int) ≤ (i : Int) * $ws := by omega
      have h1s : (i : Int) * $ws + $ws ≤ $n := by omega
      have h2s : (i : Int) * $ws ≤ $n - $ws := by omega
      have h0 : (0 : Int) ≤ (i : Int) * $w := by omega
      have h1 : (i : Int) * $w + $w ≤ $rs := by omega
      have h2 : (i : Int) * $w ≤ $rs - $w := by omega
      simp only [Int.reduceSub] at h2s h2
      simp only [Int.zero_add, h2s, h2, decide_true, assert_of_true, pure_bind,
        sliceElement_bitVec_eq_pure _ h0s (by decide) h1s, natCast_mul_toNat i $ws (by decide),
        Int.reduceToNat, extractLsb'_eq_lane]
      refine (specM_bind_run _ _ ($lanerun i hik)).trans ?_
      $prio:tactic
      rw [setSliceChecked_eq_pure _ _ h0 (by decide) h1]
      simp only [pure_bind, natCast_mul_toNat i $w (by decide), Int.reduceToNat]
      rfl))

/-- A converting lane loop (`fp_cvt_lane k ws n w lanerun`, with `masked` for
`FP.Prioritize_Operand_Exceptions`) and what follows it: the flags ORed into MXCSR
(`hm : MxcsrPre s`) and the lanes returned. -/
syntax "fp_cvt_loop " num num num num term:max term:max (" masked")? (" into " num)? : tactic
macro_rules
  | `(tactic| fp_cvt_loop $k $ws $n $w $lanerun $hm $[masked%$m]? $[into $rs]?) => do
    let rs := rs.getD (Lean.Syntax.mkNumLit "128")
    let lane ← match m with
      | some _ => `(tactic| fp_cvt_lane $k $ws $n $w $lanerun masked $hm into $rs)
      | none => `(tactic| fp_cvt_lane $k $ws $n $w $lanerun into $rs)
    `(tactic| (
      refine (specM_bind_run _ _ (specM_forIn_lanes _ _ _ ?g _ ?h)).trans ?k
      case h => $lane:tactic
      case k =>
        try simp only [and_false_left, Bool.false_eq_true, ↓reduceIte]
        refine (specM_bind_run _ _ (checkExceptions_run _ _ $hm)).trans ?_
        rfl))

/-! ### Conversions to integers -/

/-- lean-x86's `FP.To_Int x true r` (the `e`-bit float `x` to a signed `r`-bit integer), with DAZ
from MXCSR `mx` and the rounding mode `rm` the form passes (CVTSS2SI, CVTPS2DQ: MXCSR.RC;
CVTTSS2SI, CVTTPS2DQ: toward zero). It is a `PartialResult`: `FP87.Convert_From_Float` normalizes
a denormal with a loop lean-x86 does not show terminates. -/
def fpToIntRun (e r : Nat) (rm : Rounding_Mode) (mx : BitVec 32) (x : BitVec e) :
    Option (Except (Error Empty) (BitVec r × BitVec 6)) :=
  (FP.To_Int (N := e) x true r (mxDaz mx) rm false).run

/-- `x` converted to a signed `r`-bit integer and the exception flags, as lean-x86 computes them
with DAZ from MXCSR `mx` and rounding mode `rm` (a NaN, an infinity or a value out of range is
the integer indefinite value `1 << (r - 1)` with the invalid flag, lean-x86's own result). -/
def fpToInt (e r : Nat) (rm : Rounding_Mode) (mx : BitVec 32) (x : BitVec e) :
    BitVec r × BitVec 6 :=
  match fpToIntRun e r rm mx x with
  | some (.ok v) => v
  | _ => default

/-- lean-x86's `FP.To_Int` terminates and returns a value on `x` (DAZ from `mx`, rounding mode
`rm`). -/
def FpToIntOk (e r : Nat) (rm : Rounding_Mode) (mx : BitVec 32) (x : BitVec e) : Prop :=
  ∃ v, fpToIntRun e r rm mx x = some (.ok v)

/-- `FP.To_Int` with DAZ from MXCSR `mx` returns `fpToInt` (it reads no state: DAZ and the
rounding mode are its arguments). -/
theorem fpToInt_run (e r : Nat) (rm : Rounding_Mode) (mx : BitVec 32) (x : BitVec e)
    (hok : FpToIntOk e r rm mx x) :
    FP.To_Int (N := e) x true r (mxDaz mx) rm false = pure (fpToInt e r rm mx x) := by
  obtain ⟨v, hv⟩ := hok
  unfold fpToInt
  rw [hv]
  exact hv

/-- `specM_forIn_lanes` in `PartialSpecM` (CVTPS2DQ, CVTTPD2DQ, …: lane loops whose body converts
to integers with the partial `FP.To_Int`). -/
theorem partialSpecM_forIn_lanes {ε σ β : Type} (k : Nat) (init : β)
    (body : Int → β → PartialSpecM ε σ (ForInStep β)) (g : Nat → β → β) (s : σ)
    (h : ∀ i < k, ∀ r, (body (0 + (i : Int)) r).run s = some (.ok (.yield (g i r)), s)) :
    (forIn ((List.range k).map (fun i : Nat => (0 : Int) + (i : Int))) init body).run s =
      some (.ok ((List.range k).foldl (fun r i => g i r) init), s) := by
  rw [List.forIn_map]
  have : ∀ l : List Nat, (∀ i ∈ l, i < k) → ∀ init,
      (forIn l init (fun (i : Nat) (r : β) => body (0 + (i : Int)) r)).run s =
      some (.ok (l.foldl (fun r i => g i r) init), s) := by
    intro l hl
    induction l with
    | nil => intro; rfl
    | cons a l ih =>
      intro init
      rw [List.forIn_cons, partialSpecM_bind_run _ _ (h a (hl a (by simp)) init)]
      exact ih (fun i hi => hl i (by simp [hi])) _
  exact this _ (fun i hi => List.mem_range.mp hi) init

/-- `fp_cvt_lane` for a lane loop in `PartialSpecM` whose lane is lean-x86's partial `FP.To_Int`:
`lanerun i hi` is the lane's `fpToInt_run`. -/
syntax "fp_cvt_lane_partial " num num num num term:max (" masked " term:max)? (" into " num)? :
  tactic
macro_rules
  | `(tactic| fp_cvt_lane_partial $k $ws $n $w $lanerun $[masked $hm]? $[into $rs]?) => do
    let rs := rs.getD (Lean.Syntax.mkNumLit "128")
    let prio ← match hm with
      | some hm => `(tactic| refine (partialSpecM_bind_run _ _
          (partialSpecM_liftM_run_of_ok (prioritizeOperandExceptions_masked _ $hm) _)).trans ?_)
      | none => `(tactic| skip)
    `(tactic| (
      intro i hi r
      have hik : i < $k := by simpa using hi
      have h0s : (0 : Int) ≤ (i : Int) * $ws := by omega
      have h1s : (i : Int) * $ws + $ws ≤ $n := by omega
      have h2s : (i : Int) * $ws ≤ $n - $ws := by omega
      have h0 : (0 : Int) ≤ (i : Int) * $w := by omega
      have h1 : (i : Int) * $w + $w ≤ $rs := by omega
      have h2 : (i : Int) * $w ≤ $rs - $w := by omega
      simp only [Int.reduceSub] at h2s h2
      simp only [Int.zero_add, h2s, h2, decide_true, assert_of_true, pure_bind,
        sliceElement_bitVec_eq_pure _ h0s (by decide) h1s, natCast_mul_toNat i $ws (by decide),
        Int.reduceToNat, extractLsb'_eq_lane]
      refine (partialSpecM_bind_run _ _ (partialResult_lift_run ($lanerun i hik) _)).trans ?_
      $prio:tactic
      rw [setSliceChecked_eq_pure _ _ h0 (by decide) h1]
      simp only [pure_bind, natCast_mul_toNat i $w (by decide), Int.reduceToNat]
      rfl))

/-- `fp_cvt_loop` in `PartialSpecM` (`partialSpecM_forIn_lanes`, `fp_cvt_lane_partial`): the lane
loop, the flags ORed into MXCSR (`hm : MxcsrPre s`) and the lanes returned. -/
syntax "fp_cvt_loop_partial " num num num num term:max term:max (" masked")? (" into " num)? :
  tactic
macro_rules
  | `(tactic| fp_cvt_loop_partial $k $ws $n $w $lanerun $hm $[masked%$m]? $[into $rs]?) => do
    let rs := rs.getD (Lean.Syntax.mkNumLit "128")
    let lane ← match m with
      | some _ => `(tactic| fp_cvt_lane_partial $k $ws $n $w $lanerun masked $hm into $rs)
      | none => `(tactic| fp_cvt_lane_partial $k $ws $n $w $lanerun into $rs)
    `(tactic| (
      refine (partialSpecM_bind_run _ _ (partialSpecM_forIn_lanes _ _ _ ?g _ ?h)).trans ?k
      case h => $lane:tactic
      case k =>
        try simp only [and_false_left, Bool.false_eq_true, ↓reduceIte]
        refine (partialSpecM_liftTotal_bind_run _ _ (checkExceptions_run _ _ $hm)).trans ?_
        rfl))

/-! ### Reciprocal approximations -/

open Lean Meta Elab Tactic in
/-- One step of `keeps_state`: introduce a bound value, or apply the `ReadOnly` rule (for no
relation: the state is left alone, the result may depend on anything) for the head of the
computation (bind, `get`, `pure`, `liftM`, `assert`, `readInitialized`, `liftNoSourceException`,
a branch, decided by `decide` when its condition is closed, `throw`), split a `match`, close a leaf
whose run is `rfl`-constant in the state, or unfold the head definition. -/
elab "keeps_state_step" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  if tgt.isForall then
    evalTactic (← `(tactic| intro _))
    return
  unless tgt.isAppOf ``ReadOnly do throwError "keeps_state: not a ReadOnly goal"
  let m := tgt.appArg!.consumeMData
  if m.isLet || m.isAppOf ``letFun then
    evalTactic (← `(tactic| dsimp only))
    return
  let head := m.getAppFn.constName?.getD .anonymous
  let run (t : TSyntax `tactic) : TacticM Unit := evalTactic t
  if head == ``Bind.bind || head == ``bind then
    let first := m.getAppArgs[m.getAppNumArgs - 2]!
    let fh := first.getAppFn.constName?.getD .anonymous
    if fh == ``MonadStateOf.get || fh == ``get || fh == ``getThe || fh == ``MonadState.get then
      run (← `(tactic| refine ReadOnly.get_bind (fun _ _ h => h.elim) (fun _ => ?_)))
    else run (← `(tactic| refine ReadOnly.bind ?_ (fun _ => ?_)))
  else if head == ``Pure.pure || head == ``pure then run (← `(tactic| exact ReadOnly.pure _))
  else if head == ``liftM then run (← `(tactic| exact ReadOnly.lift _))
  else if head == ``X86.Runtime.assert then run (← `(tactic| exact ReadOnly.assert _))
  else if head == ``X86.Runtime.readInitialized then
    run (← `(tactic| exact ReadOnly.readInitialized _))
  else if head == ``X86.Runtime.liftNoSourceException then
    run (← `(tactic| refine ReadOnly.liftNoSourceException ?_))
  else if head == ``ite then
    run (← `(tactic| first
      | rw [ite_eq_left_of_eq_true (eq_true (by decide))]
      | rw [ite_eq_right_of_eq_false (eq_false (by decide))]
      | refine ReadOnly.ite ?_ ?_))
  else if head == ``dite then
    run (← `(tactic| first
      | rw [dite_cond_eq_true (eq_true (by decide))]
      | rw [dite_cond_eq_false (eq_false (by decide))]
      | refine ReadOnly.dite ?_ ?_))
  else if head == ``MonadExceptOf.throw || head == ``MonadExcept.throw || head == ``throw ||
      head == ``throwThe then
    run (← `(tactic| exact ReadOnly.throw _))
  else if (← isMatcherApp m) then run (← `(tactic| split))
  else
    try run (← `(tactic| exact ReadOnly.of_const _ (fun _ => rfl)))
    catch _ =>
      if head != .anonymous then run (← `(tactic| unfold $(mkIdent head):ident))
      else throwError "keeps_state: cannot step {m}"

/-- Prove `ReadOnly (fun _ _ => False) m` (running `m` leaves the state as it is) for a lean-x86
computation built from binds, `get`, `pure`, `liftM`, assertions, branches and `throw`, unfolding
the helpers it calls. -/
macro "keeps_state" : tactic => `(tactic| repeat' keeps_state_step)

/-- lean-x86's `FP.Reciprocal x` (RCPSS, RCPPS: the approximate reciprocal of the single-precision
`x`; a normal `x` goes to the machine's numerical binding `Emulate_RCPSS`, which may read the state)
run from `s`. -/
def fpRcpRun [Bindings] (x : BitVec 32) (s : RamState) : Except (Error X86.Exception) (BitVec 32) :=
  ((FP.Reciprocal (N := 32) x : SpecM X86.Exception RamState _).run s).1

/-- The approximate reciprocal of `x` as lean-x86 computes it (its value from the default state;
`FpRcpOk` makes it the value from every state). -/
def fpRcp [Bindings] (x : BitVec 32) : BitVec 32 := laneVal (fpRcpRun x default)

/-- lean-x86's `FP.Reciprocal` returns a value on `x`, the same from every state (the numerical
binding returns a value and does not depend on the state). -/
def FpRcpOk [Bindings] (x : BitVec 32) : Prop := ∃ v, ∀ s, fpRcpRun x s = .ok v

/-- lean-x86's `FP.Reciprocal_Sqrt x` (RSQRTSS, RSQRTPS: the approximate reciprocal square root;
the numerical binding `Emulate_RSQRTSS`) run from `s`. -/
def fpRsqrtRun [Bindings] (x : BitVec 32) (s : RamState) :
    Except (Error X86.Exception) (BitVec 32) :=
  ((FP.Reciprocal_Sqrt (N := 32) x : SpecM X86.Exception RamState _).run s).1

/-- The approximate reciprocal square root of `x` as lean-x86 computes it. -/
def fpRsqrt [Bindings] (x : BitVec 32) : BitVec 32 := laneVal (fpRsqrtRun x default)

/-- lean-x86's `FP.Reciprocal_Sqrt` returns a value on `x`, the same from every state. -/
def FpRsqrtOk [Bindings] (x : BitVec 32) : Prop := ∃ v, ∀ s, fpRsqrtRun x s = .ok v

/-- `FP.Reciprocal` leaves the state alone (the numerical binding only reads it). -/
theorem fpRcp_reads [Bindings] (x : BitVec 32) :
    ReadOnly (fun _ _ => False) (FP.Reciprocal (N := 32) x : SpecM X86.Exception RamState _) := by
  unfold FP.Reciprocal
  keeps_state

/-- `FP.Reciprocal_Sqrt` leaves the state alone. -/
theorem fpRsqrt_reads [Bindings] (x : BitVec 32) :
    ReadOnly (fun _ _ => False)
      (FP.Reciprocal_Sqrt (N := 32) x : SpecM X86.Exception RamState _) := by
  unfold FP.Reciprocal_Sqrt
  keeps_state

/-- `FP.Reciprocal` on `x`, where lean-x86 returns a value from every state, returns `fpRcp x`
and leaves the state alone. -/
theorem fpRcp_run [Bindings] (x : BitVec 32) (s : RamState) (hok : FpRcpOk x) :
    (FP.Reciprocal (N := 32) x : SpecM X86.Exception RamState _).run s = (.ok (fpRcp x), s) := by
  obtain ⟨v, hv⟩ := hok
  refine (fpRcp_reads x).run_of_result ?_
  show fpRcpRun x s = _
  rw [hv s, fpRcp, hv default]
  rfl

/-- `FP.Reciprocal_Sqrt` on `x`, where lean-x86 returns a value from every state, returns
`fpRsqrt x` and leaves the state alone. -/
theorem fpRsqrt_run [Bindings] (x : BitVec 32) (s : RamState) (hok : FpRsqrtOk x) :
    (FP.Reciprocal_Sqrt (N := 32) x : SpecM X86.Exception RamState _).run s =
      (.ok (fpRsqrt x), s) := by
  obtain ⟨v, hv⟩ := hok
  refine (fpRsqrt_reads x).run_of_result ?_
  show fpRsqrtRun x s = _
  rw [hv s, fpRsqrt, hv default]
  rfl

end X86Proofs
