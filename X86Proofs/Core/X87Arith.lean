import X86Proofs.Core.X87
import X86.Instructions.FADD
import X86.Instructions.FSUB
import X86.Instructions.FMUL
import X86.Instructions.FDIV
import X86.Instructions.FSQRT

/-!
# x87 arithmetic: lean-x86's register-stack float functions at a masked control word

The x87 arithmetic forms (FADD, FSUB, FMUL, FDIV and their reversed and popping forms, FSQRT,
FRNDINT) compute with lean-x86's own float model (`FP87.Add`, `FP87.Subtract`, `FP87.Multiply`,
`FP87.Divide`, `FP87.Sqrt` on exact integers, rounding by `Emulate_FP87_Result`;
`FP87.Round_To_Integer`).
As for SSE (`Core/Float.lean`), there is no independent IEEE-754 library to state them against, so
the library states each as lean-x86's function, evaluated at the control word FCW it reads:

- `fcwRun m fcw`: the result of `m` at FCW = `fcw`. `ReadsFcw m`: from any state whose FCW masks
  every exception (`FcwMasked`), `m` returns its result at that state's FCW and leaves the state
  alone. The masked control word matters: with the denormal exception masked (DM = 1) the helpers
  never take their `UNSPECIFIED` branch (an unmasked denormal operand leaves the result
  unspecified), so they read nothing but FCW (`ReadsFcw.dm_bind`). `reads_fcw` proves `ReadsFcw`
  of a helper by stepping through its body.
- The lanes: `x87Arith op fcw x y` (`op`: `X87Op.add`, `sub`, `mul`, `div`; the result, whether it
  was rounded up, the six exception flags) and `x87Sqrt fcw x`, each with its definedness predicate
  (`X87ArithOk`, `X87SqrtOk`: lean-x86 returns a value, `LaneOk`; its helpers assert, e.g., that
  the precision control is not the reserved value 1). `x87Rndint rc x` (`FP87.Round_To_Integer`,
  a pure function of the rounding control) with `X87RndintOk`.
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers X86.Runtime

/-- A state whose FCW is `fcw` (the rest is lean-x86's default state). -/
def fcwState (fcw : BitVec 16) : RamState := { (default : RamState) with FP87_Control := fcw }

/-- The result of `m` at FCW = `fcw`. -/
def fcwRun {α : Type} (m : SpecM X86.Exception RamState α) (fcw : BitVec 16) :
    Except (Error X86.Exception) α :=
  (m.run (fcwState fcw)).1

/-- `m` reads nothing but FCW and changes nothing, from a state whose FCW masks every exception. -/
structure ReadsFcw {α : Type} (m : SpecM X86.Exception RamState α) : Prop where
  run_eq : ∀ s : RamState, FcwMasked s.FP87_Control → m.run s = (fcwRun m s.FP87_Control, s)

theorem fcwMasked_dm {fcw : BitVec 16} (h : FcwMasked fcw) : fcw.extractLsb' 1 1 = 1#1 := by
  unfold FcwMasked at h
  have h1 : fcw.getLsbD 1 = true := by
    have := congrArg (fun x => x.getLsbD 1) h
    simpa using this
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases (by omega : i = 0) with rfl
  simpa using h1

theorem fcwMasked_im {fcw : BitVec 16} (h : FcwMasked fcw) : fcw.extractLsb' 0 1 = 1#1 := by
  unfold FcwMasked at h
  have h1 : fcw.getLsbD 0 = true := by
    have := congrArg (fun x => x.getLsbD 0) h
    simpa using this
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases (by omega : i = 0) with rfl
  simpa using h1

namespace ReadsFcw

theorem pure' {α : Type} (a : α) : ReadsFcw (pure a : SpecM X86.Exception RamState α) :=
  ⟨fun _ _ => rfl⟩

theorem bind' {α β : Type} {m : SpecM X86.Exception RamState α}
    {k : α → SpecM X86.Exception RamState β} (hm : ReadsFcw m) (hk : ∀ a, ReadsFcw (k a)) :
    ReadsFcw (m >>= k) := by
  refine ⟨fun s hs => ?_⟩
  have hs' : FcwMasked (fcwState s.FP87_Control).FP87_Control := hs
  have h2 := hm.run_eq (fcwState s.FP87_Control) hs'
  have hfcw : (fcwState s.FP87_Control).FP87_Control = s.FP87_Control := rfl
  rw [hfcw] at h2
  unfold fcwRun
  rw [specM_run_bind, specM_run_bind, hm.run_eq s hs, h2]
  cases fcwRun m s.FP87_Control with
  | error e => rfl
  | ok a =>
    simp only
    rw [(hk a).run_eq s hs, (hk a).run_eq (fcwState s.FP87_Control) hs', hfcw]

theorem lift {α : Type} (e : Except (Error Empty) α) :
    ReadsFcw (liftM e : SpecM X86.Exception RamState α) := by
  refine ⟨fun s _ => ?_⟩
  cases e <;> rfl

theorem lift' {α : Type} (e : Except (Error X86.Exception) α) :
    ReadsFcw (liftM e : SpecM X86.Exception RamState α) := by
  refine ⟨fun s _ => ?_⟩
  cases e <;> rfl

theorem ite_of_true {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by
  simp [h]

theorem ite_of_false {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by
  simp [h]

theorem ite' {α : Type} {c : Prop} [Decidable c] {a b : SpecM X86.Exception RamState α}
    (ha : c → ReadsFcw a) (hb : ¬ c → ReadsFcw b) : ReadsFcw (if c then a else b) := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

theorem dite' {α : Type} {c : Prop} [Decidable c] {a : c → SpecM X86.Exception RamState α}
    {b : ¬ c → SpecM X86.Exception RamState α}
    (ha : ∀ h, ReadsFcw (a h)) (hb : ∀ h, ReadsFcw (b h)) : ReadsFcw (dite c a b) := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

theorem throw' {α : Type} (e : Error X86.Exception) :
    ReadsFcw (throw e : SpecM X86.Exception RamState α) := ⟨fun _ _ => rfl⟩

theorem assert' (c : Bool) : ReadsFcw (assert c : SpecM X86.Exception RamState Unit) := by
  refine ⟨fun s _ => ?_⟩
  cases c <;> rfl

theorem readInitialized' {α : Type} (o : Option α) :
    ReadsFcw (readInitialized o : SpecM X86.Exception RamState α) := by
  refine ⟨fun s _ => ?_⟩
  cases o <;> rfl

theorem pc : ReadsFcw (X86.FP87_Control.PC : SpecM X86.Exception RamState _) := ⟨fun _ _ => rfl⟩
theorem rc : ReadsFcw (X86.FP87_Control.RC : SpecM X86.Exception RamState _) := ⟨fun _ _ => rfl⟩
theorem om : ReadsFcw (X86.FP87_Control.OM : SpecM X86.Exception RamState _) := ⟨fun _ _ => rfl⟩
theorem um : ReadsFcw (X86.FP87_Control.UM : SpecM X86.Exception RamState _) := ⟨fun _ _ => rfl⟩
theorem im : ReadsFcw (X86.FP87_Control.IM : SpecM X86.Exception RamState _) := ⟨fun _ _ => rfl⟩
theorem zm : ReadsFcw (X86.FP87_Control.ZM : SpecM X86.Exception RamState _) := ⟨fun _ _ => rfl⟩
theorem pm : ReadsFcw (X86.FP87_Control.PM : SpecM X86.Exception RamState _) := ⟨fun _ _ => rfl⟩
theorem masks : ReadsFcw (X86.FP87_Control.Exception_Masks : SpecM X86.Exception RamState _) :=
  ⟨fun _ _ => rfl⟩

theorem dm_run (s : RamState) (hs : FcwMasked s.FP87_Control) :
    (X86.FP87_Control.DM : SpecM X86.Exception RamState _).run s = (.ok 1#1, s) := by
  have h : (X86.FP87_Control.DM : SpecM X86.Exception RamState _).run s =
      (.ok (s.FP87_Control.extractLsb' 1 1), s) := by
    simp [X86.FP87_Control.DM, x86_runtime]
    rfl
  rw [h, fcwMasked_dm hs]

/-- With every exception masked, DM reads 1: only the continuation at 1 matters. -/
theorem dm_bind {β : Type} {k : Bits 1 → SpecM X86.Exception RamState β}
    (hk : ReadsFcw (k 1#1)) : ReadsFcw (X86.FP87_Control.DM >>= k) := by
  refine ⟨fun s hs => ?_⟩
  have hs' : FcwMasked (fcwState s.FP87_Control).FP87_Control := hs
  unfold fcwRun
  rw [specM_run_bind, specM_run_bind, dm_run s hs, dm_run _ hs']
  simp only
  rw [hk.run_eq s hs, hk.run_eq _ hs']
  rfl

end ReadsFcw

open Lean Meta Elab Tactic in
/-- One step of `reads_fcw`: as `reads_mxcsr_step`, with the FCW field reads, a branch on a closed
condition decided, a bind of `FP87_Control.DM` continued at 1 (`ReadsFcw.dm_bind`), and the shared
rounding and arithmetic helpers by their lemmas. -/
elab "reads_fcw_step" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  if tgt.isForall then
    evalTactic (← `(tactic| intro _))
    return
  unless tgt.isAppOf ``ReadsFcw do throwError "reads_fcw: not a ReadsFcw goal"
  let some m := tgt.getAppArgs.back? | throwError "reads_fcw: unexpected goal"
  let m := m.consumeMData
  if m.isLet || m.isAppOf ``letFun || m.getAppFn.isLambda then
    evalTactic (← `(tactic| dsimp only))
    return
  let head := m.getAppFn.constName?.getD .anonymous
  let run (t : TSyntax `tactic) : TacticM Unit := evalTactic t
  if head == ``Bind.bind then
    let args := m.getAppArgs
    let first := args[args.size - 2]!
    if first.getAppFn.constName? == some ``X86.FP87_Control.DM then
      run (← `(tactic| refine ReadsFcw.dm_bind ?_))
    else
      run (← `(tactic| refine ReadsFcw.bind' ?_ ?_))
  else if head == ``Pure.pure then run (← `(tactic| exact ReadsFcw.pure' _))
  else if head == ``liftM then
    run (← `(tactic| first | exact ReadsFcw.lift _ | exact ReadsFcw.lift' _))
  else if head == ``X86.Runtime.assert then run (← `(tactic| exact ReadsFcw.assert' _))
  else if head == ``X86.Runtime.readInitialized then
    run (← `(tactic| exact ReadsFcw.readInitialized' _))
  else if head == ``ite then
    let c := m.getAppArgs[1]!
    if !c.hasFVar && !c.hasMVar then
      let cs ← Term.exprToSyntax c
      run (← `(tactic| first | rw [ReadsFcw.ite_of_true (c := $cs) (by decide)] |
        rw [ReadsFcw.ite_of_false (c := $cs) (by decide)] | refine ReadsFcw.ite' ?_ ?_))
    else
      run (← `(tactic| refine ReadsFcw.ite' ?_ ?_))
  else if head == ``dite then run (← `(tactic| refine ReadsFcw.dite' ?_ ?_))
  else if head == ``MonadExcept.throw || head == ``throw || head == ``throwThe then
    run (← `(tactic| exact ReadsFcw.throw' _))
  else if head == ``X86.FP87_Control.PC then run (← `(tactic| exact ReadsFcw.pc))
  else if head == ``X86.FP87_Control.RC then run (← `(tactic| exact ReadsFcw.rc))
  else if head == ``X86.FP87_Control.OM then run (← `(tactic| exact ReadsFcw.om))
  else if head == ``X86.FP87_Control.UM then run (← `(tactic| exact ReadsFcw.um))
  else if head == ``X86.FP87_Control.IM then run (← `(tactic| exact ReadsFcw.im))
  else if head == ``X86.FP87_Control.ZM then run (← `(tactic| exact ReadsFcw.zm))
  else if head == ``X86.FP87_Control.PM then run (← `(tactic| exact ReadsFcw.pm))
  else if head == ``X86.FP87_Control.Exception_Masks then run (← `(tactic| exact ReadsFcw.masks))
  else if head == ``X86.Helpers.Emulate_FP87_Result then
    run (← `(tactic| exact $(mkIdent `X86Proofs.emulateFP87Result_reads) _ _ _ _ _ _ _))
  else if head == ``X86.Helpers.Emulate_FP87_Add then
    run (← `(tactic| exact $(mkIdent `X86Proofs.emulateFP87Add_reads) _ _ _))
  else if head == ``X86.Helpers.Emulate_FMUL then
    run (← `(tactic| exact $(mkIdent `X86Proofs.emulateFMUL_reads) _ _))
  else if head == ``X86.Helpers.Emulate_FDIV then
    run (← `(tactic| exact $(mkIdent `X86Proofs.emulateFDIV_reads) _ _))
  else if head == ``X86.Helpers.Emulate_FSQRT then
    run (← `(tactic| exact $(mkIdent `X86Proofs.emulateFSQRT_reads) _))
  else if (← isMatcherApp m) then run (← `(tactic| split))
  else if head != .anonymous then run (← `(tactic| unfold $(mkIdent head):ident))
  else if m.getAppFn.isProj then
    run (← `(tactic|
      dsimp only [X86.Runtime.instCheckedSliceInt, X86.Runtime.instCheckedSliceBitVec]))
  else throwError "reads_fcw: cannot step {m}"

/-- Prove `ReadsFcw m` for a lean-x86 x87 float helper `m`. -/
macro "reads_fcw" : tactic => `(tactic| repeat' reads_fcw_step)

theorem emulateFP87Result_reads (magnitude denominator exponent leading : Int) (sign : Bits 1)
    (precision : Int) (rc : Bits 2) :
    ReadsFcw (Emulate_FP87_Result magnitude denominator exponent leading sign precision rc :
      SpecM X86.Exception RamState _) := by
  unfold Emulate_FP87_Result
  reads_fcw

theorem emulateFP87Add_reads (x y : BitVec 80) (sub : Bool) :
    ReadsFcw (Emulate_FP87_Add x y sub : SpecM X86.Exception RamState _) := by
  unfold Emulate_FP87_Add
  reads_fcw

theorem emulateFMUL_reads (x y : BitVec 80) :
    ReadsFcw (Emulate_FMUL x y : SpecM X86.Exception RamState _) := by
  unfold Emulate_FMUL
  reads_fcw

theorem emulateFDIV_reads (x y : BitVec 80) :
    ReadsFcw (Emulate_FDIV x y : SpecM X86.Exception RamState _) := by
  unfold Emulate_FDIV
  reads_fcw

theorem emulateFSQRT_reads (x : BitVec 80) :
    ReadsFcw (Emulate_FSQRT x : SpecM X86.Exception RamState _) := by
  unfold Emulate_FSQRT
  reads_fcw

theorem fp87Add_reads (x y : BitVec 80) :
    ReadsFcw (FP87.Add x y false : SpecM X86.Exception RamState _) := by
  reads_fcw

theorem fp87Subtract_reads (x y : BitVec 80) :
    ReadsFcw (FP87.Subtract x y false false : SpecM X86.Exception RamState _) := by
  reads_fcw

theorem fp87Multiply_reads (x y : BitVec 80) :
    ReadsFcw (FP87.Multiply x y false : SpecM X86.Exception RamState _) := by
  reads_fcw

theorem fp87Divide_reads (x y : BitVec 80) :
    ReadsFcw (FP87.Divide x y false false : SpecM X86.Exception RamState _) := by
  reads_fcw

theorem fp87Sqrt_reads (x : BitVec 80) :
    ReadsFcw (FP87.Sqrt x : SpecM X86.Exception RamState _) := by
  reads_fcw

/-! ### The lanes -/

/-- The four x87 arithmetic operations. -/
inductive X87Op where
  | add
  | sub
  | mul
  | div
  deriving DecidableEq

/-- lean-x86's helper for `op` (`FP87.Add`, `FP87.Subtract`, `FP87.Multiply`, `FP87.Divide`), as
the arithmetic forms call it: `x op y` (no operand known denormal). -/
def x87OpM (op : X87Op) (x y : BitVec 80) :
    SpecM X86.Exception RamState (BitVec 80 × Bool × BitVec 6) :=
  match op with
  | .add => FP87.Add x y false
  | .sub => FP87.Subtract x y false false
  | .mul => FP87.Multiply x y false
  | .div => FP87.Divide x y false false

theorem x87OpM_reads (op : X87Op) (x y : BitVec 80) : ReadsFcw (x87OpM op x y) := by
  cases op
  · exact fp87Add_reads x y
  · exact fp87Subtract_reads x y
  · exact fp87Multiply_reads x y
  · exact fp87Divide_reads x y

/-- `x op y` at FCW `fcw`: the result, whether its magnitude was rounded up, the exception flags. -/
def x87Arith (op : X87Op) (fcw : BitVec 16) (x y : BitVec 80) : BitVec 80 × Bool × BitVec 6 :=
  laneVal (fcwRun (x87OpM op x y) fcw)

/-- lean-x86 returns a value for `x op y` at FCW `fcw`. -/
def X87ArithOk (op : X87Op) (fcw : BitVec 16) (x y : BitVec 80) : Prop :=
  LaneOk (fcwRun (x87OpM op x y) fcw)

theorem x87OpM_run (op : X87Op) (x y : BitVec 80) (s : RamState)
    (hm : FcwMasked s.FP87_Control) (hok : X87ArithOk op s.FP87_Control x y) :
    (x87OpM op x y).run s = (.ok (x87Arith op s.FP87_Control x y), s) := by
  rw [(x87OpM_reads op x y).run_eq s hm]
  exact congrArg (fun r => (r, s)) hok.eq

/-- The square root of `x` at FCW `fcw`: the result, whether it was rounded up, the flags. -/
def x87Sqrt (fcw : BitVec 16) (x : BitVec 80) : BitVec 80 × Bool × BitVec 6 :=
  laneVal (fcwRun (FP87.Sqrt x) fcw)

/-- lean-x86 returns a value for the square root of `x` at FCW `fcw`. -/
def X87SqrtOk (fcw : BitVec 16) (x : BitVec 80) : Prop := LaneOk (fcwRun (FP87.Sqrt x) fcw)

theorem fp87Sqrt_run (x : BitVec 80) (s : RamState) (hm : FcwMasked s.FP87_Control)
    (hok : X87SqrtOk s.FP87_Control x) :
    (FP87.Sqrt x : SpecM X86.Exception RamState _).run s = (.ok (x87Sqrt s.FP87_Control x), s) := by
  rw [(fp87Sqrt_reads x).run_eq s hm]
  exact congrArg (fun r => (r, s)) hok.eq

/-- `x` rounded to an integer with rounding control `rc` (`FP87.Round_To_Integer`): the result,
whether it was rounded up, the flags. -/
def x87Rndint (rc : BitVec 2) (x : BitVec 80) : BitVec 80 × Bool × BitVec 6 :=
  match FP87.Round_To_Integer x rc with
  | .ok v => v
  | .error _ => default

/-- lean-x86 returns a value for `x` rounded with rounding control `rc`. -/
def X87RndintOk (rc : BitVec 2) (x : BitVec 80) : Prop := ∃ v, FP87.Round_To_Integer x rc = .ok v

theorem X87RndintOk.eq {rc : BitVec 2} {x : BitVec 80} (h : X87RndintOk rc x) :
    FP87.Round_To_Integer x rc = .ok (x87Rndint rc x) := by
  obtain ⟨v, hv⟩ := h
  simp only [x87Rndint, hv]

/-! ### Status words -/

/-- The status word an arithmetic operation (`Operations.FADD`, …) returns from status word `fsw`
and oracle `o`: C0, C2, C3 the oracle's next three bits, the exception flags := `ex`, C1 := whether
the result was rounded up (`up`), as lean-x86 sets them. -/
def x87OpStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up : Bool) (ex : BitVec 6) :
    BitVec 16 :=
  setSlice (setSlice (setSlice (setSlice (setSlice (setSlice fsw 8 1
    (BitVec.ofBool (oracleBit o))) 9 1 0) 10 1 (BitVec.ofBool (oracleBit (oracleSkip o 1)))) 14 1
    (BitVec.ofBool (oracleBit (oracleSkip (oracleSkip o 1) 1)))) 0 6 ex) 9 1
    (if up = true then 1 else 0)

/-- The status word an arithmetic form leaves: from the current status word `cur` (after a pop, if
any) and the operation's `x87OpStatus fsw o up ex`, SF and the flags `ex` ORed in, C1 := `up`, C0,
C2, C3 the oracle's next three bits after `o`'s first three, as lean-x86 sets them. -/
def x87ArithFsw (cur fsw : BitVec 16) (o : X86.Runtime.Oracle) (up : Bool) (ex : BitVec 6) :
    BitVec 16 :=
  let st := x87OpStatus fsw o up ex
  let o' := oracleSkip (oracleSkip (oracleSkip o 1) 1) 1
  setSlice (setSlice (setSlice (setSlice
    (fswOrFlags (setSlice cur 6 1 (st.extractLsb' 6 1)) (st.extractLsb' 0 6))
    8 1 (BitVec.ofBool (oracleBit o'))) 9 1 (st.extractLsb' 9 1)) 10 1
    (BitVec.ofBool (oracleBit (oracleSkip o' 1)))) 14 1
    (BitVec.ofBool (oracleBit (oracleSkip (oracleSkip o' 1) 1)))

/-- C1 (`up`) as condition codes: bit 1. -/
def ccC1 (up : Bool) : BitVec 4 := if up = true then 2 else 0

theorem x87ArithFsw_eq (cur fsw : BitVec 16) (o : X86.Runtime.Oracle) (up : Bool)
    (ex : BitVec 6) :
    x87ArithFsw cur fsw o up ex = fswSetC (fswOrFlags (setSlice cur 6 1 (fsw.extractLsb' 6 1)) ex)
      (oBit o 3) (if up = true then 1 else 0) (oBit o 4) (oBit o 5) := by
  simp only [x87ArithFsw, x87OpStatus, oBit, oracleSkip_oracleSkip]
  fsw_bits
  all_goals cases up <;> simp [getElem_setSlice]

@[simp] theorem fswTop_x87OpStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up : Bool)
    (ex : BitVec 6) : fswTop (x87OpStatus fsw o up ex) = fswTop fsw := by
  simp (disch := omega) only [x87OpStatus, fswTop_setSlice]

@[simp] theorem fswES_x87OpStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up : Bool)
    (ex : BitVec 6) : fswES (x87OpStatus fsw o up ex) = fswES fsw := by
  simp (disch := omega) only [x87OpStatus, fswES_setSlice]

@[simp] theorem fswTop_x87ArithFsw (cur fsw : BitVec 16) (o : X86.Runtime.Oracle) (up : Bool)
    (ex : BitVec 6) : fswTop (x87ArithFsw cur fsw o up ex) = fswTop cur := by
  rw [x87ArithFsw_eq]
  simp (disch := omega) only [fswTop_fswSetC, fswTop_fswOrFlags, fswTop_setSlice]

@[simp] theorem fswES_x87ArithFsw (cur fsw : BitVec 16) (o : X86.Runtime.Oracle) (up : Bool)
    (ex : BitVec 6) : fswES (x87ArithFsw cur fsw o up ex) = fswES cur := by
  rw [x87ArithFsw_eq]
  simp (disch := omega) only [fswES_fswSetC, fswES_fswOrFlags, fswES_setSlice]

theorem fswRest_x87ArithFsw (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up : Bool)
    (ex : BitVec 6) : fswRest (x87ArithFsw fsw fsw o up ex) = fswOrFlags (fswRest fsw) ex := by
  rw [x87ArithFsw_eq]
  fsw_bits

theorem fswRest_x87ArithFsw_top (fsw : BitVec 16) (top : BitVec 3) (o : X86.Runtime.Oracle)
    (up : Bool) (ex : BitVec 6) :
    fswRest (x87ArithFsw (fswSetTop fsw top) fsw o up ex) =
      fswSetTop (fswOrFlags (fswRest fsw) ex) top := by
  rw [x87ArithFsw_eq]
  fsw_bits

theorem fswCC_x87ArithFsw (cur fsw : BitVec 16) (o : X86.Runtime.Oracle) (up : Bool)
    (ex : BitVec 6) : fswCC (x87ArithFsw cur fsw o up ex) &&& 2 = ccC1 up := by
  rw [x87ArithFsw_eq, fswCC_fswSetC]
  generalize oBit o 3 = a
  generalize oBit o 4 = b
  generalize oBit o 5 = c
  revert a b c
  cases up <;> decide

/-! ### Comparisons -/

/-- lean-x86's comparison of `x` with `y` (`FP87.Compare`, ordered or unordered: whether a quiet
NaN raises the invalid exception): the result `C3 C2 C0` as one 3-bit value (bit 0 = C0 = less,
bit 1 = C2 = unordered, bit 2 = C3 = equal) and the exception flags. -/
def x87Compare (ordered : Bool) (x y : BitVec 80) : BitVec 3 × BitVec 6 :=
  match FP87.Compare x y ordered false with
  | .ok v => v
  | .error _ => default

/-- lean-x86 returns a value for the comparison of `x` with `y`. -/
def X87CompareOk (ordered : Bool) (x y : BitVec 80) : Prop :=
  ∃ v, FP87.Compare x y ordered false = .ok v

theorem X87CompareOk.eq {ordered : Bool} {x y : BitVec 80} (h : X87CompareOk ordered x y) :
    FP87.Compare x y ordered false = .ok (x87Compare ordered x y) := by
  obtain ⟨v, hv⟩ := h
  simp only [x87Compare, hv]

/-- A comparison result `C3 C2 C0` as condition codes (`C3 C2 C1 C0`, C1 = 0). -/
def x87CmpCC (c : BitVec 3) : BitVec 4 :=
  c.extractLsb' 2 1 ++ c.extractLsb' 1 1 ++ 0#1 ++ c.extractLsb' 0 1

/-- The status word a comparison (FCOM, FUCOM, FTST) leaves: C0, C2, C3 := the result `c`, C1 := 0,
the flags `ex` ORed in, as lean-x86 sets them. -/
def x87CmpFsw (fsw : BitVec 16) (c : BitVec 3) (ex : BitVec 6) : BitVec 16 :=
  fswOrFlags (setSlice (setSlice (setSlice (setSlice fsw 8 1 (c.extractLsb' 0 1)) 9 1 0) 10 1
    (c.extractLsb' 1 1)) 14 1 (c.extractLsb' 2 1)) ex

theorem x87CmpFsw_eq (fsw : BitVec 16) (c : BitVec 3) (ex : BitVec 6) :
    x87CmpFsw fsw c ex = fswSetC (fswOrFlags fsw ex) (c.extractLsb' 0 1) 0 (c.extractLsb' 1 1)
      (c.extractLsb' 2 1) := by
  unfold x87CmpFsw
  fsw_bits

@[simp] theorem fswTop_x87CmpFsw (fsw : BitVec 16) (c : BitVec 3) (ex : BitVec 6) :
    fswTop (x87CmpFsw fsw c ex) = fswTop fsw := by
  simp [x87CmpFsw_eq]

@[simp] theorem fswES_x87CmpFsw (fsw : BitVec 16) (c : BitVec 3) (ex : BitVec 6) :
    fswES (x87CmpFsw fsw c ex) = fswES fsw := by
  simp [x87CmpFsw_eq]

theorem fswRest_x87CmpFsw (fsw : BitVec 16) (c : BitVec 3) (ex : BitVec 6) :
    fswRest (x87CmpFsw fsw c ex) = fswOrFlags (fswRest fsw) ex := by
  rw [x87CmpFsw_eq]
  fsw_bits

theorem fswCC_x87CmpFsw (fsw : BitVec 16) (c : BitVec 3) (ex : BitVec 6) :
    fswCC (x87CmpFsw fsw c ex) = x87CmpCC c := by
  rw [x87CmpFsw_eq, fswCC_fswSetC]
  rfl

/-- The status word FCOMI leaves: C1 := 0, the flags `ex` ORed in. -/
def x87ComiFsw (fsw : BitVec 16) (ex : BitVec 6) : BitVec 16 := fswOrFlags (setSlice fsw 9 1 0) ex

@[simp] theorem fswTop_x87ComiFsw (fsw : BitVec 16) (ex : BitVec 6) :
    fswTop (x87ComiFsw fsw ex) = fswTop fsw := by
  simp (disch := omega) only [x87ComiFsw, fswTop_fswOrFlags, fswTop_setSlice]

@[simp] theorem fswES_x87ComiFsw (fsw : BitVec 16) (ex : BitVec 6) :
    fswES (x87ComiFsw fsw ex) = fswES fsw := by
  simp (disch := omega) only [x87ComiFsw, fswES_fswOrFlags, fswES_setSlice]

theorem fswRest_x87ComiFsw (fsw : BitVec 16) (ex : BitVec 6) :
    fswRest (x87ComiFsw fsw ex) = fswOrFlags (fswRest fsw) ex := by
  unfold x87ComiFsw
  fsw_bits

theorem fswCC_x87ComiFsw (fsw : BitVec 16) (ex : BitVec 6) :
    fswCC (x87ComiFsw fsw ex) &&& 2 = 0 := by
  unfold x87ComiFsw
  rw [fswCC_fswOrFlags]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [fswCC, BitVec.getLsbD_and, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases lt4_cases hi with rfl | rfl | rfl | rfl <;> simp [getElem_setSlice]

/-! ### FXTRACT -/

/-- lean-x86's `FP87.Extract x` (a `PartialResult`: `FP87.Normalize` normalizes a denormal with a
loop lean-x86 does not show terminates). -/
def x87ExtractRun (x : BitVec 80) : Option
    (Except (Error Empty) (BitVec 80 × BitVec 80 × BitVec 6)) :=
  (FP87.Extract x).run

/-- The significand and the exponent of `x` (as 80-bit values) and the exception flags, as
lean-x86's `FP87.Extract` computes them. -/
def x87Extract (x : BitVec 80) : BitVec 80 × BitVec 80 × BitVec 6 :=
  match x87ExtractRun x with
  | some (.ok v) => v
  | _ => default

/-- lean-x86's `FP87.Extract` terminates and returns a value on `x`. -/
def X87ExtractOk (x : BitVec 80) : Prop := ∃ v, x87ExtractRun x = some (.ok v)

theorem fp87Extract_eq {x : BitVec 80} (hok : X87ExtractOk x) :
    FP87.Extract x = pure (x87Extract x) := by
  obtain ⟨v, hv⟩ := hok
  unfold x87Extract
  rw [hv]
  exact hv

/-- The status word `Operations.FXTRACT` returns from `fsw` and oracle `o`: C0, C2, C3 the oracle's
next three bits, C1 := 0, the exception flags := `ex`, as lean-x86 sets them. -/
def x87ExtractStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) (ex : BitVec 6) : BitVec 16 :=
  setSlice (setSlice (setSlice (setSlice (setSlice fsw 8 1
    (BitVec.ofBool (oracleBit o))) 9 1 0) 10 1 (BitVec.ofBool (oracleBit (oracleSkip o 1)))) 14 1
    (BitVec.ofBool (oracleBit (oracleSkip (oracleSkip o 1) 1)))) 0 6 ex

/-- The status word FXTRACT leaves: from the current status word `cur` (after the push) and the
operation's `x87ExtractStatus fsw o ex`, the flags `ex` ORed in, C1 := 0, C0, C2, C3 the oracle's
next three bits after `o`'s first three, as lean-x86 sets them. -/
def x87ExtractFsw (cur fsw : BitVec 16) (o : X86.Runtime.Oracle) (ex : BitVec 6) : BitVec 16 :=
  let st := x87ExtractStatus fsw o ex
  let o' := oracleSkip (oracleSkip (oracleSkip o 1) 1) 1
  setSlice (setSlice (setSlice (setSlice
    (fswOrFlags (setSlice cur 6 1 (st.extractLsb' 6 1)) (st.extractLsb' 0 6))
    8 1 (BitVec.ofBool (oracleBit o'))) 9 1 (st.extractLsb' 9 1)) 10 1
    (BitVec.ofBool (oracleBit (oracleSkip o' 1)))) 14 1
    (BitVec.ofBool (oracleBit (oracleSkip (oracleSkip o' 1) 1)))

theorem x87ExtractFsw_eq (cur fsw : BitVec 16) (o : X86.Runtime.Oracle) (ex : BitVec 6) :
    x87ExtractFsw cur fsw o ex = fswSetC (fswOrFlags (setSlice cur 6 1 (fsw.extractLsb' 6 1)) ex)
      (oBit o 3) 0 (oBit o 4) (oBit o 5) := by
  simp only [x87ExtractFsw, x87ExtractStatus, oBit, oracleSkip_oracleSkip]
  fsw_bits
  all_goals simp [getElem_setSlice]

@[simp] theorem fswTop_x87ExtractStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle)
    (ex : BitVec 6) : fswTop (x87ExtractStatus fsw o ex) = fswTop fsw := by
  simp (disch := omega) only [x87ExtractStatus, fswTop_setSlice]

@[simp] theorem fswTop_x87ExtractFsw (cur fsw : BitVec 16) (o : X86.Runtime.Oracle)
    (ex : BitVec 6) : fswTop (x87ExtractFsw cur fsw o ex) = fswTop cur := by
  rw [x87ExtractFsw_eq]
  simp (disch := omega) only [fswTop_fswSetC, fswTop_fswOrFlags, fswTop_setSlice]

@[simp] theorem fswES_x87ExtractFsw (cur fsw : BitVec 16) (o : X86.Runtime.Oracle)
    (ex : BitVec 6) : fswES (x87ExtractFsw cur fsw o ex) = fswES cur := by
  rw [x87ExtractFsw_eq]
  simp (disch := omega) only [fswES_fswSetC, fswES_fswOrFlags, fswES_setSlice]

theorem fswRest_x87ExtractFsw_top (fsw : BitVec 16) (top : BitVec 3) (o : X86.Runtime.Oracle)
    (ex : BitVec 6) :
    fswRest (x87ExtractFsw (fswSetTop fsw top) fsw o ex) =
      fswSetTop (fswOrFlags (fswRest fsw) ex) top := by
  rw [x87ExtractFsw_eq]
  fsw_bits

theorem fswCC_x87ExtractFsw (cur fsw : BitVec 16) (o : X86.Runtime.Oracle) (ex : BitVec 6) :
    fswCC (x87ExtractFsw cur fsw o ex) &&& 2 = 0 := by
  rw [x87ExtractFsw_eq, fswCC_fswSetC]
  generalize oBit o 3 = a
  generalize oBit o 4 = b
  generalize oBit o 5 = c
  revert a b c
  decide

end X86Proofs
