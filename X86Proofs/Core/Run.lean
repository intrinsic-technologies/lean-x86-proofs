import X86
import Lean
import X86Proofs.Core.Runtime

/-!
# Running lean-x86's spec monads

Rewriting lemmas for `SpecM` (total) and `PartialSpecM` (possibly divergent) programs, and the
`spec_run` tactic that steps through a do-block, using a supplied lemma for each semantic call
and `rfl` for plumbing. `pspec_run` is its
`PartialSpecM` counterpart (forms that may diverge), with `partialResult_lift_run` for a partial
operation. `stdLog2_pow` (and `stdLog2_two`, `stdLog2_four`, `stdLog2_eight`) evaluates
`Std.Integer.Log2`, the partial helper behind those operations.
-/

namespace X86Proofs

open X86

theorem specM_bind_run {exception σ α β : Type} (a : X86.Runtime.SpecM exception σ α)
    (b : α → X86.Runtime.SpecM exception σ β) {s t : σ} {value : α}
    (h : a.run s = (.ok value, t)) :
    (a >>= b).run s = (b value).run t := by
  simp only [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind, ExceptT.bindCont] at *
  rw [h]

@[simp] theorem specM_pure_run {exception σ α : Type} (value : α) (s : σ) :
    (pure value : X86.Runtime.SpecM exception σ α).run s = (.ok value, s) := rfl

theorem specM_bind_pure_unit_run {exception σ : Type} (a : X86.Runtime.SpecM exception σ Unit) (s : σ) :
    (a >>= fun _ => pure ()).run s = a.run s := by
  simp only [bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.run, ExceptT.mk, StateT.bind,
    ExceptT.bindCont]
  cases h : a s with
  | mk result t =>
    cases result with
    | error e => rfl
    | ok v => cases v; rfl

theorem specM_forIn_run {exception σ α β : Type} (items : List α)
    (body : α → β → X86.Runtime.SpecM exception σ (ForInStep β)) (f : α → β → β)
    (s : σ) (initial : β)
    (h : ∀ item ∈ items, ∀ acc, (body item acc).run s = (.ok (.yield (f item acc)), s)) :
    (forIn items initial body).run s =
      (.ok (items.foldl (fun acc item => f item acc) initial), s) := by
  induction items generalizing initial with
  | nil => rfl
  | cons item items ih =>
    simp only [List.forIn_cons, List.foldl_cons]
    rw [specM_bind_run _ _ (h item (by simp) initial)]
    exact ih _ (by intro item' hi acc; exact h item' (by simp only [List.mem_cons, hi, or_true]) acc)

/-- A `for` loop whose body changes the state by `f item` at each item. -/
theorem specM_forIn_foldl_run {exception σ α : Type} (items : List α)
    (body : α → PUnit → X86.Runtime.SpecM exception σ (ForInStep PUnit))
    (f : α → σ → σ) (P : σ → Prop) (s : σ) (hs : P s)
    (h : ∀ item ∈ items, ∀ t, P t → (body item PUnit.unit).run t = (.ok (.yield PUnit.unit), f item t))
    (hp : ∀ item ∈ items, ∀ t, P t → P (f item t)) :
    (forIn items PUnit.unit body).run s = (.ok PUnit.unit, items.foldl (fun t item => f item t) s) := by
  induction items generalizing s with
  | nil => rfl
  | cons item items ih =>
    simp only [List.forIn_cons, List.foldl_cons]
    rw [specM_bind_run _ _ (h item (by simp) s hs)]
    exact ih _ (hp item (by simp) s hs)
      (by intro i hi t ht; exact h i (by simp only [List.mem_cons, hi, or_true]) t ht)
      (by intro i hi t ht; exact hp i (by simp only [List.mem_cons, hi, or_true]) t ht)

theorem partialSpecM_liftTotal_bind_run {exception σ α β : Type}
    (a : X86.Runtime.SpecM exception σ α) (b : α → X86.Runtime.PartialSpecM exception σ β)
    {s t : σ} {value : α} (h : a.run s = (.ok value, t)) :
    (X86.Runtime.liftTotal a >>= b).run s = (b value).run t := by
  simp only [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind,
    ExceptT.bindCont, X86.Runtime.liftTotal] at *
  rw [h]
  rfl

theorem partialSpecM_bind_run {exception σ α β : Type} (a : X86.Runtime.PartialSpecM exception σ α)
    (b : α → X86.Runtime.PartialSpecM exception σ β) {s t : σ} {value : α}
    (h : a.run s = some (.ok value, t)) :
    (a >>= b).run s = (b value).run t := by
  simp only [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind, ExceptT.bindCont] at *
  rw [h]
  rfl

@[simp] theorem partialSpecM_liftTotal_run {exception σ α : Type} (a : X86.Runtime.SpecM exception σ α)
    {s t : σ} {value : α} (h : a.run s = (.ok value, t)) :
    (X86.Runtime.liftTotal a).run s = some (.ok value, t) :=
  congrArg some h

@[simp] theorem partialSpecM_pure_run {exception σ α : Type} (value : α) (s : σ) :
    (pure value : X86.Runtime.PartialSpecM exception σ α).run s = some (.ok value, s) := rfl

/-- A total action lifted into `PartialSpecM`, then `pure ()`: the action's run (it cannot
diverge). -/
theorem partialSpecM_liftTotal_bind_pure_unit_run {exception σ : Type}
    (a : X86.Runtime.SpecM exception σ Unit) (s : σ) :
    (X86.Runtime.liftTotal a >>= fun _ => pure () :
      X86.Runtime.PartialSpecM exception σ Unit).run s = some (a.run s) := by
  simp only [bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.run, ExceptT.mk, StateT.bind,
    ExceptT.bindCont, X86.Runtime.liftTotal]
  cases h : a s with
  | mk result t =>
    cases result with
    | error e => rfl
    | ok v => cases v; rfl

/-- A `PartialSpecM` action, then `pure ()`: the action's run. -/
theorem partialSpecM_bind_pure_unit_run {exception σ : Type}
    (a : X86.Runtime.PartialSpecM exception σ Unit) (s : σ) :
    (a >>= fun _ => pure ()).run s = a.run s := by
  simp only [bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.run, ExceptT.mk, StateT.bind,
    ExceptT.bindCont]
  cases h : a s with
  | none => rfl
  | some r =>
    obtain ⟨result, t⟩ := r
    cases result with
    | error e => rfl
    | ok v => cases v; rfl

/-- A `try … catch` whose body returns normally returns as the body does (the handler does not
run). -/
theorem specM_tryCatch_run {exception σ α : Type} (a : X86.Runtime.SpecM exception σ α)
    (handler : X86.Runtime.Error exception → X86.Runtime.SpecM exception σ α)
    {s t : σ} {value : α} (h : a.run s = (.ok value, t)) :
    (tryCatch a handler).run s = (.ok value, t) := by
  simp only [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch,
    ExceptT.run, ExceptT.mk, Bind.bind, StateT.bind] at *
  rw [h]
  rfl

theorem partialSpecM_tryCatch_run {exception σ α : Type} (a : X86.Runtime.PartialSpecM exception σ α)
    (handler : X86.Runtime.Error exception → X86.Runtime.PartialSpecM exception σ α)
    {s t : σ} {value : α} (h : a.run s = some (.ok value, t)) :
    (tryCatch a handler).run s = some (.ok value, t) := by
  simp only [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch,
    ExceptT.run, ExceptT.mk, Bind.bind, StateT.bind] at *
  rw [h]
  rfl

@[simp] theorem partialSpecM_get_bind_run {exception σ α : Type}
    (k : σ → X86.Runtime.PartialSpecM exception σ α) (s : σ) :
    (get >>= k).run s = (k s).run s := rfl

@[simp] theorem partialSpecM_modify_bind_run {exception σ α : Type} (f : σ → σ)
    (k : Unit → X86.Runtime.PartialSpecM exception σ α) (s : σ) :
    (modify f >>= k).run s = (k ()).run (f s) := rfl

@[simp] theorem partialSpecM_liftTotal_modify_bind_run {exception σ α : Type} (f : σ → σ)
    (k : Unit → X86.Runtime.PartialSpecM exception σ α) (s : σ) :
    (X86.Runtime.liftTotal (modify f) >>= k).run s = (k ()).run (f s) := rfl

/-- A lean-x86 `while` loop in `PartialSpecM` (`for _ in PartialLoop.mk do …`) runs as
`PartialLoop.forIn`, which `partialSpecM_loop_done_run` and `partialSpecM_loop_yield_run` step. -/
theorem partialSpecM_forIn_eq {exception σ β : Type} (initial : β)
    (body : Unit → β → X86.Runtime.PartialSpecM exception σ (ForInStep β)) :
    (forIn X86.Runtime.PartialLoop.mk initial body : X86.Runtime.PartialSpecM exception σ β) =
      X86.Runtime.PartialLoop.forIn initial body := rfl

theorem partialSpecM_loop_done_run {exception σ β : Type} (initial final : β)
    (body : Unit → β → X86.Runtime.PartialSpecM exception σ (ForInStep β)) {s t : σ}
    (h : (body () initial).run s = some (.ok (.done final), t)) :
    (X86.Runtime.PartialLoop.forIn initial body).run s = some (.ok final, t) := by
  rw [X86.Runtime.PartialLoop.forIn]
  refine (partialSpecM_bind_run _ _ h).trans ?_
  rfl

theorem partialSpecM_loop_yield_run {exception σ β : Type} (initial middle final : β)
    (body : Unit → β → X86.Runtime.PartialSpecM exception σ (ForInStep β)) {s u t : σ}
    (h : (body () initial).run s = some (.ok (.yield middle), u))
    (hrest : (X86.Runtime.PartialLoop.forIn middle body).run u = some (.ok final, t)) :
    (X86.Runtime.PartialLoop.forIn initial body).run s = some (.ok final, t) := by
  rw [X86.Runtime.PartialLoop.forIn]
  exact (partialSpecM_bind_run _ _ h).trans hrest

/-- `liftNoSourceException` widens the error type of the action's result. -/
theorem liftNoSourceException_eq {exception σ α : Type} (action : X86.Runtime.SpecM Empty σ α) :
    X86.Runtime.liftNoSourceException (exception := exception) action =
      ExceptT.adapt X86.Runtime.Error.widen action := by
  unfold X86.Runtime.liftNoSourceException
  rfl

theorem specM_liftNoSourceException_run {exception σ α : Type}
    (action : X86.Runtime.SpecM Empty σ α) (s t : σ) (value : α)
    (h : action.run s = (.ok value, t)) :
    (X86.Runtime.liftNoSourceException (exception := exception) action).run s = (.ok value, t) := by
  unfold X86.Runtime.liftNoSourceException
  change ((action.run s).1.mapError X86.Runtime.Error.widen, (action.run s).2) = _
  rw [h]
  rfl

/-- Lifting a successful total computation into `SpecM` returns its value. -/
theorem liftM_ok {σ α : Type} (a : α) :
    (liftM (Except.ok a : Except (X86.Runtime.Error Empty) α) :
      X86.Runtime.SpecM X86.Exception (X86.State σ) α) = pure a := rfl

/-- A total computation (an `Except` that cannot raise an exception) that succeeds with `v`,
lifted into `SpecM`, returns `v` and leaves the state unchanged: how a lemma `op … = .ok v` about
a lean-x86 operation is used by `spec_run` (`liftM => liftM_run_of_ok (op_lemma …) _`). -/
theorem liftM_run_of_ok {σ α : Type} {a : Except (X86.Runtime.Error Empty) α} {v : α}
    (h : a = .ok v) (s : X86.State σ) :
    (liftM a : X86.Runtime.SpecM X86.Exception (X86.State σ) α).run s = (.ok v, s) := by
  subst h
  rfl

/-! ### `Std.Integer.Log2` -/

/-- lean-x86's halving loop (`while b > 1 do b := b / 2; r := r + 1`, run as a `PartialLoop`
with no state), from `2 ^ j`, ends after `j` passes at `(1, r + j)`. -/
theorem halving_loop {ε : Type}
    (body : Unit → Int × Int → X86.Runtime.PartialSpecM ε Unit (ForInStep (Int × Int)))
    (hy : ∀ b r : Int, b > 1 → (body () (b, r)).run () = some (.ok (.yield (b / 2, r + 1)), ()))
    (hd : ∀ b r : Int, ¬ b > 1 → (body () (b, r)).run () = some (.ok (.done (b, r)), ())) :
    ∀ (j : Nat) (r : Int), X86.Runtime.PartialLoop.forIn ((2 : Int) ^ j, r) body () =
      some (.ok (1, r + j), ()) := by
  intro j
  induction j with
  | zero =>
    intro r
    rw [Int.pow_zero, Int.natCast_zero, Int.add_zero]
    exact partialSpecM_loop_done_run _ _ _ (hd 1 r (by decide))
  | succ j ih =>
    intro r
    have h1 := Nat.one_le_two_pow (n := j)
    have hc : ((2 ^ j : Nat) : Int) = (2 : Int) ^ j := Int.natCast_pow 2 j
    have h2 : (2 : Int) ^ (j + 1) > 1 := by rw [Int.pow_succ]; omega
    refine partialSpecM_loop_yield_run _ _ _ _ (hy _ r h2) ?_
    rw [Int.pow_succ, Int.mul_ediv_cancel _ (by decide)]
    refine (ih (r + 1)).trans ?_
    rw [show r + 1 + (j : Int) = r + ((j + 1 : Nat) : Int) by omega]

/-- `X86.Helpers.Std.Integer.Log2 (2 ^ k)` (a `PartialResult`: its loop could diverge) returns `k`. -/
theorem stdLog2_pow (k : Nat) :
    X86.Helpers.Std.Integer.Log2 ((2 : Int) ^ k) = (pure (k : Int) : X86.Runtime.PartialResult Empty Int) := by
  have h1 := Nat.one_le_two_pow (n := k)
  have hc : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := Int.natCast_pow 2 k
  unfold X86.Helpers.Std.Integer.Log2
  rw [X86Proofs.assert_of_true (by simp only [decide_eq_true_eq]; omega), pure_bind,
    X86Proofs.assert_of_true (by rw [decide_eq_true_eq, ← hc, Int.toNat_natCast]; exact ⟨k, rfl⟩), pure_bind]
  simp only [forIn]
  rw [halving_loop _ ?hy ?hd k 0]
  · simp only [Int.zero_add]
    rfl
  case hy =>
    intro b r hb
    simp only [hb, decide_true, ↓reduceIte]
    rw [stdPositiveDivide_eq_pure (a := b) (by omega) (by decide), pure_bind]
    rfl
  case hd =>
    intro b r hb
    simp only [hb, decide_false, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- `X86.Helpers.Std.Integer.Log2 2 = 1` (two lanes, e.g. SHUFPD). -/
theorem stdLog2_two : X86.Helpers.Std.Integer.Log2 2 = (pure 1 : X86.Runtime.PartialResult Empty Int) := stdLog2_pow 1

/-- `X86.Helpers.Std.Integer.Log2 4 = 2` (four lanes, e.g. PSHUFD, SHUFPS). -/
theorem stdLog2_four : X86.Helpers.Std.Integer.Log2 4 = (pure 2 : X86.Runtime.PartialResult Empty Int) := stdLog2_pow 2

/-- `X86.Helpers.Std.Integer.Log2 8 = 3` (eight lanes, e.g. PINSRW, PEXTRW). -/
theorem stdLog2_eight : X86.Helpers.Std.Integer.Log2 8 = (pure 3 : X86.Runtime.PartialResult Empty Int) := stdLog2_pow 3

open Lean Meta Elab Tactic

/--
Step over the first bind of a `SpecM` run by `rfl`. `spec_bind_rfl` only steps over plumbing: it
fails on a bind whose action is a semantic lean-x86 call (`X86.Helpers.*` outside `Std`, or
`X86.Instructions.*`), which needs a lemma (`spec_bind_with`). `spec_bind_rfl!` skips that check
and steps over any bind, unfolding only `let`s to find it.
-/
def specBindRfl (any : Bool) : TacticM Unit := withMainContext do
  let target ← whnf (← instantiateMVars (← getMainTarget))
  let some (_, lhs, _) := target.eq? | throwError "expected equality: {target}"
  unless lhs.isAppOfArity ``ExceptT.run 5 do throwError "expected SpecM.run"
  let plumbing (e : Expr) : MetaM Bool := pure <|
    e.isLet || e.isMData || e.getAppFn.isLambda || e.isAppOf ``letFun || e.isAppOf ``ite ||
      e.isAppOf ``dite
  let action ← if any then zetaReduce lhs.getAppArgs[3]! else
    whnfHeadPred lhs.getAppArgs[3]! plumbing
  unless action.isAppOf ``bind || action.isAppOf ``Bind.bind do throwError "expected bind"
  unless any do
    let first := action.getAppArgs[action.getAppArgs.size - 2]!
    let head := (first.getAppFn.constName?.getD .anonymous)
    if (head.toString.startsWith "X86.Helpers" && !head.toString.startsWith "X86.Helpers.Std") ||
        head.toString.startsWith "X86.Instructions" then
      throwError "semantic call {head} requires a lemma"
  evalTactic (← `(tactic| refine (specM_bind_run _ _ rfl).trans ?_))

@[inherit_doc specBindRfl] elab "spec_bind_rfl" : tactic => specBindRfl false

@[inherit_doc specBindRfl] elab "spec_bind_rfl!" : tactic => specBindRfl true

/-- Step over the first bind of a `SpecM` run using the given lemma about the bound action. -/
macro "spec_bind_with " h:term : tactic =>
  `(tactic| refine (specM_bind_run _ _ $h).trans ?_)

/--
`spec_run [f => h, ...]` runs a `SpecM` do-block to its result: each bind whose action is headed
by `f` is rewritten with `h`; other binds are plumbing and are stepped by `rfl`. It stops, leaving
the goal, at a branch whose condition does not evaluate or at a result `rfl` cannot close.
-/
syntax "spec_run " "[" (ident " => " term),* "]" : tactic

elab_rules : tactic
  | `(tactic| spec_run [$[$keys:ident => $hints:term],*]) => focus do
    let keys ← keys.mapM resolveGlobalConstNoOverload
    for _ in [:100] do
      if (← getGoals).isEmpty then return
      let (head, bound) ← withMainContext do
        let target ← whnf (← instantiateMVars (← getMainTarget))
        let some (_, lhs, _) := target.eq? | throwError "expected equality: {target}"
        unless lhs.isAppOfArity ``ExceptT.run 5 do throwError "expected SpecM.run"
        let action ← whnfHeadPred lhs.getAppArgs[3]!
          (fun e => return e.isLet || e.isMData || e.getAppFn.isLambda || e.isAppOf ``letFun || e.isAppOf ``ite || e.isAppOf ``dite)
        let bound := action.isAppOf ``bind || action.isAppOf ``Bind.bind
        let first := if bound then action.getAppArgs[action.getAppArgs.size - 2]! else action
        return ((first.getAppFn.constName?.getD .anonymous), bound)
      -- A branch on a condition that does not evaluate: leave it to the caller.
      if head == ``Decidable.rec || head == ``Decidable.casesOn then return
      if let some i := keys.idxOf? head then
        if bound then evalTactic (← `(tactic| spec_bind_with $(hints[i]!)))
        else evalTactic (← `(tactic| exact $(hints[i]!)))
      else if bound then
        evalTactic (← `(tactic| spec_bind_rfl))
      else
        -- The result: close it by `rfl` if possible, else leave it to the caller.
        evalTactic (← `(tactic| first | rfl | exact specM_bind_pure_unit_run _ _ | skip))
        return
    throwError "too many primitive actions"

/--
`spec_run_until [f => h, ...]` is `spec_run` that stops, leaving the goal, at the first semantic
call (an `X86.Helpers` or `X86.Instructions` function) it has no hint for, instead of failing; the
caller then applies that call's lemma with side goals about the state reached so far.
-/
syntax "spec_run_until " "[" (ident " => " term),* "]" : tactic

elab_rules : tactic
  | `(tactic| spec_run_until [$[$keys:ident => $hints:term],*]) => focus do
    let keys ← keys.mapM resolveGlobalConstNoOverload
    for _ in [:100] do
      if (← getGoals).isEmpty then return
      let (head, bound) ← withMainContext do
        let target ← whnf (← instantiateMVars (← getMainTarget))
        let some (_, lhs, _) := target.eq? | throwError "expected equality: {target}"
        unless lhs.isAppOfArity ``ExceptT.run 5 do throwError "expected SpecM.run"
        let action ← whnfHeadPred lhs.getAppArgs[3]!
          (fun e => return e.isLet || e.isMData || e.getAppFn.isLambda || e.isAppOf ``letFun ||
            e.isAppOf ``ite || e.isAppOf ``dite)
        let bound := action.isAppOf ``bind || action.isAppOf ``Bind.bind
        let first := if bound then action.getAppArgs[action.getAppArgs.size - 2]! else action
        return ((first.getAppFn.constName?.getD .anonymous), bound)
      if head == ``Decidable.rec || head == ``Decidable.casesOn then return
      if let some i := keys.idxOf? head then
        if bound then evalTactic (← `(tactic| spec_bind_with $(hints[i]!)))
        else
          evalTactic (← `(tactic| exact $(hints[i]!)))
          return
      else
        if (head.toString.startsWith "X86.Helpers" && !head.toString.startsWith "X86.Helpers.Std")
            ||
            head.toString.startsWith "X86.Instructions" then
          return
        if bound then
          evalTactic (← `(tactic| spec_bind_rfl))
        else
          evalTactic (← `(tactic| first | rfl | exact specM_bind_pure_unit_run _ _ | skip))
          return
    throwError "too many primitive actions"

/-- `liftM_run_of_ok` in `PartialSpecM`: a total computation that succeeds with `v`, lifted into a
form that may diverge, returns `v` and leaves the state unchanged. -/
theorem partialSpecM_liftM_run_of_ok {σ α : Type} {a : Except (X86.Runtime.Error Empty) α} {v : α}
    (h : a = .ok v) (s : X86.State σ) :
    (liftM a : X86.Runtime.PartialSpecM X86.Exception (X86.State σ) α).run s = some (.ok v, s) := by
  subst h
  rfl

/-- A possibly divergent computation (`PartialResult`) that returns `v`, lifted into
`PartialSpecM`, returns `v` and leaves the state unchanged: how a lemma `op … = pure v` about a
partial lean-x86 operation (one that uses `Std.Integer.Log2`) is used by `pspec_run`. -/
theorem partialResult_lift_run {σ α : Type}
    {a : X86.Runtime.PartialResult Empty α} {v : α} (h : a = pure v) (s : X86.State σ) :
    (liftM a : X86.Runtime.PartialSpecM X86.Exception (X86.State σ) α).run s =
      some (.ok v, s) := by
  subst h
  rfl

/--
`spec_run` for a `PartialSpecM` run (a form that may diverge, e.g. PSHUFD): binds whose action is
`liftTotal a` use the hint for `a`'s head with `partialSpecM_liftTotal_bind_run` (a `SpecM` lemma
`a.run s = (.ok v, t)`), other keyed binds the hint itself with `partialSpecM_bind_run` (a
`PartialSpecM` lemma, e.g. `partialResult_lift_run`); plumbing binds are stepped by `rfl` (a
semantic call without a hint is an error, as in `spec_bind_rfl`). It stops at a branch whose
condition does not evaluate, and closes the last action with its hint or leaves it.
-/
syntax "pspec_run " "[" (ident " => " term),* "]" : tactic

elab_rules : tactic
  | `(tactic| pspec_run [$[$keys:ident => $hints:term],*]) => focus do
    let keys ← keys.mapM resolveGlobalConstNoOverload
    for _ in [:100] do
      if (← getGoals).isEmpty then return
      let (head, bound, lifted) ← withMainContext do
        let target ← whnf (← instantiateMVars (← getMainTarget))
        let some (_, lhs, _) := target.eq? | throwError "expected equality: {target}"
        unless lhs.isAppOfArity ``ExceptT.run 5 do throwError "expected PartialSpecM.run"
        let action ← whnfHeadPred lhs.getAppArgs[3]!
          (fun e => return e.isLet || e.isMData || e.getAppFn.isLambda || e.isAppOf ``letFun ||
            e.isAppOf ``ite || e.isAppOf ``dite)
        let bound := action.isAppOf ``bind || action.isAppOf ``Bind.bind
        let first := if bound then action.getAppArgs[action.getAppArgs.size - 2]! else action
        let lifted := first.isAppOf ``X86.Runtime.liftTotal
        let inner := if lifted then first.getAppArgs[first.getAppArgs.size - 1]! else
          if first.isAppOf ``MonadLift.monadLift || first.isAppOf ``MonadLiftT.monadLift ||
              first.isAppOf ``liftM then first.getAppArgs[first.getAppArgs.size - 1]! else first
        return ((inner.getAppFn.constName?.getD .anonymous), bound, lifted)
      if head == ``Decidable.rec || head == ``Decidable.casesOn then return
      if let some i := keys.idxOf? head then
        let h := hints[i]!
        if bound then
          if lifted then
            evalTactic (← `(tactic| refine (partialSpecM_liftTotal_bind_run _ _ $h).trans ?_))
          else evalTactic (← `(tactic| refine (partialSpecM_bind_run _ _ $h).trans ?_))
        else
          if lifted then evalTactic (← `(tactic| exact partialSpecM_liftTotal_run _ $h))
          else evalTactic (← `(tactic| exact $h))
          return
      else if bound then
        if (head.toString.startsWith "X86.Helpers" && !head.toString.startsWith "X86.Helpers.Std") ||
            head.toString.startsWith "X86.Instructions" then
          throwError "semantic call {head} requires a lemma"
        evalTactic (← `(tactic| refine (partialSpecM_bind_run _ _ rfl).trans ?_))
      else
        evalTactic (← `(tactic| first | rfl | skip))
        return
    throwError "too many primitive actions"

/--
`pspec_run_until [f => h, ...]` is `pspec_run` that stops, leaving the goal, at the first semantic
call it has no hint for, instead of failing (as `spec_run_until` for `SpecM`).
-/
syntax "pspec_run_until " "[" (ident " => " term),* "]" : tactic

elab_rules : tactic
  | `(tactic| pspec_run_until [$[$keys:ident => $hints:term],*]) => focus do
    let keys ← keys.mapM resolveGlobalConstNoOverload
    for _ in [:100] do
      if (← getGoals).isEmpty then return
      let (head, bound, lifted) ← withMainContext do
        let target ← whnf (← instantiateMVars (← getMainTarget))
        let some (_, lhs, _) := target.eq? | throwError "expected equality: {target}"
        unless lhs.isAppOfArity ``ExceptT.run 5 do throwError "expected PartialSpecM.run"
        let action ← whnfHeadPred lhs.getAppArgs[3]!
          (fun e => return e.isLet || e.isMData || e.getAppFn.isLambda || e.isAppOf ``letFun ||
            e.isAppOf ``ite || e.isAppOf ``dite)
        let bound := action.isAppOf ``bind || action.isAppOf ``Bind.bind
        let first := if bound then action.getAppArgs[action.getAppArgs.size - 2]! else action
        let lifted := first.isAppOf ``X86.Runtime.liftTotal
        let inner := if lifted then first.getAppArgs[first.getAppArgs.size - 1]! else
          if first.isAppOf ``MonadLift.monadLift || first.isAppOf ``MonadLiftT.monadLift ||
              first.isAppOf ``liftM then first.getAppArgs[first.getAppArgs.size - 1]! else first
        return ((inner.getAppFn.constName?.getD .anonymous), bound, lifted)
      if head == ``Decidable.rec || head == ``Decidable.casesOn then return
      if let some i := keys.idxOf? head then
        let h := hints[i]!
        if bound then
          if lifted then
            evalTactic (← `(tactic| refine (partialSpecM_liftTotal_bind_run _ _ $h).trans ?_))
          else evalTactic (← `(tactic| refine (partialSpecM_bind_run _ _ $h).trans ?_))
        else
          if lifted then evalTactic (← `(tactic| exact partialSpecM_liftTotal_run _ $h))
          else evalTactic (← `(tactic| exact $h))
          return
      else
        if (head.toString.startsWith "X86.Helpers" && !head.toString.startsWith "X86.Helpers.Std")
            ||
            head.toString.startsWith "X86.Instructions" then
          return
        if bound then
          evalTactic (← `(tactic| refine (partialSpecM_bind_run _ _ rfl).trans ?_))
        else
          evalTactic (← `(tactic| first | rfl | skip))
          return
    throwError "too many primitive actions"

/--
`finite_cases x` splits a goal over `x : Fin n`, for a literal `n`, into one goal per value of `x`.
It is a small stand-in for Mathlib's `fin_cases`, which is not available here (this library does
not import Mathlib). Unlike `fin_cases`, it works only on a local `x` whose type is literally
`Fin n` (no `x ∈ s` hypotheses, no other finite types); it reverts `x` and splits with
`Fin.forall_fin_succ`, so in the resulting goals the value appears as `0`, `Fin.succ 0`, … rather
than as a numeral, and nothing is simplified afterwards.
-/
elab "finite_cases " x:ident : tactic => do
  let e ← getFVarId x
  let type ← withMainContext <| inferType (mkFVar e)
  let_expr Fin bound := type | throwError "expected Fin"
  let some n ← getNatValue? bound | throwError "expected literal bound"
  evalTactic (← `(tactic| revert $x))
  let mut leaves := []
  for k in [:n] do
    let pred := quote (n - k - 1)
    evalTactic (← `(tactic| refine (Fin.forall_fin_succ (n := $pred)).mpr ⟨?_, ?_⟩))
    let [head, tail] ← getGoals | throwError "unexpected goals"
    leaves := leaves ++ [head]
    setGoals [tail]
  evalTactic (← `(tactic| intro i; exact Fin.elim0 i))
  setGoals leaves

end X86Proofs
