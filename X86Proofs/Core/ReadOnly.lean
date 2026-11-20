import X86Proofs.Core.Run
import X86.Machine.Step
import Prelude

/-!
# Read-only lean-x86 actions

`ReadOnly R a`: running `a` leaves the state unchanged, and its result is the same on any two
`R`-related states. `read_only_step` proves it for an action by walking its code (and
`keeps_state`, `Core/Float.lean`, for no relation: the state is left alone, the result may depend
on anything).

lean-x86 reads CPUID features and memory types through such actions (`Read_CPUID_Feature`,
`Get_Memory_Type`), which are read-only for `SameControls` (same XCR0, CR0, CR4, PAT, MTRRs, SMRR
and SMM state). `Prelude` states facts about their results only; from those, `readCPUIDFeature_run`
gives the state equation the step proofs need, and `reportsCPUFeature_of_sameControls`,
`smrrUnblocked_of_sameControls` and `writeBackMemoryType_of_sameControls` carry `Prelude`'s facts
to every state with the same controls, such as the states a step passes through.
-/

namespace X86Proofs

open X86 X86.Helpers X86.Machine

/-- Running `a` does not change the state, and gives the same result on `R`-related states. -/
def ReadOnly {ε σ α : Type} (R : σ → σ → Prop) (a : X86.Runtime.SpecM ε σ α) : Prop :=
  ∀ s, (a.run s).2 = s ∧ ∀ t, R s t → (a.run t).1 = (a.run s).1

namespace ReadOnly

variable {ε σ α β : Type} {R : σ → σ → Prop}

theorem run_eq {a : X86.Runtime.SpecM ε σ α} (h : ReadOnly R a) (s : σ) :
    a.run s = ((a.run s).1, s) := by
  exact Prod.ext rfl (h s).1

/-- The state equation for a stable action from a fact about its result. -/
theorem run_of_result {a : X86.Runtime.SpecM ε σ α} (h : ReadOnly R a) {s : σ}
    {r : Except (X86.Runtime.Error ε) α} (hr : (a.run s).1 = r) : a.run s = (r, s) := by
  rw [h.run_eq s, hr]

/-- The state equation on an `R`-related state. -/
theorem run_of_related {a : X86.Runtime.SpecM ε σ α} (h : ReadOnly R a) {s t : σ} (hst : R s t)
    {r : Except (X86.Runtime.Error ε) α} (hr : (a.run s).1 = r) : a.run t = (r, t) := by
  rw [h.run_eq t, (h s).2 t hst, hr]

theorem pure (x : α) : ReadOnly R (Pure.pure x : X86.Runtime.SpecM ε σ α) :=
  fun _ => ⟨rfl, fun _ _ => rfl⟩

theorem throw (e : X86.Runtime.Error ε) :
    ReadOnly R (MonadExceptOf.throw e : X86.Runtime.SpecM ε σ α) :=
  fun _ => ⟨rfl, fun _ _ => rfl⟩

theorem lift (e : Except (X86.Runtime.Error ε) α) :
    ReadOnly R (liftM e : X86.Runtime.SpecM ε σ α) :=
  fun _ => ⟨rfl, fun _ _ => rfl⟩

theorem bind {a : X86.Runtime.SpecM ε σ α} {b : α → X86.Runtime.SpecM ε σ β}
    (ha : ReadOnly R a) (hb : ∀ x, ReadOnly R (b x)) : ReadOnly R (a >>= b) := by
  intro s
  have key : ∀ u, (a >>= b).run u = match (a.run u).1 with
      | .ok x => (b x).run u
      | .error e => (.error e, u) := by
    intro u
    have hu := ha.run_eq u
    simp only [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind,
      ExceptT.bindCont] at hu ⊢
    rw [hu]
    generalize (a u).1 = r
    cases r <;> rfl
  have es := key s
  have et := key
  refine ⟨?_, fun t hst => ?_⟩
  · rw [es]
    split
    · exact (hb _ s).1
    · rfl
  · rw [es, et, (ha s).2 t hst]
    split
    · exact (hb _ s).2 t hst
    · rfl

/-- `get >>= k` is stable if `k` reads only what `R` preserves. -/
theorem get_bind {k : σ → X86.Runtime.SpecM ε σ β}
    (hk : ∀ s t, R s t → k t = k s) (h : ∀ st, ReadOnly R (k st)) :
    ReadOnly R ((MonadStateOf.get : X86.Runtime.SpecM ε σ σ) >>= k) := by
  intro s
  have e : ∀ u, ((MonadStateOf.get : X86.Runtime.SpecM ε σ σ) >>= k).run u = (k u).run u :=
    fun _ => rfl
  refine ⟨by rw [e]; exact (h s s).1, fun t hst => ?_⟩
  rw [e, e, hk s t hst]
  exact (h s s).2 t hst

theorem liftNoSourceException {exception : Type} {a : X86.Runtime.SpecM Empty σ α}
    (h : ReadOnly R a) : ReadOnly R (X86.Runtime.liftNoSourceException (exception := exception) a) := by
  intro s
  have e : ∀ u, (X86.Runtime.liftNoSourceException (exception := exception) a).run u =
      ((a.run u).1.mapError X86.Runtime.Error.widen, (a.run u).2) := fun _ => rfl
  refine ⟨by rw [e]; exact (h s).1, fun t hst => ?_⟩
  rw [e, e, (h s).2 t hst]

theorem of_const {a : X86.Runtime.SpecM ε σ α} (r : Except (X86.Runtime.Error ε) α)
    (h : ∀ s, a.run s = (r, s)) : ReadOnly R a :=
  fun s => ⟨by rw [h], fun t _ => by rw [h, h]⟩

theorem assert (c : Bool) : ReadOnly R (X86.Runtime.assert c : X86.Runtime.SpecM ε σ Unit) := by
  cases c
  · exact fun _ => ⟨rfl, fun _ _ => rfl⟩
  · exact fun _ => ⟨rfl, fun _ _ => rfl⟩

theorem ite {c : Prop} [Decidable c] {a b : X86.Runtime.SpecM ε σ α}
    (ha : ReadOnly R a) (hb : ReadOnly R b) : ReadOnly R (if c then a else b) := by
  split
  · exact ha
  · exact hb

/-- A dependent branch is stable if both arms are. -/
theorem dite {c : Prop} [Decidable c] {a : c → X86.Runtime.SpecM ε σ α}
    {b : ¬ c → X86.Runtime.SpecM ε σ α} (ha : ∀ h, ReadOnly R (a h))
    (hb : ∀ h, ReadOnly R (b h)) : ReadOnly R (dite c a b) := by
  split
  · exact ha _
  · exact hb _

/-- Reading an initialized local (`readInitialized`) is stable. -/
theorem readInitialized (o : Option α) :
    ReadOnly R (X86.Runtime.readInitialized o : X86.Runtime.SpecM ε σ α) := by
  cases o <;> exact fun _ => ⟨rfl, fun _ _ => rfl⟩

end ReadOnly

/-- The registers lean-x86's CPUID feature reads and memory-type lookup depend on. -/
structure SameControls {σ : Type} (s t : X86.State σ) : Prop where
  xcr0 : t.XCR0 = s.XCR0
  cr0 : t.CR0 = s.CR0
  cr4 : t.CR4 = s.CR4
  pat : t.IA32_PAT = s.IA32_PAT
  mtrrDefType : t.IA32_MTRR_DEF_TYPE = s.IA32_MTRR_DEF_TYPE
  mtrrFixed : t.MTRR_Fixed = s.MTRR_Fixed
  mtrrBase : t.MTRR_Base = s.MTRR_Base
  mtrrMask : t.MTRR_Mask = s.MTRR_Mask
  smrrBase : t.IA32_SMRR_PHYSBASE = s.IA32_SMRR_PHYSBASE
  smrrMask : t.IA32_SMRR_PHYSMASK = s.IA32_SMRR_PHYSMASK
  smm : t.«SMM::In_SMM» = s.«SMM::In_SMM»

end X86Proofs

namespace X86Proofs

open X86 X86.Helpers X86.Machine

theorem getCPUIDValue_readOnly {σ : Type} (query : Cpuid.Query) (eax ecx : BitVec 32) :
    ReadOnly SameControls (@Get_CPUID_Value σ (Bindings.Cpuid.ofQuery query) eax ecx) := by
  unfold Get_CPUID_Value
  apply ReadOnly.get_bind
  · intro s t h
    simp only [Cpuid.queryAtState, h.xcr0, h.cr4]
  · intro st
    split
    · exact ReadOnly.pure _
    · exact ReadOnly.throw _

theorem getCacheDisabledMemoryType_call_of_sameControls [Bindings] {σ : Type} {s t : X86.State σ} (h : SameControls s t)
    (inputs : Memory_Type_Inputs) (address : BitVec 64) (pat : BitVec 3) :
    Get_Cache_Disabled_Memory_Type.Binding.call (σ := σ) inputs address pat t =
      Get_Cache_Disabled_Memory_Type.Binding.call inputs address pat s := by
  change Bindings.cacheControl.disabledMemoryType (Cpuid.queryAtState Bindings.processor.cpuid t)
      inputs address pat =
    Bindings.cacheControl.disabledMemoryType (Cpuid.queryAtState Bindings.processor.cpuid s)
      inputs address pat
  unfold Cpuid.queryAtState
  rw [h.xcr0, h.cr4]

open Lean Meta Elab Tactic in
/--
One step of a `ReadOnly SameControls a` proof, chosen by the head of `a`: a bind on `get` (the
continuation may read only the registers `SameControls` fixes), another bind, a branch, or a
leaf whose run is `rfl`-constant in the state.
-/
local elab "read_only_step" : tactic => withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  unless goal.isAppOf ``ReadOnly do throwError "expected ReadOnly goal"
  let a ← whnfCore goal.appArg!
  if a != goal.appArg! then
    let g ← mkAppM' goal.appFn! #[a]
    replaceMainGoal [← (← getMainGoal).replaceTargetDefEq g]
  let isBind := a.isAppOf ``Bind.bind || a.isAppOf ``bind
  if isBind then
    let first := a.getAppArgs[a.getAppNumArgs - 2]!
    let firstHead := first.getAppFn.constName?.getD .anonymous
    if firstHead == ``MonadStateOf.get || firstHead == ``get || firstHead == ``getThe ||
        firstHead == ``MonadState.get then
      evalTactic (← `(tactic| refine ReadOnly.get_bind (by
        intro _ _ h
        first
          | (simp only [getCacheDisabledMemoryType_call_of_sameControls h, h.xcr0, h.cr0, h.cr4, h.pat, h.mtrrDefType, h.mtrrFixed, h.mtrrBase,
              h.mtrrMask, h.smrrBase, h.smrrMask, h.smm]; done)
          | rfl) (fun _ => ?_)))
    else
      evalTactic (← `(tactic| refine ReadOnly.bind ?_ (fun _ => ?_)))
  else if a.isAppOf ``ite then
    evalTactic (← `(tactic| refine ReadOnly.ite ?_ ?_))
  else if ← isMatcherApp a then
    evalTactic (← `(tactic| split))
  else if a.isAppOf ``Get_CPUID_Value then
    evalTactic (← `(tactic| exact getCPUIDValue_readOnly _ _ _))
  else if a.isAppOf ``X86.Runtime.liftNoSourceException then
    evalTactic (← `(tactic| refine ReadOnly.liftNoSourceException ?_))
  else if a.isAppOf ``X86.Runtime.assert then
    evalTactic (← `(tactic| exact ReadOnly.assert _))
  else if a.isAppOf ``Pure.pure || a.isAppOf ``pure then
    evalTactic (← `(tactic| exact ReadOnly.pure _))
  else if a.isAppOf ``liftM then
    evalTactic (← `(tactic| exact ReadOnly.lift _))
  else if a.isAppOf ``MonadExceptOf.throw then
    evalTactic (← `(tactic| exact ReadOnly.throw _))
  else
    evalTactic (← `(tactic| exact ReadOnly.of_const _ (fun _ => rfl)))

theorem readCPUIDFeature_readOnly {σ : Type} (query : Cpuid.Query) (feature : CPUID_Feature) :
    ReadOnly SameControls (@Read_CPUID_Feature σ (Bindings.Cpuid.ofQuery query) feature) := by
  unfold Read_CPUID_Feature CPUID_Leaf_Available
  repeat' read_only_step

theorem getMemoryType_readOnly [Bindings] {σ : Type} (address : BitVec 64) (pat : BitVec 3) :
    ReadOnly SameControls (Get_Memory_Type (σ := σ) address pat) := by
  unfold Get_Memory_Type Emulate_Memory.Read_Type_Inputs Resolve_Memory_Type
    Get_Cache_Disabled_Memory_Type IA32_MTRRCAP CPUID_Leaf_Available
  repeat' read_only_step

/-- A CPUID feature `Prelude` says the processor reports is read without changing the state. -/
theorem readCPUIDFeature_run [X86.Machine.Bindings] {s : RamState} {feature : CPUID_Feature}
    {enabled : Bool} (h : Prelude.ReportsCPUFeature Bindings.processor s feature enabled) :
    (X86.Runtime.liftNoSourceException (exception := X86.Exception)
      (Read_CPUID_Feature feature)).run s = (.ok enabled, s) := by
  apply specM_liftNoSourceException_run
  apply (readCPUIDFeature_readOnly Bindings.processor.cpuid feature).run_of_result
  unfold Prelude.ReportsCPUFeature at h
  revert h
  cases ((Read_CPUID_Feature (σ := Ram) feature).run s).1 <;> simp [Except.toOption]

/-! `Prelude`'s CPUID, SMRR and memory-type facts depend only on the registers `SameControls`
fixes, so they carry over to every state the fetch passes through. -/

theorem reportsCPUFeature_of_sameControls [X86.Machine.Bindings] {s t : RamState} (hst : SameControls s t)
    {feature : CPUID_Feature} {enabled : Bool}
    (h : Prelude.ReportsCPUFeature Bindings.processor s feature enabled) :
    Prelude.ReportsCPUFeature Bindings.processor t feature enabled := by
  unfold Prelude.ReportsCPUFeature at *
  rwa [(readCPUIDFeature_readOnly Bindings.processor.cpuid feature s).2 t hst]

theorem smrrUnblocked_of_sameControls [instBindings : X86.Machine.Bindings] {s t : RamState}
    (hst : SameControls s t) (h : Prelude.SMRRUnblocked instBindings s) :
    Prelude.SMRRUnblocked instBindings t := by
  unfold Prelude.SMRRUnblocked at *
  rwa [hst.smrrBase, hst.smrrMask]

theorem writeBackMemoryType_of_sameControls [instBindings : X86.Machine.Bindings] {s t : RamState}
    (hst : SameControls s t) {selector : BitVec 3}
    (h : Prelude.WriteBackMemoryType instBindings s selector) :
    Prelude.WriteBackMemoryType instBindings t selector := by
  intro address haddr
  exact ((getMemoryType_readOnly address selector s).2 t hst).trans (h address haddr)

/-! ### CPUID reports

Which `Prelude.ReportsCPUFeature` facts follow from others: features in the same leaf
(`reportsCPUFeature_of_sameLeaf`), and CET_SS from LAM (`reportsCETSS_of_reportsLAM`). With
`readCPUIDFeature_run` above, this is the one place that unfolds `Prelude.ReportsCPUFeature`,
`Read_CPUID_Feature` and `CPUID_Leaf_Available`. -/

private theorem id_pure {α : Type} (a : α) : (pure a : Id α) = a := rfl
private theorem id_bind {α β : Type} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl

/-- Decoding a feature bit from the four CPUID outputs never fails. -/
theorem decodeCPUIDFeature_run (g : CPUID_Feature) (a b c d : BitVec 32) :
    ∃ v, Decode_CPUID_Feature g a b c d = .ok v := by
  have hb : g.bit.toNat < 32 := g.bit.isLt
  have hle : Runtime.Unsigned g.bit + 1 ≤ 32 := by simp [x86_runtime]; omega
  unfold Decode_CPUID_Feature
  simp [Runtime.CheckedSlice.read, x86_runtime, bind, Except.bind, pure, Except.pure, hle]

/--
Two features in the same CPUID leaf and subleaf make the same queries, so if one is answered so is
the other.
-/
theorem reportsCPUFeature_of_sameLeaf {p : Processor} {s : RamState} {f g : CPUID_Feature}
    (hl : f.leaf = g.leaf) (hs : f.subleaf = g.subleaf) {b : Bool}
    (h : Prelude.ReportsCPUFeature p s f b) : ∃ c, Prelude.ReportsCPUFeature p s g c := by
  letI : Get_CPUID_Value.Binding Ram := p.cpuidBinding
  unfold Prelude.ReportsCPUFeature Read_CPUID_Feature at *
  rw [hl, hs] at h
  generalize (CPUID_Leaf_Available g.leaf g.subleaf : Runtime.SpecM Empty RamState Bool) = A at *
  generalize (Get_CPUID_Value g.leaf g.subleaf : Runtime.SpecM Empty RamState _) = G at *
  simp only [bind, ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind, ExceptT.bindCont] at *
  generalize A s = x at h ⊢
  obtain ⟨ra, s1⟩ := x
  cases ra with
  | error e => simp [pure, StateT.pure, Except.toOption] at h
  | ok a =>
    cases a
    · exact ⟨false, rfl⟩
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false, StateT.bind] at h ⊢
      generalize G s1 = y at h ⊢
      obtain ⟨rg, s2⟩ := y
      cases rg with
      | error e => exact absurd (show (none : Option Bool) = some b from h) (by simp)
      | ok r =>
        obtain ⟨v, hv⟩ := decodeCPUIDFeature_run g r.1 r.2.1 r.2.2.1 r.2.2.2
        refine ⟨v, ?_⟩
        show (Decode_CPUID_Feature g r.1 r.2.1 r.2.2.1 r.2.2.2).toOption = some v
        rw [hv]; rfl

/-- What the processor's CPUID binding answers at a state. -/
def cpuidResult (p : Processor) (s : RamState) (eax ecx : BitVec 32) :
    Except (Runtime.Error Empty) Cpuid.Registers :=
  match p.cpuid s.XCR0 (s.CR4.getLsbD 18) eax.toNat ecx.toNat with
  | .ok v => .ok v
  | .error m => .error (.externalFailure m)

/-- The processor's CPUID answer depends only on the controls (XCR0 and CR4.OSXSAVE). -/
theorem cpuidResult_of_sameControls {p : Processor} {s t : RamState} (h : SameControls s t)
    (eax ecx : BitVec 32) : cpuidResult p t eax ecx = cpuidResult p s eax ecx := by
  unfold cpuidResult
  rw [h.xcr0, h.cr4]

theorem getCPUIDValue_eq (p : Processor) :
    @Get_CPUID_Value Ram p.cpuidBinding = fun eax ecx s => (cpuidResult p s eax ecx, s) := by
  funext eax ecx s
  change (match p.cpuid s.XCR0 (s.CR4.getLsbD 18) eax.toNat ecx.toNat with
      | .ok value => (pure value : Runtime.SpecM Empty RamState _)
      | .error message => throw (Runtime.Error.externalFailure message)) s = _
  unfold cpuidResult
  generalize p.cpuid s.XCR0 (s.CR4.getLsbD 18) eax.toNat ecx.toNat = r
  cases r <;> rfl

/--
CET_SS (leaf 7, subleaf 0) is answered whenever LAM (leaf 7, subleaf 1) is: reading LAM queries
leaf 0 and leaf 7 subleaf 0, which are all CET_SS needs.
-/
theorem reportsCETSS_of_reportsLAM {p : Processor} {s : RamState} {b : Bool}
    (h : Prelude.ReportsCPUFeature p s CPUID_LAM_Encoding b) :
    ∃ c, Prelude.ReportsCPUFeature p s CPUID_CET_SS_Encoding c := by
  unfold Prelude.ReportsCPUFeature Read_CPUID_Feature CPUID_Leaf_Available at *
  rw [getCPUIDValue_eq] at h ⊢
  simp only [bind, ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind, ExceptT.bindCont,
    CPUID_LAM_Encoding, CPUID_CET_SS_Encoding, Runtime.CheckedSlice.read] at *
  simp [x86_runtime, pure, StateT.pure, ExceptT.pure, StateT.bind, ExceptT.bindCont, liftM,
    Except.toOption, ExceptT.mk, id_bind] at h ⊢
  generalize cpuidResult p s 0#32 0#32 = r00 at h ⊢
  rcases r00 with e | ⟨m, _⟩ <;> simp [StateT.pure, id_pure] at h ⊢
  simp only [show ∀ n : Nat, ((n : Int) < 7 ↔ n < 7) from fun n => by omega,
    show ∀ n : Nat, ((1 : Int) ≤ n ↔ 1 ≤ n) from fun n => by omega] at h ⊢
  by_cases hm : m.toNat < 7
  · simp [hm, StateT.pure] at h ⊢
    exact Or.inl rfl
  · simp [hm, StateT.bind, ExceptT.bindCont, id_bind] at h ⊢
    rcases h70 : cpuidResult p s 7#32 0#32 with e | r
    · simp [h70] at h
      exact absurd (show (none : Option Bool) = some b from h) (by simp)
    · obtain ⟨v, hv⟩ := decodeCPUIDFeature_run CPUID_CET_SS_Encoding r.1 r.2.1 r.2.2.1 r.2.2.2
      simp [CPUID_CET_SS_Encoding] at hv
      simp [h70, hv, StateT.pure, StateT.bind, ExceptT.bindCont, id_pure, id_bind, monadLift,
        MonadLift.monadLift, ExceptT.mk]
      cases v <;> first | exact Or.inl rfl | exact Or.inr rfl

end X86Proofs
