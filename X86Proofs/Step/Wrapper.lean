import X86Proofs.Step.ReadyToStepCore
import X86Proofs.Step.Debug

/-!
# The step wrapper

Under `ReadyToStepCore s`, lean-x86's `step s` runs `Fetch_And_Execute` from `beforeFetch s`, then
does `finishStep` (RIP := Next_IP). Every step lemma goes through `step_of_fetchAndExecute`; the
fetch and decode inside `Fetch_And_Execute` stay a black box here. `step_run_of_fetchAndExecute`
is stated for any `X86.State σ`, not only `RamState`.
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers X86.UserProcess

variable {σ : Type}

theorem handleAsynchronousEvent_run [PhysicalMemory σ] [Bindings] (s : X86.State σ) (he : s.Current_Event = .No_Event)
    (hb : s.Event_Blocked.STI_BLOCKING = false) :
    Handle_Asynchronous_Event.run s = (.ok false, s) := by
  unfold Handle_Asynchronous_Event
  rw [accelerated_eq_self]
  simp only [Handle_Asynchronous_Event.source, X86.RFLAGS.IF, X86.Event_Blocked.setSTI_BLOCKING]
  simp [get, getThe, liftM, bind, ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind,
    ExceptT.bindCont, MonadStateOf.get, monadLift, MonadLift.monadLift, pure, ExceptT.pure,
    StateT.pure, StateT.get, ExceptT.lift, Functor.map, StateT.map, Bind.bind, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, he, x86_runtime, HOr.hOr, OrOp.or, strictOr,
    HAnd.hAnd, AndOp.and, strictAnd]
  rw [← he, ← hb]

theorem inPVIMode_run (s : X86.State σ) (hcr4 : Prelude.CR4.VirtualInterruptsDisabled s.CR4) :
    In_PVI_Mode.run s = (.ok false, s) := by
  have hpvi : BitVec.extractLsb' 1 1 s.CR4 = 0 := hcr4.pvi
  simp [In_PVI_Mode, cr0PE_eq, rflagsVM_eq, X86.CR4.PVI, get, getThe, liftM, bind, ExceptT.bind,
    ExceptT.run, ExceptT.mk, StateT.bind, ExceptT.bindCont, MonadStateOf.get, monadLift,
    MonadLift.monadLift, pure, ExceptT.pure, StateT.pure, StateT.get, ExceptT.lift, Functor.map,
    StateT.map, Bind.bind, x86_runtime, HAnd.hAnd, AndOp.and, strictAnd, hpvi]

theorem inVMEMode_run (s : X86.State σ) (hcr4 : Prelude.CR4.VirtualInterruptsDisabled s.CR4) :
    In_VME_Mode.run s = (.ok false, s) := by
  have hvme : BitVec.extractLsb' 0 1 s.CR4 = 0 := hcr4.vme
  simp [In_VME_Mode, cr0PE_eq, rflagsVM_eq, X86.CR4.VME, get, getThe, liftM, bind, ExceptT.bind,
    ExceptT.run, ExceptT.mk, StateT.bind, ExceptT.bindCont, MonadStateOf.get, monadLift,
    MonadLift.monadLift, pure, ExceptT.pure, StateT.pure, StateT.get, ExceptT.lift, Functor.map,
    StateT.map, Bind.bind, x86_runtime, HAnd.hAnd, AndOp.and, strictAnd, hvme]

theorem checkDebugTraps_run [X86.Get_CPUID_Value.Binding σ] [X86.Helpers.Unimplemented_Feature.Binding σ] (s : X86.State σ) (branch : Bool) (h : ReadyToStepCore s) :
    (Check_Debug_Traps branch).run s = (.ok (), s) := by
  have hb := getInstructionBreakpointMatch_run s h.cs h.lma h.debug
  have hg : (get : X86.Runtime.SpecM X86.Exception (X86.State σ) (X86.State σ)).run s = (.ok s, s) :=
    rfl
  have hr : X86.RFLAGS.RF.run s = (.ok 0, s) := by
    change (Except.ok (ε := X86.Runtime.Error X86.Exception) (BitVec.extractLsb' 16 1 s.RFLAGS), s) = _
    rw [show BitVec.extractLsb' 16 1 s.RFLAGS = 0 from h.rf.rf]
  have ht : X86.RFLAGS.TF.run s = (.ok 0, s) := by
    change (Except.ok (ε := X86.Runtime.Error X86.Exception) (BitVec.extractLsb' 8 1 s.RFLAGS), s) = _
    rw [show BitVec.extractLsb' 8 1 s.RFLAGS = 0 from h.tf.tf]
  have hc : X86.IA32_DEBUGCTL.BTF.run s = (.ok (BitVec.extractLsb' 1 1 s.IA32_DEBUGCTL), s) := rfl
  have hz : (Std.Bits.Zero 4 : X86.Runtime.SpecM X86.Exception (X86.State σ) (BitVec 4)).run s =
      (.ok 0, s) := rfl
  unfold Check_Debug_Traps
  rw [accelerated_eq_self]
  unfold Check_Debug_Traps.source
  cases hrep : s.Repeat_String_Operation <;>
  simp only [hrep, specM_bind_run _ _ hz, pure_bind, specM_bind_run _ _ hg, specM_bind_run _ _ hr, specM_bind_run _ _ ht, specM_bind_run _ _ hc,
    h.aet, h.movss, h.singleStep, h.taskSwitch, h.breakpoint, h.busLock, specM_bind_run _ _ hb,
    HAnd.hAnd, AndOp.and, strictAnd, HOr.hOr, OrOp.or, strictOr,
    BitVec.reduceBEq, Bool.not_false, Bool.not_true, Bool.false_and,
    Bool.and_true, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte, specM_pure_run]

theorem ReadyToStepCore.resetStepFields {s : X86.State σ} (h : ReadyToStepCore s) : ReadyToStepCore (resetStepFields s) :=
  ⟨h.cs, h.lma, h.cr4, h.debug, h.aet, h.event, h.active, h.sti, h.movss, h.singleStep,
    h.taskSwitch, h.breakpoint, h.busLock, h.tf, h.rf⟩

theorem setRF_zero_run (s : X86.State σ) (h : Prelude.RFLAGS.ResumeFlagClear s.RFLAGS) :
    (X86.RFLAGS.setRF 0).run s = (.ok (), s) := by
  have hrf : BitVec.extractLsb' 16 1 s.RFLAGS = 0 := h.rf
  have hbit : s.RFLAGS.getLsbD 16 = false := by
    have := congrArg (fun b : BitVec 1 => b.getLsbD 0) hrf
    simpa [BitVec.getLsbD_extractLsb'] using this
  have hb : X86.Runtime.setSlice s.RFLAGS 16 1 0 = s.RFLAGS := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [getLsbD_setSlice _ _ _ _ _ hi]
    split
    · rename_i h
      rw [show i = 16 by omega, hbit]
      simp
    · rfl
  change (Except.ok (ε := X86.Runtime.Error X86.Exception) (),
    {s with RFLAGS := X86.Runtime.setSlice s.RFLAGS 16 1 0}) = _
  rw [hb]

/--
lean-x86's generated `Step` under `ReadyToStepCore s`: it runs `Fetch_And_Execute` from
`beforeFetch s` and, if that returns normally in 64-bit mode, finishes with `finishStep`.
-/
theorem step_run_of_fetchAndExecute [PhysicalMemory σ] [Bindings] (s t : X86.State σ)
    (h : ReadyToStepCore s)
    (hfetch : Fetch_And_Execute.run (beforeFetch s) = some (.ok (), t))
    (hmode : In64BitMode t) :
    Step.run s = some (.ok (), finishStep t) := by
  unfold Step
  simp only [partialSpecM_get_bind_run, partialSpecM_modify_bind_run,
    partialSpecM_liftTotal_modify_bind_run, X86.Concurrent_Exception.setvalid,
    X86.Default_Error_Code.assign, x86_runtime, pure_bind]
  refine (partialSpecM_bind_run _ _ (t := finishStep t) (value := ()) ?_).trans ?_
  · apply partialSpecM_tryCatch_run
    have hs := h.resetStepFields
    refine (partialSpecM_bind_run _ _ (partialSpecM_liftTotal_run _
      (handleAsynchronousEvent_run (resetStepFields s) hs.event hs.sti))).trans ?_
    simp only [Bool.not_false, ↓reduceIte, partialSpecM_get_bind_run]
    simp only [show (resetStepFields s).Thread_Status = .THREAD_ACTIVE from hs.active]
    refine (partialSpecM_bind_run _ _ (partialSpecM_liftTotal_run _ (inPVIMode_run (resetStepFields s) hs.cr4))).trans ?_
    refine (partialSpecM_bind_run _ _ (partialSpecM_liftTotal_run _ (inVMEMode_run (resetStepFields s) hs.cr4))).trans ?_
    have hvif : X86.RFLAGS.VIF.run (resetStepFields s) =
        (.ok (BitVec.extractLsb' 19 1 s.RFLAGS), resetStepFields s) := rfl
    have hvip : X86.RFLAGS.VIP.run (resetStepFields s) =
        (.ok (BitVec.extractLsb' 20 1 s.RFLAGS), resetStepFields s) := rfl
    refine (partialSpecM_bind_run _ _ (partialSpecM_liftTotal_run _ hvif)).trans ?_
    refine (partialSpecM_bind_run _ _ (partialSpecM_liftTotal_run _ hvip)).trans ?_
    simp only [HOr.hOr, OrOp.or, strictOr, HAnd.hAnd, AndOp.and, strictAnd,
      Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    have hd := checkDebugTraps_run (resetStepFields s) s.Branch_Taken hs
    refine (partialSpecM_bind_run _ _ (partialSpecM_liftTotal_run _ hd)).trans ?_
    refine (partialSpecM_bind_run _ _ (partialSpecM_liftTotal_run _ (setRF_zero_run (resetStepFields s) hs.rf))).trans ?_
    simp only [partialSpecM_modify_bind_run]
    refine (partialSpecM_bind_run _ _ hfetch).trans ?_
    simp only [h.movss, Bool.false_eq_true, ↓reduceIte, partialSpecM_get_bind_run]
    by_cases ha : (!t.Branch_Taken && !t.Repeat_String_Operation && !t.«MSRLIST::In_Process») = true
    · simp only [ha, ↓reduceIte, finishStep]
      simp only [X86.RIP.assign]
      have hm : In64BitMode { t with RIP := t.Next_IP } := hmode.of_cs_lma_eq rfl rfl
      refine (partialSpecM_bind_run _ _ (partialSpecM_liftTotal_run _ hm)).trans ?_
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, partialSpecM_pure_run]
    · simp only [ha, Bool.false_eq_true, ↓reduceIte, finishStep, partialSpecM_pure_run]
  · rfl

/--
The step wrapper. Under `ReadyToStepCore s`, if `Fetch_And_Execute` (fetch, decode and the form's
code) run from `beforeFetch s` returns normally with state `t` still in 64-bit mode, then
`step s` is `.next` of `t` with `Next_IP` copied into RIP (`finishStep`).
-/
theorem step_of_fetchAndExecute [PhysicalMemory σ] [Bindings] (s t : X86.State σ)
    (h : ReadyToStepCore s)
    (hfetch : Fetch_And_Execute.run (beforeFetch s) = some (.ok (), t))
    (hmode : In64BitMode t) :
    X86.Machine.step s = some (.next (finishStep t)) := by
  unfold X86.Machine.step
  rw [step_run_of_fetchAndExecute s t h hfetch hmode]
  rfl

end X86Proofs
