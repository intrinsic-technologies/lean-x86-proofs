import X86Proofs.Step.Fetch
import X86Proofs.Step.Decode

/-!
# `ReadyToStep`: the machine facts every step lemma assumes

`ReadyToStep s` bundles `Prelude`'s machine predicates (for the processor and memory-type
configuration the `Bindings` select) with one fact of our own: the CPUID features the decoder
reads are answered (`DecoderFeatures`). It says nothing about RIP or the code: that the
instruction's bytes lie in the identity-mapped low 4 GiB is a hypothesis of each step lemma, next
to the bytes themselves, so `ReadyToStep` is about the machine only and every step preserves it.

`ReadyToStep.readyToStepCore` and `ReadyToStep.fetchReady` give the facts the step wrapper
(`Step/Wrapper.lean`) and the fetch lemma (`Step/Fetch.lean`) take.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/--
The machine facts every step lemma assumes, built from `Prelude`'s predicates for the processor
and memory-type configuration the bindings select.
-/
structure ReadyToStep [instBindings : Bindings] (s : RamState) : Prop where
  /-- 64-bit integer CPU configuration (flat code segment, paging, debug controls). -/
  cpu : Prelude.SupportedIntegerCPU Bindings.processor s
  /-- Identity-mapped page tables for the low 4 GiB. -/
  memory : Prelude.IdentityMappedMemory s
  /-- Active thread, no pending event, no debug trap, TF/RF clear. -/
  ready : Prelude.ExecutionReady s
  /-- No physical address is in the SMRR range, so RAM reads are not blocked. -/
  smrr : Prelude.SMRRUnblocked instBindings s
  /-- Write-back memory type below 4 GiB at PAT selector 0. -/
  memoryType : Prelude.WriteBackMemoryType instBindings s 0
  /-- The CPUID features the generated decoders read are answered. -/
  features : DecoderFeatures s

theorem ReadyToStep.of_supported [instBindings : Bindings] {s : RamState}
    (h : Prelude.SupportedIntegerMachineState Bindings.processor s)
    (hsmrr : Prelude.SMRRUnblocked instBindings s)
    (hmt : Prelude.WriteBackMemoryType instBindings s 0) (hfeatures : DecoderFeatures s) :
    ReadyToStep s :=
  ⟨h.integer, h.memory, h.ready, hsmrr, hmt, hfeatures⟩

/-- A state ready to step with SSE supported is a supported machine state. -/
theorem ReadyToStep.supported [Bindings] {s : RamState} (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) :
    Prelude.SupportedIntegerMachineState Bindings.processor s :=
  ⟨h.cpu, hsse, h.memory, h.ready⟩

theorem ReadyToStep.readyToStepCore [Bindings] {s : RamState} (h : ReadyToStep s) : ReadyToStepCore s :=
  ReadyToStepCore.of_prelude h.cpu h.ready

theorem SameControls.beforeFetch (s : RamState) : SameControls s (beforeFetch s) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The fetch facts, at the state `Fetch_And_Execute` starts from. -/
theorem ReadyToStep.fetchReady [Bindings] {s : RamState} (h : ReadyToStep s) :
    FetchReady (beforeFetch s) :=
  have hst := SameControls.beforeFetch s
  ⟨h.cpu.cs, h.cpu.cr0, h.memory.cr3, h.cpu.cr4, h.cpu.efer, h.cpu.maxPhysical, h.cpu.early,
    reportsCPUFeature_of_sameControls hst h.cpu.lam, reportsCPUFeature_of_sameControls hst h.cpu.lass,
    h.features.cetSS.imp fun _ => reportsCPUFeature_of_sameControls hst, smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.memory.tables⟩

/-! ### Ready to step in the middle of a REP string instruction -/

/--
`ReadyToStep` except for `Repeat_String_Operation`. Between the iterations of a REP string
instruction (`rep movsq`) the flag is set and RIP stays on the instruction, so those states are not
`ReadyToStep` (`ExecutionReady.repeatClear`); they are `ReadyMidRep`. Nothing before
`Fetch_And_Execute` and nothing in the fetch reads the flag (`checkDebugTraps_run` handles both
values), so the step wrappers that REP instructions use (`step_f3_rex_legacy0`) take `ReadyMidRep`.
-/
def ReadyMidRep [Bindings] (s : RamState) : Prop :=
  ReadyToStep { s with Repeat_String_Operation := false }

/-- A state with the flag clear is ready mid-REP iff it is ready. -/
theorem ReadyToStep.midRep [Bindings] {s : RamState} (h : ReadyToStep s) : ReadyMidRep s := by
  have he : { s with Repeat_String_Operation := false } = s := by
    have : ∀ b, s.Repeat_String_Operation = b → { s with Repeat_String_Operation := b } = s := by
      rintro b rfl; rfl
    exact this _ h.ready.repeatClear
  unfold ReadyMidRep
  rw [he]
  exact h

/-- `ReadyMidRep` with the flag clear is `ReadyToStep`. -/
theorem ReadyMidRep.ready [Bindings] {s : RamState} (h : ReadyMidRep s)
    (hrep : s.Repeat_String_Operation = false) : ReadyToStep s := by
  have he : { s with Repeat_String_Operation := false } = s := by
    have : ∀ b, s.Repeat_String_Operation = b → { s with Repeat_String_Operation := b } = s := by
      rintro b rfl; rfl
    exact this _ hrep
  unfold ReadyMidRep at h
  rwa [he] at h

theorem ReadyMidRep.readyToStepCore [Bindings] {s : RamState} (h : ReadyMidRep s) : ReadyToStepCore s :=
  have h' := ReadyToStep.readyToStepCore (s := { s with Repeat_String_Operation := false }) h
  ⟨h'.cs, h'.lma, h'.cr4, h'.debug, h'.aet, h'.event, h'.active, h'.sti, h'.movss, h'.singleStep,
    h'.taskSwitch, h'.breakpoint, h'.busLock, h'.tf, h'.rf⟩

theorem ReadyMidRep.fetchReady [Bindings] {s : RamState} (h : ReadyMidRep s) :
    FetchReady (beforeFetch s) :=
  have h' := ReadyToStep.fetchReady (s := { s with Repeat_String_Operation := false }) h
  have hst : SameControls (beforeFetch { s with Repeat_String_Operation := false })
      (beforeFetch s) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  ⟨h'.cs, h'.cr0, h'.cr3, h'.cr4, h'.efer, h'.maxPhysical, h'.early,
    reportsCPUFeature_of_sameControls hst h'.lam, reportsCPUFeature_of_sameControls hst h'.lass,
    h'.cetSS.imp fun _ => reportsCPUFeature_of_sameControls hst, smrrUnblocked_of_sameControls hst h'.smrr,
    writeBackMemoryType_of_sameControls hst h'.memoryType, h'.tables⟩

theorem ReadyMidRep.features [Bindings] {s : RamState} (h : ReadyMidRep s) : DecoderFeatures s :=
  DecoderFeatures.of_sameControls (s := { s with Repeat_String_Operation := false })
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (ReadyToStep.features h)

end X86Proofs
