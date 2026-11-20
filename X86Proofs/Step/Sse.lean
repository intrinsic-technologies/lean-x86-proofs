import X86Proofs.Step.Decode
import X86Proofs.Program.Agrees

/-!
# SSE preconditions

The legacy SSE forms (MOVUPS, MOVAPS, XORPS, …) check, besides the prefixes, three control-register
bits before they touch any state: `CR4.OSFXSR = 1` (else #UD), `CR0.EM = 0` (else #UD) and
`CR0.TS = 0` (else #NM). Their opcode decoders also select the form only if CPUID reports SSE.
`ReadyToStep` (the integer configuration) says nothing about these, so the SSE triples take
`Prelude.SupportedSSE Bindings.processor s` as a precondition: SSE reported by CPUID, `CR0.EM` and
`CR0.TS` clear, `CR4.OSFXSR` and `CR4.OSXMMEXCPT` set. It is the `sse` field of `Prelude`'s
`SupportedIntegerMachineState` (which `ReadyToStep.of_supported` drops), so a program proof gets
it from the same place as `ReadyToStep`. It depends only on the control registers and the CPUID
configuration, so every step keeps it (`SupportedSSE.of_sameControls`, `SupportedSSE.of_agreesExcept`).

- `cr4OSFXSR_run`, `cr0EM_run`, `cr0TS_run`: the three checks read the expected bits
  (`cr0EM_run_of_cr0`, `cr0TS_run_of_cr0` from the CR0 bits alone, for the MMX forms).
- `decoderSelect_run_sse`: `decoderSelect_run` for a selector that picks the form only when
  SSE is reported; `decoderSelect_run_sse2`: when SSE2 is reported (the `66`, `F2` and `F3`
  forms of the SSE2 opcodes).
- `decode_modrm_form_sse`, `decode_modrm_form_sse2`: `decode_modrm_form` for those decoders
  (as `decode_modrm_form`, for a decoder that reads the ModRM `reg` field or not: group opcodes
  such as `0F 71`–`73` select the form from it without binding it).
- `decoderSelect_run_sse2_partial`, `decode_modrm_form_sse2_partial` (and the SSE
  `decoderSelect_run_sse_partial`, `decode_modrm_form_sse_partial`): the same for the decoders
  that may diverge (`PartialSpecM`: `0F 70`, `C4`, `C5`, `C6`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem SupportedSSE.of_sameControls [Bindings] {s t : RamState} (hst : SameControls s t)
    (h : Prelude.SupportedSSE Bindings.processor s) : Prelude.SupportedSSE Bindings.processor t :=
  ⟨reportsCPUFeature_of_sameControls hst h.feature, hst.cr0 ▸ h.cr0, hst.cr4 ▸ h.cr4⟩

/-- `fixedPart` keeps every control register, so `AgreesExcept` keeps SSE support. -/
theorem SameControls.of_fixedPart {s t : RamState} (h : fixedPart t = fixedPart s) :
    SameControls s t :=
  ⟨congrArg (·.XCR0) h, congrArg (·.CR0) h, congrArg (·.CR4) h,
    congrArg (·.IA32_PAT) h, congrArg (·.IA32_MTRR_DEF_TYPE) h,
    congrArg (·.MTRR_Fixed) h, congrArg (·.MTRR_Base) h, congrArg (·.MTRR_Mask) h,
    congrArg (·.IA32_SMRR_PHYSBASE) h, congrArg (·.IA32_SMRR_PHYSMASK) h,
    congrArg (·.«SMM::In_SMM») h⟩

/-- SSE support survives any change `AgreesExcept` allows (in particular every triple's
`Effect.post`). -/
theorem SupportedSSE.of_agreesExcept [Bindings] {cs : List Component} {s t : RamState}
    (h : AgreesExcept cs s t) (hs : Prelude.SupportedSSE Bindings.processor s) :
    Prelude.SupportedSSE Bindings.processor t :=
  SupportedSSE.of_sameControls (SameControls.of_fixedPart h.rest) hs

theorem cr4OSFXSR_run [Bindings] {s : RamState} (h : Prelude.SupportedSSE Bindings.processor s) :
    (X86.CR4.OSFXSR : X86.Runtime.SpecM X86.Exception RamState _).run s = (.ok 1, s) := by
  have := h.cr4.osfxsr
  simp only [X86.CR4_Type.OSFXSR] at this
  simp [X86.CR4.OSFXSR, x86_runtime, get, getThe, MonadStateOf.get, bind, pure, ExceptT.bind,
    ExceptT.run, ExceptT.mk, StateT.bind, ExceptT.bindCont, liftM, monadLift, MonadLift.monadLift,
    ExceptT.pure, StateT.pure, StateT.get, ExceptT.lift, Functor.map, StateT.map, this]

theorem cr0EM_run [Bindings] {s : RamState} (h : Prelude.SupportedSSE Bindings.processor s) :
    (X86.CR0.EM : X86.Runtime.SpecM X86.Exception RamState _).run s = (.ok 0, s) := by
  have := h.cr0.em
  simp only [X86.CR0_Type.EM] at this
  simp [X86.CR0.EM, x86_runtime, get, getThe, MonadStateOf.get, bind, pure, ExceptT.bind,
    ExceptT.run, ExceptT.mk, StateT.bind, ExceptT.bindCont, liftM, monadLift, MonadLift.monadLift,
    ExceptT.pure, StateT.pure, StateT.get, ExceptT.lift, Functor.map, StateT.map, this]

theorem cr0TS_run [Bindings] {s : RamState} (h : Prelude.SupportedSSE Bindings.processor s) :
    (X86.CR0.TS : X86.Runtime.SpecM X86.Exception RamState _).run s = (.ok 0, s) := by
  have := h.cr0.ts
  simp only [X86.CR0_Type.TS] at this
  simp [X86.CR0.TS, x86_runtime, get, getThe, MonadStateOf.get, bind, pure, ExceptT.bind,
    ExceptT.run, ExceptT.mk, StateT.bind, ExceptT.bindCont, liftM, monadLift, MonadLift.monadLift,
    ExceptT.pure, StateT.pure, StateT.get, ExceptT.lift, Functor.map, StateT.map, this]

/-- `CR0.EM` reads 0 when it is clear (the MMX forms, whose precondition has only the CR0 part of
`Prelude.SupportedSSE`). -/
theorem cr0EM_run_of_cr0 {s : RamState} (h : Prelude.CR0.SSEEnabled s.CR0) :
    (X86.CR0.EM : X86.Runtime.SpecM X86.Exception RamState _).run s = (.ok 0, s) := by
  have := h.em
  simp only [X86.CR0_Type.EM] at this
  simp [X86.CR0.EM, x86_runtime, get, getThe, MonadStateOf.get, bind, pure, ExceptT.bind,
    ExceptT.run, ExceptT.mk, StateT.bind, ExceptT.bindCont, liftM, monadLift, MonadLift.monadLift,
    ExceptT.pure, StateT.pure, StateT.get, ExceptT.lift, Functor.map, StateT.map, this]

/-- `CR0.TS` reads 0 when it is clear. -/
theorem cr0TS_run_of_cr0 {s : RamState} (h : Prelude.CR0.SSEEnabled s.CR0) :
    (X86.CR0.TS : X86.Runtime.SpecM X86.Exception RamState _).run s = (.ok 0, s) := by
  have := h.ts
  simp only [X86.CR0_Type.TS] at this
  simp [X86.CR0.TS, x86_runtime, get, getThe, MonadStateOf.get, bind, pure, ExceptT.bind,
    ExceptT.run, ExceptT.mk, StateT.bind, ExceptT.bindCont, liftM, monadLift, MonadLift.monadLift,
    ExceptT.pure, StateT.pure, StateT.get, ExceptT.lift, Functor.map, StateT.map, this]

/--
`decoderSelect_run` for an SSE opcode: with SSE reported by CPUID, if `select` returns `index`
whatever the other features are (with the SSE feature `true`), the decoder continues with
`next index`.
-/
theorem decoderSelect_run_sse [Bindings] (s : RamState)
    (select : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Except (X86.Runtime.Error Empty) Int)
    {β : Type} (next : Int → X86.Runtime.SpecM X86.Exception RamState β) (index : Int)
    (hmode : In64BitMode s) (hf : DecoderFeatures s)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE_Encoding true)
    (hselect : ∀ a b d e f, select true a b true d e f = .ok index) :
    (do
      let mode ← In_64Bit_Mode
      let a ← CPUID_LZCNT
      let b ← CPUID_MMX
      let c ← CPUID_SSE
      let d ← CPUID_SSE2
      let e ← CPUID_CET_SS
      let f ← CPUID_CMPXCHG16B
      let i ← liftM (select mode a b c d e f)
      next i : X86.Runtime.SpecM X86.Exception RamState β).run s = (next index).run s := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, -, ⟨d, hd⟩, ⟨e, he⟩, ⟨f, hf⟩⟩ := hf
  refine (specM_bind_run _ _ hmode).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run ha)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hb)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hsse)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hd)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run he)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hf)).trans ?_
  refine specM_bind_run _ _ ?_
  rw [hselect]
  rfl

/--
`decoderSelect_run` for an SSE2 opcode form: with SSE2 reported by CPUID, if `select` returns
`index` whatever the other features are (with the SSE2 feature `true`), the decoder continues
with `next index`.
-/
theorem decoderSelect_run_sse2 [Bindings] (s : RamState)
    (select : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Except (X86.Runtime.Error Empty) Int)
    {β : Type} (next : Int → X86.Runtime.SpecM X86.Exception RamState β) (index : Int)
    (hmode : In64BitMode s) (hf : DecoderFeatures s)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true)
    (hselect : ∀ a b c e f, select true a b c true e f = .ok index) :
    (do
      let mode ← In_64Bit_Mode
      let a ← CPUID_LZCNT
      let b ← CPUID_MMX
      let c ← CPUID_SSE
      let d ← CPUID_SSE2
      let e ← CPUID_CET_SS
      let f ← CPUID_CMPXCHG16B
      let i ← liftM (select mode a b c d e f)
      next i : X86.Runtime.SpecM X86.Exception RamState β).run s = (next index).run s := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, -, ⟨e, he⟩, ⟨f, hf⟩⟩ := hf
  refine (specM_bind_run _ _ hmode).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run ha)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hb)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hc)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hsse2)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run he)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hf)).trans ?_
  refine specM_bind_run _ _ ?_
  rw [hselect]
  rfl

/-- `decode_modrm_form` for an SSE opcode form (`decoderSelect_run_sse`), given the SSE feature
`hsse` at the state after the ModRM fetch. -/
macro "decode_modrm_form_sse" s:term:max t:term:max ip:term:max hfetch:term:max hmode:term:max
    hf:term:max hsse:term:max hsel:term:max : tactic => `(tactic| (
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 1)) _ (s := $s) rfl).trans ?_
  refine (specM_bind_run _ _ $hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive _ 7 6) _ (s := $t) rfl).trans ?_
  try refine (specM_bind_run (X86.Runtime.sliceInclusive _ 5 3) _ (s := $t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive _ 2 0) _ (s := $t) rfl).trans ?_
  refine (decoderSelect_run_sse $t _ _ _ $hmode $hf $hsse $hsel).trans ?_
  try simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 2)) _ (s := $t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ $t))

/-- `decode_modrm_form` for an SSE2 opcode form (`decoderSelect_run_sse2`), given the SSE2
feature `hsse2` at the state after the ModRM fetch. -/
macro "decode_modrm_form_sse2" s:term:max t:term:max ip:term:max hfetch:term:max hmode:term:max
    hf:term:max hsse2:term:max hsel:term:max : tactic => `(tactic| (
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 1)) _ (s := $s) rfl).trans ?_
  refine (specM_bind_run _ _ $hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive _ 7 6) _ (s := $t) rfl).trans ?_
  try refine (specM_bind_run (X86.Runtime.sliceInclusive _ 5 3) _ (s := $t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive _ 2 0) _ (s := $t) rfl).trans ?_
  refine (decoderSelect_run_sse2 $t _ _ _ $hmode $hf $hsse2 $hsel).trans ?_
  try simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 2)) _ (s := $t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ $t))

/--
`decoderSelect_run_sse2` for an opcode decoder that may diverge (`PartialSpecM`: `0F 70`, `C4`,
`C5`, `C6`, whose forms or operations use a partial lean-x86 helper): it reads the mode and the
CPUID features through `liftTotal`.
-/
theorem decoderSelect_run_sse2_partial [Bindings] (s : RamState)
    (select : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Except (X86.Runtime.Error Empty) Int)
    {β : Type} (next : Int → X86.Runtime.PartialSpecM X86.Exception RamState β) (index : Int)
    (hmode : In64BitMode s) (hf : DecoderFeatures s)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true)
    (hselect : ∀ a b c e f, select true a b c true e f = .ok index) :
    (do
      let mode ← X86.Runtime.liftTotal In_64Bit_Mode
      let a ← X86.Runtime.liftTotal CPUID_LZCNT
      let b ← X86.Runtime.liftTotal CPUID_MMX
      let c ← X86.Runtime.liftTotal CPUID_SSE
      let d ← X86.Runtime.liftTotal CPUID_SSE2
      let e ← X86.Runtime.liftTotal CPUID_CET_SS
      let f ← X86.Runtime.liftTotal CPUID_CMPXCHG16B
      let i ← liftM (select mode a b c d e f)
      next i : X86.Runtime.PartialSpecM X86.Exception RamState β).run s = (next index).run s := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, -, ⟨e, he⟩, ⟨f, hf⟩⟩ := hf
  refine (partialSpecM_liftTotal_bind_run _ _ hmode).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run ha)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run hb)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run hc)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run hsse2)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run he)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run hf)).trans ?_
  refine partialSpecM_bind_run _ _ ?_
  rw [hselect]
  rfl

/-- `decode_modrm_form_sse2` for a decoder that may diverge (`decoderSelect_run_sse2_partial`): the
chosen form is run as it is (a `PartialSpecM` form) or through `liftTotal` (a total form, whose run
is then wrapped in `some`). -/
macro "decode_modrm_form_sse2_partial" s:term:max t:term:max ip:term:max hfetch:term:max
    hmode:term:max hf:term:max hsse2:term:max hsel:term:max : tactic => `(tactic| (
  refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 1)) _ (s := $s) rfl).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ $hfetch).trans ?_
  refine (partialSpecM_bind_run (X86.Runtime.sliceInclusive _ 7 6) _ (s := $t) rfl).trans ?_
  try refine (partialSpecM_bind_run (X86.Runtime.sliceInclusive _ 5 3) _ (s := $t) rfl).trans ?_
  refine (partialSpecM_bind_run (X86.Runtime.sliceInclusive _ 2 0) _ (s := $t) rfl).trans ?_
  refine (decoderSelect_run_sse2_partial $t _ _ _ $hmode $hf $hsse2 $hsel).trans ?_
  try simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 2)) _ (s := $t) rfl).trans ?_
  first
    | exact partialSpecM_liftTotal_bind_pure_unit_run _ $t
    | exact partialSpecM_bind_pure_unit_run _ $t))

/-- `decoderSelect_run_sse` for a decoder that may diverge (`decoderSelect_run_sse2_partial`; the
`NP` form of `0F C6`). -/
theorem decoderSelect_run_sse_partial [Bindings] (s : RamState)
    (select : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Except (X86.Runtime.Error Empty) Int)
    {β : Type} (next : Int → X86.Runtime.PartialSpecM X86.Exception RamState β) (index : Int)
    (hmode : In64BitMode s) (hf : DecoderFeatures s)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE_Encoding true)
    (hselect : ∀ a b d e f, select true a b true d e f = .ok index) :
    (do
      let mode ← X86.Runtime.liftTotal In_64Bit_Mode
      let a ← X86.Runtime.liftTotal CPUID_LZCNT
      let b ← X86.Runtime.liftTotal CPUID_MMX
      let c ← X86.Runtime.liftTotal CPUID_SSE
      let d ← X86.Runtime.liftTotal CPUID_SSE2
      let e ← X86.Runtime.liftTotal CPUID_CET_SS
      let f ← X86.Runtime.liftTotal CPUID_CMPXCHG16B
      let i ← liftM (select mode a b c d e f)
      next i : X86.Runtime.PartialSpecM X86.Exception RamState β).run s = (next index).run s := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, -, ⟨d, hd⟩, ⟨e, he⟩, ⟨f, hf⟩⟩ := hf
  refine (partialSpecM_liftTotal_bind_run _ _ hmode).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run ha)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run hb)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run hsse)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run hd)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run he)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run hf)).trans ?_
  refine partialSpecM_bind_run _ _ ?_
  rw [hselect]
  rfl

/-- `decode_modrm_form_sse2_partial` for an SSE (`NP`) form (`decoderSelect_run_sse_partial`). -/
macro "decode_modrm_form_sse_partial" s:term:max t:term:max ip:term:max hfetch:term:max
    hmode:term:max hf:term:max hsse:term:max hsel:term:max : tactic => `(tactic| (
  refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 1)) _ (s := $s) rfl).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ $hfetch).trans ?_
  refine (partialSpecM_bind_run (X86.Runtime.sliceInclusive _ 7 6) _ (s := $t) rfl).trans ?_
  try refine (partialSpecM_bind_run (X86.Runtime.sliceInclusive _ 5 3) _ (s := $t) rfl).trans ?_
  refine (partialSpecM_bind_run (X86.Runtime.sliceInclusive _ 2 0) _ (s := $t) rfl).trans ?_
  refine (decoderSelect_run_sse_partial $t _ _ _ $hmode $hf $hsse $hsel).trans ?_
  try simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 2)) _ (s := $t) rfl).trans ?_
  first
    | exact partialSpecM_liftTotal_bind_pure_unit_run _ $t
    | exact partialSpecM_bind_pure_unit_run _ $t))

end X86Proofs
