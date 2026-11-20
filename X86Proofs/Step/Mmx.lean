import X86Proofs.Step.Sse

/-!
# Decoding the MMX forms

The legacy MMX forms (`NP 0F …` on MMX registers: PADDB `mm, mm/m64`, MOVQ, PSLLW, …) share their
opcodes with the `66` SSE2 forms; each opcode's form selection picks the MMX form when there is no
`66` prefix and CPUID reports MMX (MMX and SSE2 for PADDQ, PSUBQ and PMULUDQ on MMX registers).

- `decoderSelect_run_mmx`, `decoderSelect_run_mmx_sse2`: `decoderSelect_run` for a selector that
  picks the form only when MMX (and SSE2) is reported;
- `decode_modrm_form_mmx`, `decode_modrm_form_mmx_sse2`: `decode_modrm_form` for those decoders;
- `decoderSelect_run_mmx_partial`, `decode_modrm_form_mmx_partial`: the same for the decoders
  that may diverge (`PartialSpecM`: `0F 70`, `C4`, `C5`, whose MMX forms are PSHUFW, PINSRW and
  PEXTRW).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- `decoderSelect_run` for an MMX opcode form: with MMX reported by CPUID, if `select` returns
`index` whatever the other features are (with the MMX feature `true`), the decoder continues with
`next index`. -/
theorem decoderSelect_run_mmx [Bindings] (s : RamState)
    (select : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Except (X86.Runtime.Error Empty) Int)
    {β : Type} (next : Int → X86.Runtime.SpecM X86.Exception RamState β) (index : Int)
    (hmode : In64BitMode s) (hf : DecoderFeatures s)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor s CPUID_MMX_Encoding true)
    (hselect : ∀ a c d e f, select true a true c d e f = .ok index) :
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
  obtain ⟨⟨a, ha⟩, -, ⟨c, hc⟩, ⟨d, hd⟩, ⟨e, he⟩, ⟨f, hf⟩⟩ := hf
  refine (specM_bind_run _ _ hmode).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run ha)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hmmx)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hc)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hd)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run he)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hf)).trans ?_
  refine specM_bind_run _ _ ?_
  rw [hselect]
  rfl

/-- `decoderSelect_run_mmx` for a selector that also needs SSE2 (PADDQ, PSUBQ, PMULUDQ on MMX
registers). -/
theorem decoderSelect_run_mmx_sse2 [Bindings] (s : RamState)
    (select : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Except (X86.Runtime.Error Empty) Int)
    {β : Type} (next : Int → X86.Runtime.SpecM X86.Exception RamState β) (index : Int)
    (hmode : In64BitMode s) (hf : DecoderFeatures s)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor s CPUID_MMX_Encoding true)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true)
    (hselect : ∀ a c e f, select true a true c true e f = .ok index) :
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
  obtain ⟨⟨a, ha⟩, -, ⟨c, hc⟩, -, ⟨e, he⟩, ⟨f, hf⟩⟩ := hf
  refine (specM_bind_run _ _ hmode).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run ha)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hmmx)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hc)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hsse2)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run he)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hf)).trans ?_
  refine specM_bind_run _ _ ?_
  rw [hselect]
  rfl

/-- `decode_modrm_form` for an MMX opcode form (`decoderSelect_run_mmx`), given the MMX feature
`hmmx` at the state after the ModRM fetch. -/
macro "decode_modrm_form_mmx" s:term:max t:term:max ip:term:max hfetch:term:max hmode:term:max
    hf:term:max hmmx:term:max hsel:term:max : tactic => `(tactic| (
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 1)) _ (s := $s) rfl).trans ?_
  refine (specM_bind_run _ _ $hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive _ 7 6) _ (s := $t) rfl).trans ?_
  try refine (specM_bind_run (X86.Runtime.sliceInclusive _ 5 3) _ (s := $t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive _ 2 0) _ (s := $t) rfl).trans ?_
  refine (decoderSelect_run_mmx $t _ _ _ $hmode $hf $hmmx $hsel).trans ?_
  try simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  first
    | (refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 2)) _ (s := $t) rfl).trans ?_
       exact specM_bind_pure_unit_run _ $t)
    | exact specM_bind_pure_unit_run _ $t))

/-- `decode_modrm_form_mmx` for an MMX form that also needs SSE2 (`decoderSelect_run_mmx_sse2`). -/
macro "decode_modrm_form_mmx_sse2" s:term:max t:term:max ip:term:max hfetch:term:max
    hmode:term:max hf:term:max hmmx:term:max hsse2:term:max hsel:term:max : tactic => `(tactic| (
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 1)) _ (s := $s) rfl).trans ?_
  refine (specM_bind_run _ _ $hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive _ 7 6) _ (s := $t) rfl).trans ?_
  try refine (specM_bind_run (X86.Runtime.sliceInclusive _ 5 3) _ (s := $t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive _ 2 0) _ (s := $t) rfl).trans ?_
  refine (decoderSelect_run_mmx_sse2 $t _ _ _ $hmode $hf $hmmx $hsse2 $hsel).trans ?_
  try simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 2)) _ (s := $t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ $t))

/-- `decoderSelect_run_mmx` for an opcode decoder that may diverge (`PartialSpecM`: `0F 70`, `C4`,
`C5`): it reads the mode and the CPUID features through `liftTotal`. -/
theorem decoderSelect_run_mmx_partial [Bindings] (s : RamState)
    (select : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Except (X86.Runtime.Error Empty) Int)
    {β : Type} (next : Int → X86.Runtime.PartialSpecM X86.Exception RamState β) (index : Int)
    (hmode : In64BitMode s) (hf : DecoderFeatures s)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor s CPUID_MMX_Encoding true)
    (hselect : ∀ a c d e f, select true a true c d e f = .ok index) :
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
  obtain ⟨⟨a, ha⟩, -, ⟨c, hc⟩, ⟨d, hd⟩, ⟨e, he⟩, ⟨f, hf⟩⟩ := hf
  refine (partialSpecM_liftTotal_bind_run _ _ hmode).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run ha)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run hmmx)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run hc)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run hd)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run he)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run hf)).trans ?_
  refine partialSpecM_bind_run _ _ ?_
  rw [hselect]
  rfl

/-- `decode_modrm_form_mmx` for a decoder that may diverge (`decoderSelect_run_mmx_partial`). -/
macro "decode_modrm_form_mmx_partial" s:term:max t:term:max ip:term:max hfetch:term:max
    hmode:term:max hf:term:max hmmx:term:max hsel:term:max : tactic => `(tactic| (
  refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 1)) _ (s := $s) rfl).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ $hfetch).trans ?_
  refine (partialSpecM_bind_run (X86.Runtime.sliceInclusive _ 7 6) _ (s := $t) rfl).trans ?_
  try refine (partialSpecM_bind_run (X86.Runtime.sliceInclusive _ 5 3) _ (s := $t) rfl).trans ?_
  refine (partialSpecM_bind_run (X86.Runtime.sliceInclusive _ 2 0) _ (s := $t) rfl).trans ?_
  refine (decoderSelect_run_mmx_partial $t _ _ _ $hmode $hf $hmmx $hsel).trans ?_
  try simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 2)) _ (s := $t) rfl).trans ?_
  first
    | exact partialSpecM_liftTotal_bind_pure_unit_run _ $t
    | exact partialSpecM_bind_pure_unit_run _ $t))

end X86Proofs
