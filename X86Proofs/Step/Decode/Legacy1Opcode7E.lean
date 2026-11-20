import X86Proofs.Step.Mmx

/-!
# Opcode `0F 7E`: `MOVD`/`MOVQ r/m, xmm` and `r/m, mm`

The one place that looks inside lean-x86's opcode-`7E` decoder (`Decode_Legacy_1_Opcode_7E`) and its
form selection (`Select_Legacy_1_Opcode_7E`), architecture rule 5. In 64-bit mode the selection
picks `MOVD_GPR32_XMMd_0` after `66` without REX.W and `MOVQ_GPR64_XMMq` after `66` with REX.W, for
`mod = 3`, without `F3`, with SSE2 (`Instructions/Movd/Generated/RX`,
`Instructions/Movq/Generated/RX`), and `MOVD_MEMd_XMMd_1` / `MOVQ_MEMq_XMMq_0F7E_0` for `mod ≠ 3`
(`Instructions/Movd/Generated/MX`, `Instructions/Movq/Generated/MX7E`); after `F3`, with SSE2,
`MOVQ_XMMdq_MEMq_0F7E_1` (`mod ≠ 3`) and `MOVQ_XMMdq_XMMq_0F7E` (`mod = 3`), `MOVQ xmm, xmm/m64`
(`Instructions/Movq/Generated/{XM,XX}`). Without a prefix, with MMX, it picks the MMX forms
`MOVD_GPR32_MMXd_0` / `MOVQ_GPR64_MMXq` (`mod = 3`, by REX.W;
`Instructions/{Movd,Movq}/Generated/{RM32,RM64}`) and `MOVD_MEMd_MMXd_0` / `MOVQ_MEMq_MMXq_0F7E`
(`Instructions/Movd/Generated/MemM`, `Instructions/Movq/Generated/MemM7E`). For each, a
`selectLegacy1Opcode7E_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy1Opcode7E_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`, `ip` the
second opcode byte's address) to the call of that form at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcode7E` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` and a `66` prefix, `rex_w = 0`, `rep_prefix = 0` in 64-bit mode, with SSE2: form
7, `MOVD_GPR32_XMMd_0`. -/
theorem selectLegacy1Opcode7E_run_of_66_w0_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_7E context true a b c true e f modrm = .ok 7 := by
  simp [Select_Legacy_1_Opcode_7E, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd,
    HOr.hOr, OrOp.or, strictOr]

/-- The opcode-7E decoder with a `66` prefix, `rex_w = 0`, `rep_prefix = 0` and a register ModRM
(`mod = 3`), with SSE2 reported, runs `MOVD_GPR32_XMMd_0` from the state after the ModRM fetch, at
`ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode7E_run_of_66_w0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_7E ip context).run s =
      (X86.Instructions.MOVD_GPR32_XMMd_0 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_7E
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode7E_run_of_66_w0_register context hosz hw hrep a b c e f
      modrm hmod)

/-- With `mod = 3` and a `66` prefix, `rex_w = 1`, `rep_prefix = 0` in 64-bit mode, with SSE2: form
9, `MOVQ_GPR64_XMMq`. -/
theorem selectLegacy1Opcode7E_run_of_66_w1_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_7E context true a b c true e f modrm = .ok 9 := by
  simp [Select_Legacy_1_Opcode_7E, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd,
    HOr.hOr, OrOp.or, strictOr]

/-- The opcode-7E decoder with a `66` prefix, `rex_w = 1`, `rep_prefix = 0` and a register ModRM
(`mod = 3`), with SSE2 reported, runs `MOVQ_GPR64_XMMq` from the state after the ModRM fetch, at
`ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode7E_run_of_66_w1_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_7E ip context).run s =
      (X86.Instructions.MOVQ_GPR64_XMMq (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_7E
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode7E_run_of_66_w1_register context hosz hw hrep a b c e f
      modrm hmod)

/-- With `mod ≠ 3`, an `F3` prefix (`rep_prefix = 243`), in 64-bit mode with SSE2: form 1,
`MOVQ_XMMdq_MEMq_0F7E_1`. -/
theorem selectLegacy1Opcode7E_run_of_f3_memory (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_7E context true a b c true e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_7E, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-7E decoder with an `F3` prefix (`rep_prefix = 243`) and a memory ModRM (`mod ≠ 3`),
with SSE2 reported, runs `MOVQ_XMMdq_MEMq_0F7E_1` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1Opcode7E_run_of_f3_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_7E ip context).run s =
      (X86.Instructions.MOVQ_XMMdq_MEMq_0F7E_1 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_7E
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode7E_run_of_f3_memory context hrep a b c e f
      modrm hmod)

/-- With `mod = 3`, an `F3` prefix (`rep_prefix = 243`), in 64-bit mode with SSE2: form 2,
`MOVQ_XMMdq_XMMq_0F7E`. -/
theorem selectLegacy1Opcode7E_run_of_f3_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_7E context true a b c true e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_7E, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-7E decoder with an `F3` prefix (`rep_prefix = 243`) and a register ModRM (`mod = 3`),
with SSE2 reported, runs `MOVQ_XMMdq_XMMq_0F7E` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1Opcode7E_run_of_f3_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_7E ip context).run s =
      (X86.Instructions.MOVQ_XMMdq_XMMq_0F7E (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_7E
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode7E_run_of_f3_register context hrep a b c e f
      modrm hmod)

/-- With `mod ≠ 3`, a `66` prefix, `rex_w = 0` and `rep_prefix = 0`, in 64-bit mode with SSE2: form
8, `MOVD_MEMd_XMMd_1`. -/
theorem selectLegacy1Opcode7E_run_of_66_w0_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_7E context true a b c true e f modrm = .ok 8 := by
  simp [Select_Legacy_1_Opcode_7E, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd,
    HOr.hOr, OrOp.or, strictOr]

/-- The opcode-7E decoder with a `66` prefix, `rex_w = 0` and `rep_prefix = 0` and a memory ModRM
(`mod ≠ 3`), with SSE2 reported, runs `MOVD_MEMd_XMMd_1` from the state after the ModRM fetch, at
`ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode7E_run_of_66_w0_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_7E ip context).run s =
      (X86.Instructions.MOVD_MEMd_XMMd_1 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_7E
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode7E_run_of_66_w0_memory context hosz hw hrep a b c e f
      modrm hmod)

/-- With `mod ≠ 3`, a `66` prefix, `rex_w = 1` and `rep_prefix = 0`, in 64-bit mode with SSE2: form
10, `MOVQ_MEMq_XMMq_0F7E_0`. -/
theorem selectLegacy1Opcode7E_run_of_66_w1_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_7E context true a b c true e f modrm = .ok 10 := by
  simp [Select_Legacy_1_Opcode_7E, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd,
    HOr.hOr, OrOp.or, strictOr]

/-- The opcode-7E decoder with a `66` prefix, `rex_w = 1` and `rep_prefix = 0` and a memory ModRM
(`mod ≠ 3`), with SSE2 reported, runs `MOVQ_MEMq_XMMq_0F7E_0` from the state after the ModRM fetch,
at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode7E_run_of_66_w1_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_7E ip context).run s =
      (X86.Instructions.MOVQ_MEMq_XMMq_0F7E_0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_7E
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode7E_run_of_66_w1_memory context hosz hw hrep a b c e f
      modrm hmod)

/-- With `mod ≠ 3` and no `66` prefix, REX.W = 1, no REP prefix in 64-bit mode, with MMX: form 6,
`MOVQ_MEMq_MMXq_0F7E`. -/
theorem selectLegacy1Opcode7E_run_of_w1_mmx_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 0)
    (a c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_7E context true a true c d e f modrm = .ok 6 := by
  simp [Select_Legacy_1_Opcode_7E, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd,
    HOr.hOr, OrOp.or, strictOr]

/-- The opcode-7E decoder with no `66` prefix, REX.W = 1, no REP prefix and a memory ModRM
(`mod ≠ 3`), with MMX reported, runs `MOVQ_MEMq_MMXq_0F7E` from the state after the ModRM fetch, at
`ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode7E_run_of_w1_mmx_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 1) (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor t CPUID_MMX_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_7E ip context).run s =
      (X86.Instructions.MOVQ_MEMq_MMXq_0F7E (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_7E
  decode_modrm_form_mmx s t ip hfetch hmode hf hmmx
    (fun a c d e f =>
      selectLegacy1Opcode7E_run_of_w1_mmx_memory context hosz hw hrep a c d e f modrm hmod)

/-- With `mod ≠ 3` and no `66` prefix, REX.W = 0, no REP prefix in 64-bit mode, with MMX: form 4,
`MOVD_MEMd_MMXd_0`. -/
theorem selectLegacy1Opcode7E_run_of_w0_mmx_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (a c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_7E context true a true c d e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_7E, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd,
    HOr.hOr, OrOp.or, strictOr]

/-- The opcode-7E decoder with no `66` prefix, REX.W = 0, no REP prefix and a memory ModRM
(`mod ≠ 3`), with MMX reported, runs `MOVD_MEMd_MMXd_0` from the state after the ModRM fetch, at
`ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode7E_run_of_w0_mmx_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0) (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor t CPUID_MMX_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_7E ip context).run s =
      (X86.Instructions.MOVD_MEMd_MMXd_0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_7E
  decode_modrm_form_mmx s t ip hfetch hmode hf hmmx
    (fun a c d e f =>
      selectLegacy1Opcode7E_run_of_w0_mmx_memory context hosz hw hrep a c d e f modrm hmod)

/-- With `mod = 3` and no `66` prefix, REX.W = 0, no REP prefix in 64-bit mode, with MMX: form 3,
`MOVD_GPR32_MMXd_0`. -/
theorem selectLegacy1Opcode7E_run_of_w0_mmx_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (a c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_7E context true a true c d e f modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_7E, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd,
    HOr.hOr, OrOp.or, strictOr]

/-- The opcode-7E decoder with no `66` prefix, REX.W = 0, no REP prefix and a register ModRM
(`mod = 3`), with MMX reported, runs `MOVD_GPR32_MMXd_0` from the state after the ModRM fetch, at
`ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode7E_run_of_w0_mmx_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0) (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor t CPUID_MMX_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_7E ip context).run s =
      (X86.Instructions.MOVD_GPR32_MMXd_0 (BitVec.add ip 2#64) context (modrm.extractLsb' 3 3)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_7E
  decode_modrm_form_mmx s t ip hfetch hmode hf hmmx
    (fun a c d e f =>
      selectLegacy1Opcode7E_run_of_w0_mmx_register context hosz hw hrep a c d e f modrm hmod)

/-- With `mod = 3` and no `66` prefix, REX.W = 1, no REP prefix in 64-bit mode, with MMX: form 5,
`MOVQ_GPR64_MMXq`. -/
theorem selectLegacy1Opcode7E_run_of_w1_mmx_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 0)
    (a c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_7E context true a true c d e f modrm = .ok 5 := by
  simp [Select_Legacy_1_Opcode_7E, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd,
    HOr.hOr, OrOp.or, strictOr]

/-- The opcode-7E decoder with no `66` prefix, REX.W = 1, no REP prefix and a register ModRM
(`mod = 3`), with MMX reported, runs `MOVQ_GPR64_MMXq` from the state after the ModRM fetch, at
`ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode7E_run_of_w1_mmx_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 1) (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor t CPUID_MMX_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_7E ip context).run s =
      (X86.Instructions.MOVQ_GPR64_MMXq (BitVec.add ip 2#64) context (modrm.extractLsb' 3 3)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_7E
  decode_modrm_form_mmx s t ip hfetch hmode hf hmmx
    (fun a c d e f =>
      selectLegacy1Opcode7E_run_of_w1_mmx_register context hosz hw hrep a c d e f modrm hmod)

end X86Proofs
