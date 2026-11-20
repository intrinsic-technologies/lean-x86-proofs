import X86Proofs.Step.Sse

/-!
# Opcode `0F 2A`: `CVTSI2SS`, `CVTSI2SD`, `CVTPI2PS`, `CVTPI2PD`

The one place that looks inside lean-x86's opcode-`2A` decoder (`Decode_Legacy_1_Opcode_2A`) and its
form selection (`Select_Legacy_1_Opcode_2A`), architecture rule 5. For each form the library uses, a
`selectLegacy1Opcode2A_run_of_…` lemma gives the form the selection picks (by the REP prefix, REX.W,
`mod`, and the CPUID feature it requires), and a `decodeLegacy1Opcode2A_run_of_…` lemma runs the
decoder (from the ModRM fetch at `ip + 1`, `ip` the second opcode byte's address) to the call of
that form at `ip + 2`. The `NP` and `66` forms are CVTPI2PS and CVTPI2PD: with `mod = 3` (`xmm,
mm`, `Instructions/{Cvtpi2ps,Cvtpi2pd}/Generated/XMm`) they read MMX registers, with a memory
operand (`xmm, m64`, `…/Generated/XM`) 64 bits of memory.

The dispatch to this decoder is `decodeLegacy1_run_of_opcode2A` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3`, an `F3` prefix (`rep_prefix = 243`), REX.W clear, in 64-bit mode with SSE: form
1, `CVTSI2SS_XMMss_GPR32d`. -/
theorem selectLegacy1Opcode2A_run_of_f3_w0_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hw : context.rex_w = 0)
    (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_2A context true a b true d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_2A, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`2A` decoder with an `F3` prefix (`rep_prefix = 243`), REX.W clear and a register
ModRM (`mod = 3`), with SSE reported, runs `CVTSI2SS_XMMss_GPR32d` from the state after the ModRM
fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode2A_run_of_f3_w0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hw : context.rex_w = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2A ip context).run s =
      (X86.Instructions.CVTSI2SS_XMMss_GPR32d (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2A
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode2A_run_of_f3_w0_register context hrep hw a b d e f modrm
      hmod)

/-- With `mod = 3`, an `F3` prefix (`rep_prefix = 243`), REX.W set, in 64-bit mode with SSE: form 2,
`CVTSI2SS_XMMss_GPR64q`. -/
theorem selectLegacy1Opcode2A_run_of_f3_w1_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hw : context.rex_w = 1)
    (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_2A context true a b true d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_2A, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`2A` decoder with an `F3` prefix (`rep_prefix = 243`), REX.W set and a register ModRM
(`mod = 3`), with SSE reported, runs `CVTSI2SS_XMMss_GPR64q` from the state after the ModRM fetch,
at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode2A_run_of_f3_w1_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hw : context.rex_w = 1)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2A ip context).run s =
      (X86.Instructions.CVTSI2SS_XMMss_GPR64q (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2A
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode2A_run_of_f3_w1_register context hrep hw a b d e f modrm
      hmod)

/-- With `mod ≠ 3`, an `F3` prefix (`rep_prefix = 243`), REX.W clear, in 64-bit mode with SSE: form
3, `CVTSI2SS_XMMss_MEMd`. -/
theorem selectLegacy1Opcode2A_run_of_f3_w0_memory (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hw : context.rex_w = 0)
    (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_2A context true a b true d e f modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_2A, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`2A` decoder with an `F3` prefix (`rep_prefix = 243`), REX.W clear and a memory ModRM
(`mod ≠ 3`), with SSE reported, runs `CVTSI2SS_XMMss_MEMd` from the state after the ModRM fetch, at
`ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode2A_run_of_f3_w0_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hw : context.rex_w = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2A ip context).run s =
      (X86.Instructions.CVTSI2SS_XMMss_MEMd (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2A
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode2A_run_of_f3_w0_memory context hrep hw a b d e f modrm
      hmod)

/-- With `mod ≠ 3`, an `F3` prefix (`rep_prefix = 243`), REX.W set, in 64-bit mode with SSE: form 4,
`CVTSI2SS_XMMss_MEMq`. -/
theorem selectLegacy1Opcode2A_run_of_f3_w1_memory (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hw : context.rex_w = 1)
    (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_2A context true a b true d e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_2A, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`2A` decoder with an `F3` prefix (`rep_prefix = 243`), REX.W set and a memory ModRM
(`mod ≠ 3`), with SSE reported, runs `CVTSI2SS_XMMss_MEMq` from the state after the ModRM fetch, at
`ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode2A_run_of_f3_w1_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hw : context.rex_w = 1)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2A ip context).run s =
      (X86.Instructions.CVTSI2SS_XMMss_MEMq (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2A
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode2A_run_of_f3_w1_memory context hrep hw a b d e f modrm
      hmod)

/-- With `mod = 3`, an `F2` prefix (`rep_prefix = 242`), REX.W clear, in 64-bit mode with SSE2: form
5, `CVTSI2SD_XMMsd_GPR32d`. -/
theorem selectLegacy1Opcode2A_run_of_f2_w0_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (hw : context.rex_w = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_2A context true a b c true e f modrm = .ok 5 := by
  simp [Select_Legacy_1_Opcode_2A, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`2A` decoder with an `F2` prefix (`rep_prefix = 242`), REX.W clear and a register
ModRM (`mod = 3`), with SSE2 reported, runs `CVTSI2SD_XMMsd_GPR32d` from the state after the ModRM
fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode2A_run_of_f2_w0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (hw : context.rex_w = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2A ip context).run s =
      (X86.Instructions.CVTSI2SD_XMMsd_GPR32d (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2A
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode2A_run_of_f2_w0_register context hrep hw a b c e f modrm
      hmod)

/-- With `mod = 3`, an `F2` prefix (`rep_prefix = 242`), REX.W set, in 64-bit mode with SSE2: form
6, `CVTSI2SD_XMMsd_GPR64q`. -/
theorem selectLegacy1Opcode2A_run_of_f2_w1_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (hw : context.rex_w = 1)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_2A context true a b c true e f modrm = .ok 6 := by
  simp [Select_Legacy_1_Opcode_2A, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`2A` decoder with an `F2` prefix (`rep_prefix = 242`), REX.W set and a register ModRM
(`mod = 3`), with SSE2 reported, runs `CVTSI2SD_XMMsd_GPR64q` from the state after the ModRM fetch,
at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode2A_run_of_f2_w1_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (hw : context.rex_w = 1)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2A ip context).run s =
      (X86.Instructions.CVTSI2SD_XMMsd_GPR64q (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2A
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode2A_run_of_f2_w1_register context hrep hw a b c e f modrm
      hmod)

/-- With `mod ≠ 3`, an `F2` prefix (`rep_prefix = 242`), REX.W clear, in 64-bit mode with SSE2: form
7, `CVTSI2SD_XMMsd_MEMd`. -/
theorem selectLegacy1Opcode2A_run_of_f2_w0_memory (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (hw : context.rex_w = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_2A context true a b c true e f modrm = .ok 7 := by
  simp [Select_Legacy_1_Opcode_2A, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`2A` decoder with an `F2` prefix (`rep_prefix = 242`), REX.W clear and a memory ModRM
(`mod ≠ 3`), with SSE2 reported, runs `CVTSI2SD_XMMsd_MEMd` from the state after the ModRM fetch, at
`ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode2A_run_of_f2_w0_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (hw : context.rex_w = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2A ip context).run s =
      (X86.Instructions.CVTSI2SD_XMMsd_MEMd (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2A
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode2A_run_of_f2_w0_memory context hrep hw a b c e f modrm
      hmod)

/-- With `mod ≠ 3`, an `F2` prefix (`rep_prefix = 242`), REX.W set, in 64-bit mode with SSE2: form
8, `CVTSI2SD_XMMsd_MEMq`. -/
theorem selectLegacy1Opcode2A_run_of_f2_w1_memory (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (hw : context.rex_w = 1)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_2A context true a b c true e f modrm = .ok 8 := by
  simp [Select_Legacy_1_Opcode_2A, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`2A` decoder with an `F2` prefix (`rep_prefix = 242`), REX.W set and a memory ModRM
(`mod ≠ 3`), with SSE2 reported, runs `CVTSI2SD_XMMsd_MEMq` from the state after the ModRM fetch, at
`ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode2A_run_of_f2_w1_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (hw : context.rex_w = 1)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2A ip context).run s =
      (X86.Instructions.CVTSI2SD_XMMsd_MEMq (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2A
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode2A_run_of_f2_w1_memory context hrep hw a b c e f modrm
      hmod)

/-- With `mod = 3` and no `66` prefix, `rep_prefix = 0` in 64-bit mode, with SSE: form 12,
`CVTPI2PS_XMMq_MMXq`. -/
theorem selectLegacy1Opcode2A_run_of_mmx_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (hrep : context.rep_prefix = 0)
    (a b d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_2A context true a b true d e f modrm = .ok 12 := by
  simp [Select_Legacy_1_Opcode_2A, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-2A decoder with no `66` prefix, `rep_prefix = 0` and a register ModRM (`mod = 3`),
with SSE reported, runs `CVTPI2PS_XMMq_MMXq` from the state after the ModRM fetch, at `ip + 2`, with
the ModRM fields. -/
theorem decodeLegacy1Opcode2A_run_of_mmx_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2A ip context).run s =
      (X86.Instructions.CVTPI2PS_XMMq_MMXq (BitVec.add ip 2#64) context (modrm.extractLsb' 3 3)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2A
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f =>
      selectLegacy1Opcode2A_run_of_mmx_register context hosz hrep a b d e f modrm hmod)

/-- With `mod = 3` and a `66` prefix, `rep_prefix = 0` in 64-bit mode, with SSE2: form 10,
`CVTPI2PD_XMMpd_MMXq`. -/
theorem selectLegacy1Opcode2A_run_of_66_mmx_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_2A context true a b c true e f modrm = .ok 10 := by
  simp [Select_Legacy_1_Opcode_2A, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-2A decoder with a `66` prefix, `rep_prefix = 0` and a register ModRM (`mod = 3`),
with SSE2 reported, runs `CVTPI2PD_XMMpd_MMXq` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1Opcode2A_run_of_66_mmx_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2A ip context).run s =
      (X86.Instructions.CVTPI2PD_XMMpd_MMXq (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2A
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f =>
      selectLegacy1Opcode2A_run_of_66_mmx_register context hosz hrep a b c e f modrm hmod)


/-- With `mod ≠ 3`, no `66` prefix, `rep_prefix = 0` in 64-bit mode, with SSE: form 11,
`CVTPI2PS_XMMq_MEMq`. -/
theorem selectLegacy1Opcode2A_run_of_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (hrep : context.rep_prefix = 0)
    (a b d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_2A context true a b true d e f modrm = .ok 11 := by
  simp [Select_Legacy_1_Opcode_2A, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-2A decoder with no `66` prefix, `rep_prefix = 0` and a memory ModRM (`mod ≠ 3`),
with SSE reported, runs `CVTPI2PS_XMMq_MEMq` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1Opcode2A_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2A ip context).run s =
      (X86.Instructions.CVTPI2PS_XMMq_MEMq (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2A
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f =>
      selectLegacy1Opcode2A_run_of_memory context hosz hrep a b d e f modrm hmod)

/-- With `mod ≠ 3` and a `66` prefix, `rep_prefix = 0` in 64-bit mode, with SSE2: form 9,
`CVTPI2PD_XMMpd_MEMq`. -/
theorem selectLegacy1Opcode2A_run_of_66_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_2A context true a b c true e f modrm = .ok 9 := by
  simp [Select_Legacy_1_Opcode_2A, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-2A decoder with a `66` prefix, `rep_prefix = 0` and a memory ModRM (`mod ≠ 3`),
with SSE2 reported, runs `CVTPI2PD_XMMpd_MEMq` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1Opcode2A_run_of_66_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2A ip context).run s =
      (X86.Instructions.CVTPI2PD_XMMpd_MEMq (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2A
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f =>
      selectLegacy1Opcode2A_run_of_66_memory context hosz hrep a b c e f modrm hmod)

end X86Proofs
