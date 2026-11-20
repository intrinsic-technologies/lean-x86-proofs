import X86Proofs.Step.Mmx

/-!
# Opcode `0F 6E`: `MOVD`/`MOVQ xmm, r/m` and `mm, r/m`

The one place that looks inside lean-x86's opcode-`6E` decoder (`Decode_Legacy_1_Opcode_6E`) and its
form selection (`Select_Legacy_1_Opcode_6E`), architecture rule 5. In 64-bit mode the selection
picks `MOVD_XMMdq_GPR32_0` after `66` without REX.W and `MOVQ_XMMdq_GPR64` after `66` with REX.W,
for `mod = 3`, with SSE2 (`Instructions/Movd/Generated/XR`, `Instructions/Movq/Generated/XR`), and
`MOVD_XMMdq_MEMd_1` / `MOVQ_XMMdq_MEMq_0F6E_0` for `mod ≠ 3` (`Instructions/Movd/Generated/XM`,
`Instructions/Movq/Generated/XM6E`). Without `66`, with MMX, it picks the MMX forms
`MOVD_MMXq_GPR32_0` / `MOVQ_MMXq_GPR64` (`mod = 3`, by REX.W;
`Instructions/{Movd,Movq}/Generated/{MR32,MR64}`) and `MOVD_MMXq_MEMd_0` / `MOVQ_MMXq_MEMq_0F6E`
(`Instructions/Movd/Generated/MMem`, `Instructions/Movq/Generated/MMem6E`). For each, a
`selectLegacy1Opcode6E_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy1Opcode6E_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`, `ip` the
second opcode byte's address) to the call of that form at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcode6E` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` and a `66` prefix, `rex_w = 0` in 64-bit mode, with SSE2: form 5,
`MOVD_XMMdq_GPR32_0`. -/
theorem selectLegacy1Opcode6E_run_of_66_w0_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_6E context true a b c true e f modrm = .ok 5 := by
  simp [Select_Legacy_1_Opcode_6E, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-6E decoder with a `66` prefix, `rex_w = 0` and a register ModRM (`mod = 3`), with
SSE2 reported, runs `MOVD_XMMdq_GPR32_0` from the state after the ModRM fetch, at `ip + 2`, with the
ModRM fields. -/
theorem decodeLegacy1Opcode6E_run_of_66_w0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_6E ip context).run s =
      (X86.Instructions.MOVD_XMMdq_GPR32_0 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_6E
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode6E_run_of_66_w0_register context hosz hw a b c e f
      modrm hmod)

/-- With `mod = 3` and a `66` prefix, `rex_w = 1` in 64-bit mode, with SSE2: form 7,
`MOVQ_XMMdq_GPR64`. -/
theorem selectLegacy1Opcode6E_run_of_66_w1_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 1)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_6E context true a b c true e f modrm = .ok 7 := by
  simp [Select_Legacy_1_Opcode_6E, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-6E decoder with a `66` prefix, `rex_w = 1` and a register ModRM (`mod = 3`), with
SSE2 reported, runs `MOVQ_XMMdq_GPR64` from the state after the ModRM fetch, at `ip + 2`, with the
ModRM fields. -/
theorem decodeLegacy1Opcode6E_run_of_66_w1_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 1)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_6E ip context).run s =
      (X86.Instructions.MOVQ_XMMdq_GPR64 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_6E
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode6E_run_of_66_w1_register context hosz hw a b c e f
      modrm hmod)

/-- With `mod ≠ 3`, a `66` prefix and `rex_w = 0`, in 64-bit mode with SSE2: form 6,
`MOVD_XMMdq_MEMd_1`. -/
theorem selectLegacy1Opcode6E_run_of_66_w0_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_6E context true a b c true e f modrm = .ok 6 := by
  simp [Select_Legacy_1_Opcode_6E, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-6E decoder with a `66` prefix and `rex_w = 0` and a memory ModRM (`mod ≠ 3`), with
SSE2 reported, runs `MOVD_XMMdq_MEMd_1` from the state after the ModRM fetch, at `ip + 2`, with the
ModRM fields. -/
theorem decodeLegacy1Opcode6E_run_of_66_w0_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_6E ip context).run s =
      (X86.Instructions.MOVD_XMMdq_MEMd_1 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_6E
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode6E_run_of_66_w0_memory context hosz hw a b c e f
      modrm hmod)

/-- With `mod ≠ 3`, a `66` prefix and `rex_w = 1`, in 64-bit mode with SSE2: form 8,
`MOVQ_XMMdq_MEMq_0F6E_0`. -/
theorem selectLegacy1Opcode6E_run_of_66_w1_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 1)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_6E context true a b c true e f modrm = .ok 8 := by
  simp [Select_Legacy_1_Opcode_6E, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-6E decoder with a `66` prefix and `rex_w = 1` and a memory ModRM (`mod ≠ 3`), with
SSE2 reported, runs `MOVQ_XMMdq_MEMq_0F6E_0` from the state after the ModRM fetch, at `ip + 2`, with
the ModRM fields. -/
theorem decodeLegacy1Opcode6E_run_of_66_w1_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 1)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_6E ip context).run s =
      (X86.Instructions.MOVQ_XMMdq_MEMq_0F6E_0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_6E
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode6E_run_of_66_w1_memory context hosz hw a b c e f
      modrm hmod)

/-- With `mod ≠ 3` and no `66` prefix, REX.W = 1 in 64-bit mode, with MMX: form 4,
`MOVQ_MMXq_MEMq_0F6E`. -/
theorem selectLegacy1Opcode6E_run_of_w1_mmx_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (hw : context.rex_w = 1)
    (a c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_6E context true a true c d e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_6E, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-6E decoder with no `66` prefix, REX.W = 1 and a memory ModRM (`mod ≠ 3`), with MMX
reported, runs `MOVQ_MMXq_MEMq_0F6E` from the state after the ModRM fetch, at `ip + 2`, with the
ModRM fields. -/
theorem decodeLegacy1Opcode6E_run_of_w1_mmx_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 1)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor t CPUID_MMX_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_6E ip context).run s =
      (X86.Instructions.MOVQ_MMXq_MEMq_0F6E (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_6E
  decode_modrm_form_mmx s t ip hfetch hmode hf hmmx
    (fun a c d e f =>
      selectLegacy1Opcode6E_run_of_w1_mmx_memory context hosz hw a c d e f modrm hmod)

/-- With `mod = 3` and no `66` prefix, REX.W = 1 in 64-bit mode, with MMX: form 3,
`MOVQ_MMXq_GPR64`. -/
theorem selectLegacy1Opcode6E_run_of_w1_mmx_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (hw : context.rex_w = 1)
    (a c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_6E context true a true c d e f modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_6E, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-6E decoder with no `66` prefix, REX.W = 1 and a register ModRM (`mod = 3`), with MMX
reported, runs `MOVQ_MMXq_GPR64` from the state after the ModRM fetch, at `ip + 2`, with the ModRM
fields. -/
theorem decodeLegacy1Opcode6E_run_of_w1_mmx_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 1)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor t CPUID_MMX_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_6E ip context).run s =
      (X86.Instructions.MOVQ_MMXq_GPR64 (BitVec.add ip 2#64) context (modrm.extractLsb' 3 3)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_6E
  decode_modrm_form_mmx s t ip hfetch hmode hf hmmx
    (fun a c d e f =>
      selectLegacy1Opcode6E_run_of_w1_mmx_register context hosz hw a c d e f modrm hmod)

/-- With `mod ≠ 3` and no `66` prefix, REX.W = 0 in 64-bit mode, with MMX: form 2,
`MOVD_MMXq_MEMd_0`. -/
theorem selectLegacy1Opcode6E_run_of_w0_mmx_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (hw : context.rex_w = 0)
    (a c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_6E context true a true c d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_6E, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-6E decoder with no `66` prefix, REX.W = 0 and a memory ModRM (`mod ≠ 3`), with MMX
reported, runs `MOVD_MMXq_MEMd_0` from the state after the ModRM fetch, at `ip + 2`, with the ModRM
fields. -/
theorem decodeLegacy1Opcode6E_run_of_w0_mmx_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor t CPUID_MMX_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_6E ip context).run s =
      (X86.Instructions.MOVD_MMXq_MEMd_0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_6E
  decode_modrm_form_mmx s t ip hfetch hmode hf hmmx
    (fun a c d e f =>
      selectLegacy1Opcode6E_run_of_w0_mmx_memory context hosz hw a c d e f modrm hmod)

/-- With `mod = 3` and no `66` prefix, REX.W = 0 in 64-bit mode, with MMX: form 1,
`MOVD_MMXq_GPR32_0`. -/
theorem selectLegacy1Opcode6E_run_of_w0_mmx_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (hw : context.rex_w = 0)
    (a c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_6E context true a true c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_6E, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-6E decoder with no `66` prefix, REX.W = 0 and a register ModRM (`mod = 3`), with MMX
reported, runs `MOVD_MMXq_GPR32_0` from the state after the ModRM fetch, at `ip + 2`, with the ModRM
fields. -/
theorem decodeLegacy1Opcode6E_run_of_w0_mmx_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor t CPUID_MMX_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_6E ip context).run s =
      (X86.Instructions.MOVD_MMXq_GPR32_0 (BitVec.add ip 2#64) context (modrm.extractLsb' 3 3)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_6E
  decode_modrm_form_mmx s t ip hfetch hmode hf hmmx
    (fun a c d e f =>
      selectLegacy1Opcode6E_run_of_w0_mmx_register context hosz hw a c d e f modrm hmod)

end X86Proofs
