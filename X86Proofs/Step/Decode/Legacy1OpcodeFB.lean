import X86Proofs.Step.Mmx

/-!
# Opcode `0F FB`: `PSUBQ`

The one place that looks inside lean-x86's opcode-`FB` decoder (`Decode_Legacy_1_Opcode_FB`) and its
form selection (`Select_Legacy_1_Opcode_FB`), architecture rule 5. In 64-bit mode the selection
picks, after `66` and with SSE2, `PSUBQ_XMMdq_XMMdq` for `mod = 3` and `PSUBQ_XMMdq_MEMdq` otherwise
(`Instructions/Psubq/Generated/{XX,XM}`). Without `66`, with MMX, it picks the MMX forms
(`Instructions/Psubq/Generated/{MM,MMem}`). For each, a `selectLegacy1OpcodeFB_run_of_…` lemma gives
the form the selection picks, and a `decodeLegacy1OpcodeFB_run_of_…` lemma runs the decoder (from
the ModRM fetch at `ip + 1`, `ip` the second opcode byte's address) to the call of that form at
`ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcodeFB` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod ≠ 3` and a `66` prefix in 64-bit mode, with SSE2: form 3, `PSUBQ_XMMdq_MEMdq`. -/
theorem selectLegacy1OpcodeFB_run_of_66_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_FB context true a b c true e f modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_FB, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-FB decoder with a `66` prefix and a memory ModRM (`mod ≠ 3`), with SSE2 reported,
runs `PSUBQ_XMMdq_MEMdq` from the state after the ModRM fetch, at `ip + 2`, with the ModRM fields.
-/
theorem decodeLegacy1OpcodeFB_run_of_66_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_FB ip context).run s =
      (X86.Instructions.PSUBQ_XMMdq_MEMdq (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_FB
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1OpcodeFB_run_of_66_memory context hosz a b c e f modrm hmod)

/-- With `mod = 3` and a `66` prefix in 64-bit mode, with SSE2: form 4, `PSUBQ_XMMdq_XMMdq`. -/
theorem selectLegacy1OpcodeFB_run_of_66_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_FB context true a b c true e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_FB, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-FB decoder with a `66` prefix and a register ModRM (`mod = 3`), with SSE2 reported,
runs `PSUBQ_XMMdq_XMMdq` from the state after the ModRM fetch, at `ip + 2`, with the ModRM fields.
-/
theorem decodeLegacy1OpcodeFB_run_of_66_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_FB ip context).run s =
      (X86.Instructions.PSUBQ_XMMdq_XMMdq (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_FB
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1OpcodeFB_run_of_66_register context hosz a b c e f modrm hmod)

/-- With `mod = 3` and no `66` prefix in 64-bit mode, with MMX and SSE2: form 2, `PSUBQ_MMXq_MMXq`.
-/
theorem selectLegacy1OpcodeFB_run_of_mmx_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (a c e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_FB context true a true c true e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_FB, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-FB decoder with no `66` prefix and a register ModRM (`mod = 3`), with MMX and SSE2
reported, runs `PSUBQ_MMXq_MMXq` from the state after the ModRM fetch, at `ip + 2`, with the ModRM
fields. -/
theorem decodeLegacy1OpcodeFB_run_of_mmx_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor t CPUID_MMX_Encoding true)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_FB ip context).run s =
      (X86.Instructions.PSUBQ_MMXq_MMXq (BitVec.add ip 2#64) context (modrm.extractLsb' 3 3)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_FB
  decode_modrm_form_mmx_sse2 s t ip hfetch hmode hf hmmx hsse2
    (fun a c e f =>
      selectLegacy1OpcodeFB_run_of_mmx_register context hosz a c e f modrm hmod)

/-- With `mod ≠ 3` and no `66` prefix in 64-bit mode, with MMX and SSE2: form 1, `PSUBQ_MMXq_MEMq`.
-/
theorem selectLegacy1OpcodeFB_run_of_mmx_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (a c e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_FB context true a true c true e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_FB, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-FB decoder with no `66` prefix and a memory ModRM (`mod ≠ 3`), with MMX and SSE2
reported, runs `PSUBQ_MMXq_MEMq` from the state after the ModRM fetch, at `ip + 2`, with the ModRM
fields. -/
theorem decodeLegacy1OpcodeFB_run_of_mmx_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor t CPUID_MMX_Encoding true)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_FB ip context).run s =
      (X86.Instructions.PSUBQ_MMXq_MEMq (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_FB
  decode_modrm_form_mmx_sse2 s t ip hfetch hmode hf hmmx hsse2
    (fun a c e f =>
      selectLegacy1OpcodeFB_run_of_mmx_memory context hosz a c e f modrm hmod)

end X86Proofs
