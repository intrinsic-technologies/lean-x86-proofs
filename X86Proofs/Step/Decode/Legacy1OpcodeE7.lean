import X86Proofs.Step.Mmx

/-!
# Opcode `0F E7`: `MOVNTDQ m128, xmm`, `MOVNTQ m64, mm`

The one place that looks inside lean-x86's opcode-`E7` decoder (`Decode_Legacy_1_Opcode_E7`) and its
form selection (`Select_Legacy_1_Opcode_E7`), architecture rule 5. In 64-bit mode the selection
picks, for `mod ≠ 3` after `66` with SSE2, `MOVNTDQ_MEMdq_XMMdq`
(`Instructions/Movntdq/Generated/MX`), and without `66`, with MMX, the MMX form `MOVNTQ_MEMq_MMXq`
(`Instructions/Movntq/Generated/MemM`). The `selectLegacy1OpcodeE7_run_of_…` lemmas give the form
the selection picks, and the `decodeLegacy1OpcodeE7_run_of_…` lemmas run the decoder (from the ModRM
fetch at `ip + 1`, `ip` the second opcode byte's address) to the call of that form at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcodeE7` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod ≠ 3`, a `66` prefix, in 64-bit mode with SSE2: form 1, `MOVNTDQ_MEMdq_XMMdq`. -/
theorem selectLegacy1OpcodeE7_run_of_66_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (a b c e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_E7 context true a b c true e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_E7, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-E7 decoder with a `66` prefix and a memory ModRM (`mod ≠ 3`), with SSE2 reported,
runs `MOVNTDQ_MEMdq_XMMdq` from the state after the ModRM fetch, at `ip + 2`, with the ModRM
fields. -/
theorem decodeLegacy1OpcodeE7_run_of_66_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_E7 ip context).run s =
      (X86.Instructions.MOVNTDQ_MEMdq_XMMdq (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_E7
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1OpcodeE7_run_of_66_memory context hosz a b c e f modrm hmod)

/-- With `mod ≠ 3` and no `66` prefix in 64-bit mode, with MMX: form 2, `MOVNTQ_MEMq_MMXq`. -/
theorem selectLegacy1OpcodeE7_run_of_mmx_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (a c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_E7 context true a true c d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_E7, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-E7 decoder with no `66` prefix and a memory ModRM (`mod ≠ 3`), with MMX reported,
runs `MOVNTQ_MEMq_MMXq` from the state after the ModRM fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1OpcodeE7_run_of_mmx_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor t CPUID_MMX_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_E7 ip context).run s =
      (X86.Instructions.MOVNTQ_MEMq_MMXq (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_E7
  decode_modrm_form_mmx s t ip hfetch hmode hf hmmx
    (fun a c d e f =>
      selectLegacy1OpcodeE7_run_of_mmx_memory context hosz a c d e f modrm hmod)

end X86Proofs
