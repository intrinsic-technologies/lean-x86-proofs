import X86Proofs.Step.Sse

/-!
# Opcode `0F C3`: `MOVNTI m32/m64, r32/r64`

The one place that looks inside lean-x86's opcode-`C3` decoder (`Decode_Legacy_1_Opcode_C3`) and its
form selection (`Select_Legacy_1_Opcode_C3`), architecture rule 5. In 64-bit mode the selection
picks, for `mod ≠ 3` with SSE2: `MOVNTI_MEMd_GPR32_1` with REX.W clear and
`MOVNTI_MEMq_GPR64` with REX.W set (`Instructions/Movnti/Generated/{MR32,MR64}`). It also picks
them after `66` (without `F3`/`F2`), but the forms then raise #UD, so only the encodings without
`66` are covered. For each, a `selectLegacy1OpcodeC3_run_of_…` lemma gives the form the selection
picks, and a `decodeLegacy1OpcodeC3_run_of_…` lemma runs the decoder (from the ModRM fetch at
`ip + 1`, `ip` the second opcode byte's address) to the call of that form at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcodeC3` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod ≠ 3`, no `66` prefix, `rex_w = 0`, in 64-bit mode with SSE2: form 1,
`MOVNTI_MEMd_GPR32_1`. -/
theorem selectLegacy1OpcodeC3_run_of_w0_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (hw : context.rex_w = 0)
    (a b c e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_C3 context true a b c true e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_C3, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hw, HAnd.hAnd, AndOp.and, strictAnd,
    HOr.hOr, OrOp.or, strictOr]

/-- The opcode-C3 decoder with no `66` prefix, `rex_w = 0` and a memory ModRM (`mod ≠ 3`), with
SSE2 reported, runs `MOVNTI_MEMd_GPR32_1` from the state after the ModRM fetch, at `ip + 2`, with
the ModRM fields. -/
theorem decodeLegacy1OpcodeC3_run_of_w0_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_C3 ip context).run s =
      (X86.Instructions.MOVNTI_MEMd_GPR32_1 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_C3
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1OpcodeC3_run_of_w0_memory context hosz hw a b c e f modrm hmod)

/-- With `mod ≠ 3`, no `66` prefix, `rex_w = 1`, in 64-bit mode with SSE2: form 2,
`MOVNTI_MEMq_GPR64`. -/
theorem selectLegacy1OpcodeC3_run_of_w1_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (hw : context.rex_w = 1)
    (a b c e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_C3 context true a b c true e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_C3, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hw, HAnd.hAnd, AndOp.and, strictAnd,
    HOr.hOr, OrOp.or, strictOr]

/-- The opcode-C3 decoder with no `66` prefix, `rex_w = 1` and a memory ModRM (`mod ≠ 3`), with
SSE2 reported, runs `MOVNTI_MEMq_GPR64` from the state after the ModRM fetch, at `ip + 2`, with
the ModRM fields. -/
theorem decodeLegacy1OpcodeC3_run_of_w1_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 1) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_C3 ip context).run s =
      (X86.Instructions.MOVNTI_MEMq_GPR64 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_C3
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1OpcodeC3_run_of_w1_memory context hosz hw a b c e f modrm hmod)

end X86Proofs
