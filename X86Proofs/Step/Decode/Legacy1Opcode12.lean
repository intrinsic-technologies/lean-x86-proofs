import X86Proofs.Step.Sse

/-!
# Opcode `0F 12`: `MOVLPS`, `MOVLPD xmm, m64`, `MOVHLPS`

The one place that looks inside lean-x86's opcode-`12` decoder (`Decode_Legacy_1_Opcode_12`) and its
form selection (`Select_Legacy_1_Opcode_12`), architecture rule 5. In 64-bit mode, without a REP
prefix, the selection picks `MOVLPS_XMMq_MEMq` (no `66`, SSE, `mod ≠ 3`), `MOVLPD_XMMsd_MEMq` (`66`,
SSE2, `mod ≠ 3`) and `MOVHLPS_XMMq_XMMq` (no `66`, SSE, `mod = 3`)
(`Instructions/{Movlps,Movlpd,Movhlps}/Generated`). For each, a `selectLegacy1Opcode12_run_of_…`
lemma gives the form the selection picks, and a `decodeLegacy1Opcode12_run_of_…` lemma runs the
decoder (from the ModRM fetch at `ip + 1`, `ip` the second opcode byte's address) to the call of
that form at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcode12` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod ≠ 3`, no `66` prefix and `rep_prefix = 0`, in 64-bit mode with SSE: form 1,
`MOVLPS_XMMq_MEMq`. -/
theorem selectLegacy1Opcode12_run_of_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_12 context true a b true d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_12, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-12 decoder with no `66` prefix and `rep_prefix = 0` and a memory ModRM (`mod ≠ 3`),
with SSE reported, runs `MOVLPS_XMMq_MEMq` from the state after the ModRM fetch, at `ip + 2`, with
the ModRM fields. -/
theorem decodeLegacy1Opcode12_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_12 ip context).run s =
      (X86.Instructions.MOVLPS_XMMq_MEMq (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_12
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode12_run_of_memory context hosz hrep a b d e f
      modrm hmod)

/-- With `mod ≠ 3`, a `66` prefix and `rep_prefix = 0`, in 64-bit mode with SSE2: form 2,
`MOVLPD_XMMsd_MEMq`. -/
theorem selectLegacy1Opcode12_run_of_66_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_12 context true a b c true e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_12, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-12 decoder with a `66` prefix and `rep_prefix = 0` and a memory ModRM (`mod ≠ 3`),
with SSE2 reported, runs `MOVLPD_XMMsd_MEMq` from the state after the ModRM fetch, at `ip + 2`, with
the ModRM fields. -/
theorem decodeLegacy1Opcode12_run_of_66_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_12 ip context).run s =
      (X86.Instructions.MOVLPD_XMMsd_MEMq (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_12
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode12_run_of_66_memory context hosz hrep a b c e f
      modrm hmod)

/-- With `mod = 3`, no `66` prefix and `rep_prefix = 0`, in 64-bit mode with SSE: form 3,
`MOVHLPS_XMMq_XMMq`. -/
theorem selectLegacy1Opcode12_run_of_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_12 context true a b true d e f modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_12, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-12 decoder with no `66` prefix and `rep_prefix = 0` and a register ModRM (`mod = 3`),
with SSE reported, runs `MOVHLPS_XMMq_XMMq` from the state after the ModRM fetch, at `ip + 2`, with
the ModRM fields. -/
theorem decodeLegacy1Opcode12_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_12 ip context).run s =
      (X86.Instructions.MOVHLPS_XMMq_XMMq (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_12
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode12_run_of_register context hosz hrep a b d e f
      modrm hmod)

end X86Proofs
