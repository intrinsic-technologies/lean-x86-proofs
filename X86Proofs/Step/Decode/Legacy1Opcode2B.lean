import X86Proofs.Step.Sse

/-!
# Opcode `0F 2B`: `MOVNTPS`, `MOVNTPD m128, xmm`

The one place that looks inside lean-x86's opcode-`2B` decoder (`Decode_Legacy_1_Opcode_2B`) and its
form selection (`Select_Legacy_1_Opcode_2B`), architecture rule 5. In 64-bit mode the selection
picks, for `mod ≠ 3` only: without `66` and with SSE, `MOVNTPS_MEMdq_XMMps`; after `66` with SSE2,
`MOVNTPD_MEMdq_XMMpd` (`Instructions/{Movntps,Movntpd}/Generated/MX`). For each, a
`selectLegacy1Opcode2B_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy1Opcode2B_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`, `ip`
the second opcode byte's address) to the call of that form at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcode2B` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod ≠ 3`, no `66` prefix, in 64-bit mode with SSE: form 2, `MOVNTPS_MEMdq_XMMps`. -/
theorem selectLegacy1Opcode2B_run_of_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (a b d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_2B context true a b true d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_2B, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-2B decoder with no `66` prefix and a memory ModRM (`mod ≠ 3`), with SSE reported,
runs `MOVNTPS_MEMdq_XMMps` from the state after the ModRM fetch, at `ip + 2`, with the ModRM
fields. -/
theorem decodeLegacy1Opcode2B_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2B ip context).run s =
      (X86.Instructions.MOVNTPS_MEMdq_XMMps (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2B
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode2B_run_of_memory context hosz a b d e f modrm hmod)

/-- With `mod ≠ 3`, a `66` prefix, in 64-bit mode with SSE2: form 1, `MOVNTPD_MEMdq_XMMpd`. -/
theorem selectLegacy1Opcode2B_run_of_66_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (a b c e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_2B context true a b c true e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_2B, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-2B decoder with a `66` prefix and a memory ModRM (`mod ≠ 3`), with SSE2 reported,
runs `MOVNTPD_MEMdq_XMMpd` from the state after the ModRM fetch, at `ip + 2`, with the ModRM
fields. -/
theorem decodeLegacy1Opcode2B_run_of_66_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2B ip context).run s =
      (X86.Instructions.MOVNTPD_MEMdq_XMMpd (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2B
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode2B_run_of_66_memory context hosz a b c e f modrm hmod)

end X86Proofs
