import X86Proofs.Step.Sse

/-!
# Opcode `0F 56`: `ORPS`, `ORPD`

The one place that looks inside lean-x86's opcode-`56` decoder (`Decode_Legacy_1_Opcode_56`) and its
form selection (`Select_Legacy_1_Opcode_56`), architecture rule 5. In 64-bit mode the selection
picks, without `66` and with SSE, `ORPS_XMMxud_XMMxud` for `mod = 3` and `ORPS_XMMxud_MEMxud`
otherwise (`Instructions/Orps/Generated/{XX,XM}`); after `66` and with SSE2, `ORPD_XMMxuq_XMMxuq`
for `mod = 3` and `ORPD_XMMxuq_MEMxuq` otherwise (`Instructions/Orpd/Generated/{XX,XM}`). For each,
a `selectLegacy1Opcode56_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy1Opcode56_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`, `ip` the
second opcode byte's address) to the call of that form at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcode56` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod ≠ 3` and no `66` prefix in 64-bit mode, with SSE: form 1, `ORPS_XMMxud_MEMxud`. -/
theorem selectLegacy1Opcode56_run_of_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_56 context true a b true d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_56, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-56 decoder with no `66` prefix and a memory ModRM (`mod ≠ 3`), with SSE reported,
runs `ORPS_XMMxud_MEMxud` from the state after the ModRM fetch, at `ip + 2`, with the ModRM fields.
-/
theorem decodeLegacy1Opcode56_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_56 ip context).run s =
      (X86.Instructions.ORPS_XMMxud_MEMxud (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_56
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode56_run_of_memory context hosz a b d e f modrm hmod)

/-- With `mod = 3` and no `66` prefix in 64-bit mode, with SSE: form 2, `ORPS_XMMxud_XMMxud`. -/
theorem selectLegacy1Opcode56_run_of_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_56 context true a b true d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_56, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-56 decoder with no `66` prefix and a register ModRM (`mod = 3`), with SSE reported,
runs `ORPS_XMMxud_XMMxud` from the state after the ModRM fetch, at `ip + 2`, with the ModRM fields.
-/
theorem decodeLegacy1Opcode56_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_56 ip context).run s =
      (X86.Instructions.ORPS_XMMxud_XMMxud (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_56
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode56_run_of_register context hosz a b d e f modrm hmod)

/-- With `mod ≠ 3` and a `66` prefix in 64-bit mode, with SSE2: form 3, `ORPD_XMMxuq_MEMxuq`. -/
theorem selectLegacy1Opcode56_run_of_66_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_56 context true a b c true e f modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_56, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-56 decoder with a `66` prefix and a memory ModRM (`mod ≠ 3`), with SSE2 reported,
runs `ORPD_XMMxuq_MEMxuq` from the state after the ModRM fetch, at `ip + 2`, with the ModRM fields.
-/
theorem decodeLegacy1Opcode56_run_of_66_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_56 ip context).run s =
      (X86.Instructions.ORPD_XMMxuq_MEMxuq (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_56
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode56_run_of_66_memory context hosz a b c e f modrm hmod)

/-- With `mod = 3` and a `66` prefix in 64-bit mode, with SSE2: form 4, `ORPD_XMMxuq_XMMxuq`. -/
theorem selectLegacy1Opcode56_run_of_66_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_56 context true a b c true e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_56, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-56 decoder with a `66` prefix and a register ModRM (`mod = 3`), with SSE2 reported,
runs `ORPD_XMMxuq_XMMxuq` from the state after the ModRM fetch, at `ip + 2`, with the ModRM fields.
-/
theorem decodeLegacy1Opcode56_run_of_66_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_56 ip context).run s =
      (X86.Instructions.ORPD_XMMxuq_XMMxuq (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_56
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode56_run_of_66_register context hosz a b c e f modrm hmod)

end X86Proofs
