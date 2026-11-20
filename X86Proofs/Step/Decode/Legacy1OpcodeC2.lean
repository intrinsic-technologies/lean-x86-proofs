import X86Proofs.Step.Sse

/-!
# Opcode `0F C2`: `CMPPS`, `CMPPD`, `CMPSS`, `CMPSD` with an immediate predicate

The one place that looks inside lean-x86's opcode-`C2` decoder (`Decode_Legacy_1_Opcode_C2`) and
its form selection (`Select_Legacy_1_Opcode_C2`), architecture rule 5. For each form the library
uses, a `selectLegacy1OpcodeC2_run_of_…` lemma gives the form the selection picks (by the `66` and
REP prefixes, `mod`, and the CPUID feature it requires), and a `decodeLegacy1OpcodeC2_run_of_…`
lemma runs the decoder (from the ModRM fetch at `ip + 1`, `ip` the second opcode byte's address)
to the call of that form at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcodeC2` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod ≠ 3`, no `66` or REP prefix, in 64-bit mode with SSE: form 1,
`CMPPS_XMMps_MEMps_IMMb`. -/
theorem selectLegacy1OpcodeC2_run_of_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_C2 context true a b true d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_C2, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`C2` decoder with no `66` or REP prefix and a memory ModRM (`mod ≠ 3`),
with SSE reported, runs `CMPPS_XMMps_MEMps_IMMb` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1OpcodeC2_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_C2 ip context).run s =
      (X86.Instructions.CMPPS_XMMps_MEMps_IMMb (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_C2
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1OpcodeC2_run_of_memory context hosz hrep a b d e f
      modrm hmod)

/-- With `mod = 3`, no `66` or REP prefix, in 64-bit mode with SSE: form 2,
`CMPPS_XMMps_XMMps_IMMb`. -/
theorem selectLegacy1OpcodeC2_run_of_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_C2 context true a b true d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_C2, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`C2` decoder with no `66` or REP prefix and a register ModRM (`mod = 3`),
with SSE reported, runs `CMPPS_XMMps_XMMps_IMMb` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1OpcodeC2_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_C2 ip context).run s =
      (X86.Instructions.CMPPS_XMMps_XMMps_IMMb (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_C2
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1OpcodeC2_run_of_register context hosz hrep a b d e f
      modrm hmod)

/-- With `mod ≠ 3`, a `66` prefix and no REP prefix, in 64-bit mode with SSE2: form 3,
`CMPPD_XMMpd_MEMpd_IMMb`. -/
theorem selectLegacy1OpcodeC2_run_of_66_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_C2 context true a b c true e f modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_C2, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`C2` decoder with a `66` prefix and no REP prefix and a memory ModRM (`mod ≠ 3`),
with SSE2 reported, runs `CMPPD_XMMpd_MEMpd_IMMb` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1OpcodeC2_run_of_66_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_C2 ip context).run s =
      (X86.Instructions.CMPPD_XMMpd_MEMpd_IMMb (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_C2
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1OpcodeC2_run_of_66_memory context hosz hrep a b c e f
      modrm hmod)

/-- With `mod = 3`, a `66` prefix and no REP prefix, in 64-bit mode with SSE2: form 4,
`CMPPD_XMMpd_XMMpd_IMMb`. -/
theorem selectLegacy1OpcodeC2_run_of_66_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_C2 context true a b c true e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_C2, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`C2` decoder with a `66` prefix and no REP prefix and a register ModRM (`mod = 3`),
with SSE2 reported, runs `CMPPD_XMMpd_XMMpd_IMMb` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1OpcodeC2_run_of_66_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_C2 ip context).run s =
      (X86.Instructions.CMPPD_XMMpd_XMMpd_IMMb (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_C2
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1OpcodeC2_run_of_66_register context hosz hrep a b c e f
      modrm hmod)

/-- With `mod ≠ 3`, an `F3` prefix (`rep_prefix = 243`), in 64-bit mode with SSE: form 5,
`CMPSS_XMMss_MEMss_IMMb`. -/
theorem selectLegacy1OpcodeC2_run_of_f3_memory (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_C2 context true a b true d e f modrm = .ok 5 := by
  simp [Select_Legacy_1_Opcode_C2, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`C2` decoder with an `F3` prefix (`rep_prefix = 243`) and a memory ModRM (`mod ≠ 3`),
with SSE reported, runs `CMPSS_XMMss_MEMss_IMMb` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1OpcodeC2_run_of_f3_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_C2 ip context).run s =
      (X86.Instructions.CMPSS_XMMss_MEMss_IMMb (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_C2
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1OpcodeC2_run_of_f3_memory context hrep a b d e f
      modrm hmod)

/-- With `mod = 3`, an `F3` prefix (`rep_prefix = 243`), in 64-bit mode with SSE: form 6,
`CMPSS_XMMss_XMMss_IMMb`. -/
theorem selectLegacy1OpcodeC2_run_of_f3_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_C2 context true a b true d e f modrm = .ok 6 := by
  simp [Select_Legacy_1_Opcode_C2, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`C2` decoder with an `F3` prefix (`rep_prefix = 243`) and a register ModRM
(`mod = 3`), with SSE reported, runs `CMPSS_XMMss_XMMss_IMMb` from the state after the ModRM fetch,
at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1OpcodeC2_run_of_f3_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_C2 ip context).run s =
      (X86.Instructions.CMPSS_XMMss_XMMss_IMMb (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_C2
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1OpcodeC2_run_of_f3_register context hrep a b d e f
      modrm hmod)

/-- With `mod ≠ 3`, an `F2` prefix (`rep_prefix = 242`), in 64-bit mode with SSE2: form 7,
`CMPSD_XMM_XMMsd_MEMsd_IMMb`. -/
theorem selectLegacy1OpcodeC2_run_of_f2_memory (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_C2 context true a b c true e f modrm = .ok 7 := by
  simp [Select_Legacy_1_Opcode_C2, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`C2` decoder with an `F2` prefix (`rep_prefix = 242`) and a memory ModRM (`mod ≠ 3`),
with SSE2 reported, runs `CMPSD_XMM_XMMsd_MEMsd_IMMb` from the state after the ModRM fetch, at
`ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1OpcodeC2_run_of_f2_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_C2 ip context).run s =
      (X86.Instructions.CMPSD_XMM_XMMsd_MEMsd_IMMb (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_C2
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1OpcodeC2_run_of_f2_memory context hrep a b c e f
      modrm hmod)

/-- With `mod = 3`, an `F2` prefix (`rep_prefix = 242`), in 64-bit mode with SSE2: form 8,
`CMPSD_XMM_XMMsd_XMMsd_IMMb`. -/
theorem selectLegacy1OpcodeC2_run_of_f2_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_C2 context true a b c true e f modrm = .ok 8 := by
  simp [Select_Legacy_1_Opcode_C2, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`C2` decoder with an `F2` prefix (`rep_prefix = 242`) and a register ModRM
(`mod = 3`), with SSE2 reported, runs `CMPSD_XMM_XMMsd_XMMsd_IMMb` from the state after the ModRM
fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1OpcodeC2_run_of_f2_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_C2 ip context).run s =
      (X86.Instructions.CMPSD_XMM_XMMsd_XMMsd_IMMb (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_C2
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1OpcodeC2_run_of_f2_register context hrep a b c e f
      modrm hmod)

end X86Proofs
