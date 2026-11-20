import X86Proofs.Step.Sse

/-!
# Opcode `0F E6`: `CVTDQ2PD`

The one place that looks inside lean-x86's opcode-`E6` decoder (`Decode_Legacy_1_Opcode_E6`) and its
form selection (`Select_Legacy_1_Opcode_E6`), architecture rule 5. For each form the library uses, a
`selectLegacy1OpcodeE6_run_of_…` lemma gives the form the selection picks (by the `66` and REP
prefixes, `mod`, and the CPUID feature it requires), and a `decodeLegacy1OpcodeE6_run_of_…` lemma
runs the decoder (from the ModRM fetch at `ip + 1`, `ip` the second opcode byte's address) to the
call of that form at `ip + 2`. The decoder may diverge (`PartialSpecM`: the `66` and `F2` forms,
CVTTPD2DQ and CVTPD2DQ, convert to integers with `FP.To_Int`, and run as they are); CVTDQ2PD is
total and runs through `liftTotal`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcodeE6` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod ≠ 3`, an `F3` prefix (`rep_prefix = 243`), in 64-bit mode with SSE2: form 1,
`CVTDQ2PD_XMMpd_MEMq`. -/
theorem selectLegacy1OpcodeE6_run_of_f3_memory (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_E6 context true a b c true e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_E6, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`E6` decoder with an `F3` prefix (`rep_prefix = 243`) and a memory ModRM (`mod ≠ 3`),
with SSE2 reported, runs `CVTDQ2PD_XMMpd_MEMq` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1OpcodeE6_run_of_f3_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_E6 ip context).run s =
      some ((X86.Instructions.CVTDQ2PD_XMMpd_MEMq (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t) := by
  unfold Decode_Legacy_1_Opcode_E6
  decode_modrm_form_sse2_partial s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1OpcodeE6_run_of_f3_memory context hrep a b c e f
      modrm hmod)

/-- With `mod = 3`, an `F3` prefix (`rep_prefix = 243`), in 64-bit mode with SSE2: form 2,
`CVTDQ2PD_XMMpd_XMMq`. -/
theorem selectLegacy1OpcodeE6_run_of_f3_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_E6 context true a b c true e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_E6, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`E6` decoder with an `F3` prefix (`rep_prefix = 243`) and a register ModRM (`mod =
3`), with SSE2 reported, runs `CVTDQ2PD_XMMpd_XMMq` from the state after the ModRM fetch, at `ip +
2`, with the ModRM fields. -/
theorem decodeLegacy1OpcodeE6_run_of_f3_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_E6 ip context).run s =
      some ((X86.Instructions.CVTDQ2PD_XMMpd_XMMq (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t) := by
  unfold Decode_Legacy_1_Opcode_E6
  decode_modrm_form_sse2_partial s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1OpcodeE6_run_of_f3_register context hrep a b c e f
      modrm hmod)

/-- With `mod ≠ 3`, a `66` prefix, no REP prefix, in 64-bit mode with SSE2: form 3,
`CVTTPD2DQ_XMMdq_MEMpd`. -/
theorem selectLegacy1OpcodeE6_run_of_66_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_E6 context true a b c true e f modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_E6, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`E6` decoder with a `66` prefix, no REP prefix and a memory ModRM (`mod ≠ 3`), with
SSE2 reported, runs `CVTTPD2DQ_XMMdq_MEMpd` (a `PartialSpecM` form) from the state after the ModRM
fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1OpcodeE6_run_of_66_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_E6 ip context).run s =
      (X86.Instructions.CVTTPD2DQ_XMMdq_MEMpd (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_E6
  decode_modrm_form_sse2_partial s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1OpcodeE6_run_of_66_memory context hosz hrep a b c e f modrm hmod)

/-- With `mod = 3`, a `66` prefix, no REP prefix, in 64-bit mode with SSE2: form 4,
`CVTTPD2DQ_XMMdq_XMMpd`. -/
theorem selectLegacy1OpcodeE6_run_of_66_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_E6 context true a b c true e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_E6, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`E6` decoder with a `66` prefix, no REP prefix and a register ModRM (`mod = 3`), with
SSE2 reported, runs `CVTTPD2DQ_XMMdq_XMMpd` (a `PartialSpecM` form) from the state after the ModRM
fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1OpcodeE6_run_of_66_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_E6 ip context).run s =
      (X86.Instructions.CVTTPD2DQ_XMMdq_XMMpd (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_E6
  decode_modrm_form_sse2_partial s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1OpcodeE6_run_of_66_register context hosz hrep a b c e f modrm
      hmod)

/-- With `mod ≠ 3`, an `F2` prefix (`rep_prefix = 242`), in 64-bit mode with SSE2: form 5,
`CVTPD2DQ_XMMdq_MEMpd`. -/
theorem selectLegacy1OpcodeE6_run_of_f2_memory (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_E6 context true a b c true e f modrm = .ok 5 := by
  simp [Select_Legacy_1_Opcode_E6, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`E6` decoder with an `F2` prefix (`rep_prefix = 242`) and a memory ModRM (`mod ≠ 3`),
with SSE2 reported, runs `CVTPD2DQ_XMMdq_MEMpd` (a `PartialSpecM` form) from the state after the
ModRM fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1OpcodeE6_run_of_f2_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_E6 ip context).run s =
      (X86.Instructions.CVTPD2DQ_XMMdq_MEMpd (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_E6
  decode_modrm_form_sse2_partial s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1OpcodeE6_run_of_f2_memory context hrep a b c e f modrm hmod)

/-- With `mod = 3`, an `F2` prefix (`rep_prefix = 242`), in 64-bit mode with SSE2: form 6,
`CVTPD2DQ_XMMdq_XMMpd`. -/
theorem selectLegacy1OpcodeE6_run_of_f2_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_E6 context true a b c true e f modrm = .ok 6 := by
  simp [Select_Legacy_1_Opcode_E6, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`E6` decoder with an `F2` prefix (`rep_prefix = 242`) and a register ModRM
(`mod = 3`), with SSE2 reported, runs `CVTPD2DQ_XMMdq_XMMpd` (a `PartialSpecM` form) from the state
after the ModRM fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1OpcodeE6_run_of_f2_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_E6 ip context).run s =
      (X86.Instructions.CVTPD2DQ_XMMdq_XMMpd (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_E6
  decode_modrm_form_sse2_partial s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1OpcodeE6_run_of_f2_register context hrep a b c e f modrm hmod)

end X86Proofs
