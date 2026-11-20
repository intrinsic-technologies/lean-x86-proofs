import X86Proofs.Step.Sse

/-!
# Opcode `0F AE`: Group 15, `LDMXCSR`, `STMXCSR`

The one place that looks inside lean-x86's opcode-`AE` decoder (`Decode_Legacy_1_Opcode_AE`) and
its form selection (`Select_Legacy_1_Opcode_AE`), architecture rule 5. Group 15: the ModRM `reg`
digit picks the form. In 64-bit mode, with a memory ModRM (`mod ≠ 3`) and no `66` prefix, the
selection picks `LDMXCSR_MEMd` for `/2` and `STMXCSR_MEMd` for `/3` (each if CPUID reports SSE);
both forms then raise #UD for a `66` or REP prefix. With a register ModRM
(`mod = 3`) it picks the fences, `LFENCE` for `/5`, `MFENCE` for `/6` (with SSE2) and `SFENCE` for
`/7` (with SSE) (`Instructions/Fence`; here without `66` and REP). The other digits (FXSAVE,
FXRSTOR, CLFLUSH) are not covered. For each, a `selectLegacy1OpcodeAE_run_of_…` lemma
gives the form the selection picks, and a `decodeLegacy1OpcodeAE_run_of_…` lemma runs the decoder
(from the ModRM fetch at `ip + 1`, `ip` the second opcode byte's address) to the call of that form
at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcodeAE` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod ≠ 3`, `reg = 2` and no `66` prefix, in 64-bit mode with SSE: form 1,
`LDMXCSR_MEMd`. -/
theorem selectLegacy1OpcodeAE_run_of_r2_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_1_Opcode_AE context true a b true d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_AE, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hosz, HAnd.hAnd, AndOp.and, strictAnd, HOr.hOr,
    OrOp.or, strictOr]

/-- The opcode-`AE` decoder with no `66` prefix and a memory ModRM (`mod ≠ 3`, `reg = 2`), with SSE
reported, runs `LDMXCSR_MEMd` from the state after the ModRM fetch, at `ip + 2`, with the ModRM
`mod` and `rm` fields. -/
theorem decodeLegacy1OpcodeAE_run_of_r2_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 2#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_AE ip context).run s =
      (X86.Instructions.LDMXCSR_MEMd (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_AE
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1OpcodeAE_run_of_r2_memory context hosz a b d e f modrm hmod
      hreg)

/-- With `mod ≠ 3`, `reg = 3` and no `66` prefix, in 64-bit mode with SSE: form 2,
`STMXCSR_MEMd`. -/
theorem selectLegacy1OpcodeAE_run_of_r3_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_1_Opcode_AE context true a b true d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_AE, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hosz, HAnd.hAnd, AndOp.and, strictAnd, HOr.hOr,
    OrOp.or, strictOr]

/-- The opcode-`AE` decoder with no `66` prefix and a memory ModRM (`mod ≠ 3`, `reg = 3`), with SSE
reported, runs `STMXCSR_MEMd` from the state after the ModRM fetch, at `ip + 2`, with the ModRM
`mod` and `rm` fields. -/
theorem decodeLegacy1OpcodeAE_run_of_r3_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 3#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_AE ip context).run s =
      (X86.Instructions.STMXCSR_MEMd (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_AE
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1OpcodeAE_run_of_r3_memory context hosz a b d e f modrm hmod
      hreg)

/-- With `mod = 3`, `reg = 5`, no `66` and no REP prefix, in 64-bit mode with SSE2: form 4,
`LFENCE`. -/
theorem selectLegacy1OpcodeAE_run_of_lfence (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_1_Opcode_AE context true a b c true e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_AE, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd, HOr.hOr,
    OrOp.or, strictOr]

/-- The opcode-`AE` decoder with a register ModRM (`mod = 3`, `reg = 5`), no `66` and no REP
prefix, with SSE2 reported, runs `LFENCE` from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy1OpcodeAE_run_of_lfence [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 5#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_AE ip context).run s =
      (X86.Instructions.LFENCE (BitVec.add ip 2#64) context).run t := by
  unfold Decode_Legacy_1_Opcode_AE
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1OpcodeAE_run_of_lfence context hosz hrep a b c e f modrm hmod
      hreg)

/-- With `mod = 3`, `reg = 6`, no `66` and no REP prefix, in 64-bit mode with SSE2: form 6,
`MFENCE`. -/
theorem selectLegacy1OpcodeAE_run_of_mfence (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_1_Opcode_AE context true a b c true e f modrm = .ok 6 := by
  simp [Select_Legacy_1_Opcode_AE, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd, HOr.hOr,
    OrOp.or, strictOr]

/-- The opcode-`AE` decoder with a register ModRM (`mod = 3`, `reg = 6`), no `66` and no REP
prefix, with SSE2 reported, runs `MFENCE` from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy1OpcodeAE_run_of_mfence [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 6#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_AE ip context).run s =
      (X86.Instructions.MFENCE (BitVec.add ip 2#64) context).run t := by
  unfold Decode_Legacy_1_Opcode_AE
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1OpcodeAE_run_of_mfence context hosz hrep a b c e f modrm hmod
      hreg)

/-- With `mod = 3`, `reg = 7` and no `66` prefix, in 64-bit mode with SSE: form 5, `SFENCE`. -/
theorem selectLegacy1OpcodeAE_run_of_sfence (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_1_Opcode_AE context true a b true d e f modrm = .ok 5 := by
  simp [Select_Legacy_1_Opcode_AE, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hosz, HAnd.hAnd, AndOp.and, strictAnd, HOr.hOr,
    OrOp.or, strictOr]

/-- The opcode-`AE` decoder with a register ModRM (`mod = 3`, `reg = 7`) and no `66` prefix, with
SSE reported, runs `SFENCE` from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy1OpcodeAE_run_of_sfence [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 7#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_AE ip context).run s =
      (X86.Instructions.SFENCE (BitVec.add ip 2#64) context).run t := by
  unfold Decode_Legacy_1_Opcode_AE
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1OpcodeAE_run_of_sfence context hosz a b d e f modrm hmod hreg)

end X86Proofs
