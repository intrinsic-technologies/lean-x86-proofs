import X86Proofs.Step.Mmx

/-!
# Opcode `0F 73`: Group 14, `PSLLQ`, `PSRLQ`, `PSLLDQ`, `PSRLDQ` by an immediate

The one place that looks inside lean-x86's opcode-`73` decoder (`Decode_Legacy_1_Opcode_73`) and its
form selection (`Select_Legacy_1_Opcode_73`), architecture rule 5. Group 14: the ModRM `reg` digit
picks the shift, on the register in ModRM `rm` (`mod = 3`) by an immediate count the form fetches
itself. In 64-bit mode the selection picks, after `66` and with SSE2, `PSLLQ_XMMdq_IMMb` for `/6`,
`PSRLQ_XMMdq_IMMb` for `/2`, `PSLLDQ_XMMdq_IMMb` for `/7`, `PSRLDQ_XMMdq_IMMb` for `/3`
(`Instructions/<Op>/Generated/Imm8`). Without `66` it picks the MMX forms, which the library does
not cover. For each, a `selectLegacy1Opcode73_run_of_…` lemma gives the form the selection picks,
and a `decodeLegacy1Opcode73_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`,
`ip` the second opcode byte's address) to the call of that form at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcode73` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3`, `reg = 6` and a `66` prefix in 64-bit mode, with SSE2: form 2,
`PSLLQ_XMMdq_IMMb`. -/
theorem selectLegacy1Opcode73_run_of_r6_66_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_1_Opcode_73 context true a b c true e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_73, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-73 decoder with a `66` prefix and a register ModRM (`mod = 3`, `reg = 6`),
with SSE2 reported, runs `PSLLQ_XMMdq_IMMb` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy1Opcode73_run_of_r6_66_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 6#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_73 ip context).run s =
      (X86.Instructions.PSLLQ_XMMdq_IMMb (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_73
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode73_run_of_r6_66_register context hosz a b c e f modrm hmod
      hreg)

/-- With `mod = 3`, `reg = 2` and a `66` prefix in 64-bit mode, with SSE2: form 4,
`PSRLQ_XMMdq_IMMb`. -/
theorem selectLegacy1Opcode73_run_of_r2_66_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_1_Opcode_73 context true a b c true e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_73, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-73 decoder with a `66` prefix and a register ModRM (`mod = 3`, `reg = 2`),
with SSE2 reported, runs `PSRLQ_XMMdq_IMMb` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy1Opcode73_run_of_r2_66_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 2#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_73 ip context).run s =
      (X86.Instructions.PSRLQ_XMMdq_IMMb (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_73
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode73_run_of_r2_66_register context hosz a b c e f modrm hmod
      hreg)

/-- With `mod = 3`, `reg = 7` and a `66` prefix in 64-bit mode, with SSE2: form 5,
`PSLLDQ_XMMdq_IMMb`. -/
theorem selectLegacy1Opcode73_run_of_r7_66_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_1_Opcode_73 context true a b c true e f modrm = .ok 5 := by
  simp [Select_Legacy_1_Opcode_73, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-73 decoder with a `66` prefix and a register ModRM (`mod = 3`, `reg = 7`),
with SSE2 reported, runs `PSLLDQ_XMMdq_IMMb` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy1Opcode73_run_of_r7_66_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 7#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_73 ip context).run s =
      (X86.Instructions.PSLLDQ_XMMdq_IMMb (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_73
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode73_run_of_r7_66_register context hosz a b c e f modrm hmod
      hreg)

/-- With `mod = 3`, `reg = 3` and a `66` prefix in 64-bit mode, with SSE2: form 6,
`PSRLDQ_XMMdq_IMMb`. -/
theorem selectLegacy1Opcode73_run_of_r3_66_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_1_Opcode_73 context true a b c true e f modrm = .ok 6 := by
  simp [Select_Legacy_1_Opcode_73, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-73 decoder with a `66` prefix and a register ModRM (`mod = 3`, `reg = 3`),
with SSE2 reported, runs `PSRLDQ_XMMdq_IMMb` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy1Opcode73_run_of_r3_66_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 3#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_73 ip context).run s =
      (X86.Instructions.PSRLDQ_XMMdq_IMMb (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_73
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode73_run_of_r3_66_register context hosz a b c e f modrm hmod
      hreg)

/-- With `mod = 3`, `reg = 2` and no `66` prefix in 64-bit mode, with MMX: form 3,
`PSRLQ_MMXq_IMMb`. -/
theorem selectLegacy1Opcode73_run_of_r2_mmx_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (a c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_1_Opcode_73 context true a true c d e f modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_73, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-73 decoder with no `66` prefix and a register ModRM (`mod = 3`), with MMX reported,
runs `PSRLQ_MMXq_IMMb` from the state after the ModRM fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode73_run_of_r2_mmx_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor t CPUID_MMX_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_73 ip context).run s =
      (X86.Instructions.PSRLQ_MMXq_IMMb (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_73
  decode_modrm_form_mmx s t ip hfetch hmode hf hmmx
    (fun a c d e f =>
      selectLegacy1Opcode73_run_of_r2_mmx_register context hosz a c d e f modrm hmod hreg)

/-- With `mod = 3`, `reg = 6` and no `66` prefix in 64-bit mode, with MMX: form 1,
`PSLLQ_MMXq_IMMb`. -/
theorem selectLegacy1Opcode73_run_of_r6_mmx_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (a c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_1_Opcode_73 context true a true c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_73, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-73 decoder with no `66` prefix and a register ModRM (`mod = 3`), with MMX reported,
runs `PSLLQ_MMXq_IMMb` from the state after the ModRM fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode73_run_of_r6_mmx_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor t CPUID_MMX_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_73 ip context).run s =
      (X86.Instructions.PSLLQ_MMXq_IMMb (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_73
  decode_modrm_form_mmx s t ip hfetch hmode hf hmmx
    (fun a c d e f =>
      selectLegacy1Opcode73_run_of_r6_mmx_register context hosz a c d e f modrm hmod hreg)

end X86Proofs
