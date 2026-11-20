import X86Proofs.Step.Mmx

/-!
# Opcode `0F 71`: Group 12, `PSLLW`, `PSRLW`, `PSRAW` by an immediate

The one place that looks inside lean-x86's opcode-`71` decoder (`Decode_Legacy_1_Opcode_71`) and its
form selection (`Select_Legacy_1_Opcode_71`), architecture rule 5. Group 12: the ModRM `reg` digit
picks the shift, on the register in ModRM `rm` (`mod = 3`) by an immediate count the form fetches
itself. In 64-bit mode the selection picks, after `66` and with SSE2, `PSLLW_XMMdq_IMMb` for `/6`,
`PSRLW_XMMdq_IMMb` for `/2`, `PSRAW_XMMdq_IMMb` for `/4` (`Instructions/<Op>/Generated/Imm8`).
Without `66`, with MMX, it picks the MMX forms the same way (`Instructions/<Op>/Generated/MImm8`).
For each, a `selectLegacy1Opcode71_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy1Opcode71_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`, `ip` the
second opcode byte's address) to the call of that form at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcode71` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3`, `reg = 6` and a `66` prefix in 64-bit mode, with SSE2: form 2,
`PSLLW_XMMdq_IMMb`. -/
theorem selectLegacy1Opcode71_run_of_r6_66_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_1_Opcode_71 context true a b c true e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_71, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-71 decoder with a `66` prefix and a register ModRM (`mod = 3`, `reg = 6`),
with SSE2 reported, runs `PSLLW_XMMdq_IMMb` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy1Opcode71_run_of_r6_66_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 6#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_71 ip context).run s =
      (X86.Instructions.PSLLW_XMMdq_IMMb (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_71
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode71_run_of_r6_66_register context hosz a b c e f modrm hmod
      hreg)

/-- With `mod = 3`, `reg = 2` and a `66` prefix in 64-bit mode, with SSE2: form 4,
`PSRLW_XMMdq_IMMb`. -/
theorem selectLegacy1Opcode71_run_of_r2_66_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_1_Opcode_71 context true a b c true e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_71, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-71 decoder with a `66` prefix and a register ModRM (`mod = 3`, `reg = 2`),
with SSE2 reported, runs `PSRLW_XMMdq_IMMb` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy1Opcode71_run_of_r2_66_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 2#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_71 ip context).run s =
      (X86.Instructions.PSRLW_XMMdq_IMMb (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_71
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode71_run_of_r2_66_register context hosz a b c e f modrm hmod
      hreg)

/-- With `mod = 3`, `reg = 4` and a `66` prefix in 64-bit mode, with SSE2: form 6,
`PSRAW_XMMdq_IMMb`. -/
theorem selectLegacy1Opcode71_run_of_r4_66_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_1_Opcode_71 context true a b c true e f modrm = .ok 6 := by
  simp [Select_Legacy_1_Opcode_71, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-71 decoder with a `66` prefix and a register ModRM (`mod = 3`, `reg = 4`),
with SSE2 reported, runs `PSRAW_XMMdq_IMMb` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy1Opcode71_run_of_r4_66_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_71 ip context).run s =
      (X86.Instructions.PSRAW_XMMdq_IMMb (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_71
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode71_run_of_r4_66_register context hosz a b c e f modrm hmod
      hreg)

/-- With `mod = 3`, `reg = 2` and no `66` prefix in 64-bit mode, with MMX: form 3,
`PSRLW_MMXq_IMMb`. -/
theorem selectLegacy1Opcode71_run_of_r2_mmx_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (a c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_1_Opcode_71 context true a true c d e f modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_71, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-71 decoder with no `66` prefix and a register ModRM (`mod = 3`), with MMX reported,
runs `PSRLW_MMXq_IMMb` from the state after the ModRM fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode71_run_of_r2_mmx_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor t CPUID_MMX_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_71 ip context).run s =
      (X86.Instructions.PSRLW_MMXq_IMMb (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_71
  decode_modrm_form_mmx s t ip hfetch hmode hf hmmx
    (fun a c d e f =>
      selectLegacy1Opcode71_run_of_r2_mmx_register context hosz a c d e f modrm hmod hreg)

/-- With `mod = 3`, `reg = 4` and no `66` prefix in 64-bit mode, with MMX: form 5,
`PSRAW_MMXq_IMMb`. -/
theorem selectLegacy1Opcode71_run_of_r4_mmx_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (a c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_1_Opcode_71 context true a true c d e f modrm = .ok 5 := by
  simp [Select_Legacy_1_Opcode_71, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-71 decoder with no `66` prefix and a register ModRM (`mod = 3`), with MMX reported,
runs `PSRAW_MMXq_IMMb` from the state after the ModRM fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode71_run_of_r4_mmx_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor t CPUID_MMX_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_71 ip context).run s =
      (X86.Instructions.PSRAW_MMXq_IMMb (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_71
  decode_modrm_form_mmx s t ip hfetch hmode hf hmmx
    (fun a c d e f =>
      selectLegacy1Opcode71_run_of_r4_mmx_register context hosz a c d e f modrm hmod hreg)

/-- With `mod = 3`, `reg = 6` and no `66` prefix in 64-bit mode, with MMX: form 1,
`PSLLW_MMXq_IMMb`. -/
theorem selectLegacy1Opcode71_run_of_r6_mmx_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (a c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_1_Opcode_71 context true a true c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_71, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-71 decoder with no `66` prefix and a register ModRM (`mod = 3`), with MMX reported,
runs `PSLLW_MMXq_IMMb` from the state after the ModRM fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode71_run_of_r6_mmx_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor t CPUID_MMX_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_71 ip context).run s =
      (X86.Instructions.PSLLW_MMXq_IMMb (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_71
  decode_modrm_form_mmx s t ip hfetch hmode hf hmmx
    (fun a c d e f =>
      selectLegacy1Opcode71_run_of_r6_mmx_register context hosz a c d e f modrm hmod hreg)

end X86Proofs
