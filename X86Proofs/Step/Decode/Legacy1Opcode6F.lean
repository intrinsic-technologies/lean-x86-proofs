import X86Proofs.Step.Mmx

/-!
# Opcode `0F 6F`: `MOVDQA`, `MOVDQU xmm, xmm/m128`, `MOVQ mm, mm/m64`

The one place that looks inside lean-x86's opcode-`6F` decoder (`Decode_Legacy_1_Opcode_6F`) and its
form selection (`Select_Legacy_1_Opcode_6F`), architecture rule 5. In 64-bit mode the selection
picks, for `mod ≠ 3` / `mod = 3` and with SSE2: after `F3`, `MOVDQU_XMMdq_MEMdq` /
`MOVDQU_XMMdq_XMMdq_0F6F`; after `66` without a REP prefix, `MOVDQA_XMMdq_MEMdq` /
`MOVDQA_XMMdq_XMMdq_0F6F` (`Instructions/{Movdqu,Movdqa}/Generated`); without a prefix, with MMX,
`MOVQ_MMXq_MEMq_0F6F` / `MOVQ_MMXq_MMXq_0F6F` (`Instructions/Movq/Generated/{MMem,MM}`). For each, a
`selectLegacy1Opcode6F_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy1Opcode6F_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`, `ip` the
second opcode byte's address) to the call of that form at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcode6F` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod ≠ 3`, an `F3` prefix (`rep_prefix = 243`), in 64-bit mode with SSE2: form 1,
`MOVDQU_XMMdq_MEMdq`. -/
theorem selectLegacy1Opcode6F_run_of_f3_memory (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_6F context true a b c true e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_6F, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-6F decoder with an `F3` prefix (`rep_prefix = 243`) and a memory ModRM (`mod ≠ 3`),
with SSE2 reported, runs `MOVDQU_XMMdq_MEMdq` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1Opcode6F_run_of_f3_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_6F ip context).run s =
      (X86.Instructions.MOVDQU_XMMdq_MEMdq (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_6F
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode6F_run_of_f3_memory context hrep a b c e f
      modrm hmod)

/-- With `mod = 3`, an `F3` prefix (`rep_prefix = 243`), in 64-bit mode with SSE2: form 2,
`MOVDQU_XMMdq_XMMdq_0F6F`. -/
theorem selectLegacy1Opcode6F_run_of_f3_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_6F context true a b c true e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_6F, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-6F decoder with an `F3` prefix (`rep_prefix = 243`) and a register ModRM (`mod = 3`),
with SSE2 reported, runs `MOVDQU_XMMdq_XMMdq_0F6F` from the state after the ModRM fetch, at `ip +
2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode6F_run_of_f3_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_6F ip context).run s =
      (X86.Instructions.MOVDQU_XMMdq_XMMdq_0F6F (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_6F
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode6F_run_of_f3_register context hrep a b c e f
      modrm hmod)

/-- With `mod ≠ 3`, a `66` prefix and `rep_prefix = 0`, in 64-bit mode with SSE2: form 3,
`MOVDQA_XMMdq_MEMdq`. -/
theorem selectLegacy1Opcode6F_run_of_66_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_6F context true a b c true e f modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_6F, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd,
    HOr.hOr, OrOp.or, strictOr]

/-- The opcode-6F decoder with a `66` prefix and `rep_prefix = 0` and a memory ModRM (`mod ≠ 3`),
with SSE2 reported, runs `MOVDQA_XMMdq_MEMdq` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1Opcode6F_run_of_66_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_6F ip context).run s =
      (X86.Instructions.MOVDQA_XMMdq_MEMdq (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_6F
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode6F_run_of_66_memory context hosz hrep a b c e f
      modrm hmod)

/-- With `mod = 3`, a `66` prefix and `rep_prefix = 0`, in 64-bit mode with SSE2: form 4,
`MOVDQA_XMMdq_XMMdq_0F6F`. -/
theorem selectLegacy1Opcode6F_run_of_66_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_6F context true a b c true e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_6F, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd,
    HOr.hOr, OrOp.or, strictOr]

/-- The opcode-6F decoder with a `66` prefix and `rep_prefix = 0` and a register ModRM (`mod = 3`),
with SSE2 reported, runs `MOVDQA_XMMdq_XMMdq_0F6F` from the state after the ModRM fetch, at `ip +
2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode6F_run_of_66_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_6F ip context).run s =
      (X86.Instructions.MOVDQA_XMMdq_XMMdq_0F6F (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_6F
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode6F_run_of_66_register context hosz hrep a b c e f
      modrm hmod)

/-- With `mod = 3` and no `66` prefix, no REP prefix in 64-bit mode, with MMX: form 6,
`MOVQ_MMXq_MMXq_0F6F`. -/
theorem selectLegacy1Opcode6F_run_of_mmx_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (hrep : context.rep_prefix = 0)
    (a c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_6F context true a true c d e f modrm = .ok 6 := by
  simp [Select_Legacy_1_Opcode_6F, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd,
    HOr.hOr, OrOp.or, strictOr]

/-- The opcode-6F decoder with no `66` prefix, no REP prefix and a register ModRM (`mod = 3`), with
MMX reported, runs `MOVQ_MMXq_MMXq_0F6F` from the state after the ModRM fetch, at `ip + 2`, with the
ModRM fields. -/
theorem decodeLegacy1Opcode6F_run_of_mmx_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor t CPUID_MMX_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_6F ip context).run s =
      (X86.Instructions.MOVQ_MMXq_MMXq_0F6F (BitVec.add ip 2#64) context (modrm.extractLsb' 3 3)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_6F
  decode_modrm_form_mmx s t ip hfetch hmode hf hmmx
    (fun a c d e f =>
      selectLegacy1Opcode6F_run_of_mmx_register context hosz hrep a c d e f modrm hmod)

/-- With `mod ≠ 3` and no `66` prefix, no REP prefix in 64-bit mode, with MMX: form 5,
`MOVQ_MMXq_MEMq_0F6F`. -/
theorem selectLegacy1Opcode6F_run_of_mmx_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (hrep : context.rep_prefix = 0)
    (a c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_6F context true a true c d e f modrm = .ok 5 := by
  simp [Select_Legacy_1_Opcode_6F, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd,
    HOr.hOr, OrOp.or, strictOr]

/-- The opcode-6F decoder with no `66` prefix, no REP prefix and a memory ModRM (`mod ≠ 3`), with
MMX reported, runs `MOVQ_MMXq_MEMq_0F6F` from the state after the ModRM fetch, at `ip + 2`, with the
ModRM fields. -/
theorem decodeLegacy1Opcode6F_run_of_mmx_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor t CPUID_MMX_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_6F ip context).run s =
      (X86.Instructions.MOVQ_MMXq_MEMq_0F6F (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_6F
  decode_modrm_form_mmx s t ip hfetch hmode hf hmmx
    (fun a c d e f =>
      selectLegacy1Opcode6F_run_of_mmx_memory context hosz hrep a c d e f modrm hmod)

end X86Proofs
