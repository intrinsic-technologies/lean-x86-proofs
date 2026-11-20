import X86Proofs.Step.Sse

/-!
# Opcode `0F D6`: `MOVQ xmm/m64, xmm`, `MOVDQ2Q`, `MOVQ2DQ`

The one place that looks inside lean-x86's opcode-`D6` decoder (`Decode_Legacy_1_Opcode_D6`) and its
form selection (`Select_Legacy_1_Opcode_D6`), architecture rule 5. In 64-bit mode, after `66`
without a REP prefix and with SSE2, the selection picks `MOVQ_MEMq_XMMq_0FD6_1` for `mod ≠ 3` and
`MOVQ_XMMdq_XMMq_0FD6` for `mod = 3` (`Instructions/Movq/Generated/{MX,XXRev}`); for `mod = 3` after
`F2` it picks `MOVDQ2Q_MMXq_XMMq` and after `F3` `MOVQ2DQ_XMMdq_MMXq`, with SSE2
(`Instructions/Movdq2q/Generated/MmX`, `Instructions/Movq2dq/Generated/XMm`). For each, a
`selectLegacy1OpcodeD6_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy1OpcodeD6_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`, `ip` the
second opcode byte's address) to the call of that form at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcodeD6` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod ≠ 3`, a `66` prefix and `rep_prefix = 0`, in 64-bit mode with SSE2: form 1,
`MOVQ_MEMq_XMMq_0FD6_1`. -/
theorem selectLegacy1OpcodeD6_run_of_66_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_D6 context true a b c true e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_D6, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D6 decoder with a `66` prefix and `rep_prefix = 0` and a memory ModRM (`mod ≠ 3`),
with SSE2 reported, runs `MOVQ_MEMq_XMMq_0FD6_1` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1OpcodeD6_run_of_66_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_D6 ip context).run s =
      (X86.Instructions.MOVQ_MEMq_XMMq_0FD6_1 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_D6
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1OpcodeD6_run_of_66_memory context hosz hrep a b c e f
      modrm hmod)

/-- With `mod = 3`, a `66` prefix and `rep_prefix = 0`, in 64-bit mode with SSE2: form 2,
`MOVQ_XMMdq_XMMq_0FD6`. -/
theorem selectLegacy1OpcodeD6_run_of_66_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_D6 context true a b c true e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_D6, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D6 decoder with a `66` prefix and `rep_prefix = 0` and a register ModRM (`mod = 3`),
with SSE2 reported, runs `MOVQ_XMMdq_XMMq_0FD6` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1OpcodeD6_run_of_66_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_D6 ip context).run s =
      (X86.Instructions.MOVQ_XMMdq_XMMq_0FD6 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_D6
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1OpcodeD6_run_of_66_register context hosz hrep a b c e f
      modrm hmod)

/-- With `mod = 3` and an `F2` prefix in 64-bit mode, with SSE2: form 3, `MOVDQ2Q_MMXq_XMMq`. -/
theorem selectLegacy1OpcodeD6_run_of_f2_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (a b c e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_D6 context true a b c true e f modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_D6, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D6 decoder with an `F2` prefix and a register ModRM (`mod = 3`), with SSE2 reported,
runs `MOVDQ2Q_MMXq_XMMq` from the state after the ModRM fetch, at `ip + 2`, with the ModRM fields.
-/
theorem decodeLegacy1OpcodeD6_run_of_f2_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrep : context.rep_prefix = 242)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_D6 ip context).run s =
      (X86.Instructions.MOVDQ2Q_MMXq_XMMq (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_D6
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f =>
      selectLegacy1OpcodeD6_run_of_f2_register context hrep a b c e f modrm hmod)

/-- With `mod = 3` and an `F3` prefix in 64-bit mode, with SSE2: form 4, `MOVQ2DQ_XMMdq_MMXq`. -/
theorem selectLegacy1OpcodeD6_run_of_f3_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (a b c e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_D6 context true a b c true e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_D6, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D6 decoder with an `F3` prefix and a register ModRM (`mod = 3`), with SSE2 reported,
runs `MOVQ2DQ_XMMdq_MMXq` from the state after the ModRM fetch, at `ip + 2`, with the ModRM fields.
-/
theorem decodeLegacy1OpcodeD6_run_of_f3_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrep : context.rep_prefix = 243)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_D6 ip context).run s =
      (X86.Instructions.MOVQ2DQ_XMMdq_MMXq (BitVec.add ip 2#64) context (modrm.extractLsb' 3 3)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_D6
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f =>
      selectLegacy1OpcodeD6_run_of_f3_register context hrep a b c e f modrm hmod)

end X86Proofs
