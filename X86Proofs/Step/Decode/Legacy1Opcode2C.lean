import X86Proofs.Step.Sse

/-!
# Opcode `0F 2C`: `CVTTSS2SI`, `CVTTSD2SI`, `CVTTPS2PI`, `CVTTPD2PI`

The one place that looks inside lean-x86's opcode-`2C` decoder (`Decode_Legacy_1_Opcode_2C`) and its
form selection (`Select_Legacy_1_Opcode_2C`), architecture rule 5. For each form the library uses, a
`selectLegacy1Opcode2C_run_of_…` lemma gives the form the selection picks (by the REP prefix, REX.W,
`mod`, and the CPUID feature it requires), and a `decodeLegacy1Opcode2C_run_of_…` lemma runs the
decoder (from the ModRM fetch at `ip + 1`, `ip` the second opcode byte's address) to the call of
that form at `ip + 2`. The decoder and these forms may diverge (`PartialSpecM`: they convert to
integers with `FP.To_Int`), so a form's run is the decoder's. The `NP` and `66` forms (CVTTPS2PI,
CVTTPD2PI, `Instructions/{Cvttps2pi,Cvttpd2pi}/Generated/{MmX,MmM}`) write MMX registers.

The dispatch to this decoder is `decodeLegacy1_run_of_opcode2C` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod ≠ 3`, an `F2` prefix (`rep_prefix = 242`), REX.W clear, in 64-bit mode with SSE2: form
3, `CVTTSD2SI_GPR32d_MEMsd`. -/
theorem selectLegacy1Opcode2C_run_of_f2_w0_memory (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (hw : context.rex_w = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_2C context true a b c true e f modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_2C, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`2C` decoder with an `F2` prefix (`rep_prefix = 242`), REX.W clear and a memory ModRM
(`mod ≠ 3`), with SSE2 reported, runs `CVTTSD2SI_GPR32d_MEMsd` (a `PartialSpecM` form) from the
state after the ModRM fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode2C_run_of_f2_w0_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (hw : context.rex_w = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2C ip context).run s =
      (X86.Instructions.CVTTSD2SI_GPR32d_MEMsd (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2C
  decode_modrm_form_sse2_partial s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode2C_run_of_f2_w0_memory context hrep hw a b c e f modrm
      hmod)

/-- With `mod = 3`, an `F2` prefix (`rep_prefix = 242`), REX.W clear, in 64-bit mode with SSE2: form
4, `CVTTSD2SI_GPR32d_XMMsd`. -/
theorem selectLegacy1Opcode2C_run_of_f2_w0_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (hw : context.rex_w = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_2C context true a b c true e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_2C, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`2C` decoder with an `F2` prefix (`rep_prefix = 242`), REX.W clear and a register
ModRM (`mod = 3`), with SSE2 reported, runs `CVTTSD2SI_GPR32d_XMMsd` (a `PartialSpecM` form) from
the state after the ModRM fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode2C_run_of_f2_w0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (hw : context.rex_w = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2C ip context).run s =
      (X86.Instructions.CVTTSD2SI_GPR32d_XMMsd (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2C
  decode_modrm_form_sse2_partial s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode2C_run_of_f2_w0_register context hrep hw a b c e f modrm
      hmod)

/-- With `mod ≠ 3`, an `F2` prefix (`rep_prefix = 242`), REX.W set, in 64-bit mode with SSE2: form
5, `CVTTSD2SI_GPR64q_MEMsd`. -/
theorem selectLegacy1Opcode2C_run_of_f2_w1_memory (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (hw : context.rex_w = 1)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_2C context true a b c true e f modrm = .ok 5 := by
  simp [Select_Legacy_1_Opcode_2C, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`2C` decoder with an `F2` prefix (`rep_prefix = 242`), REX.W set and a memory ModRM
(`mod ≠ 3`), with SSE2 reported, runs `CVTTSD2SI_GPR64q_MEMsd` (a `PartialSpecM` form) from the
state after the ModRM fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode2C_run_of_f2_w1_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (hw : context.rex_w = 1)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2C ip context).run s =
      (X86.Instructions.CVTTSD2SI_GPR64q_MEMsd (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2C
  decode_modrm_form_sse2_partial s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode2C_run_of_f2_w1_memory context hrep hw a b c e f modrm
      hmod)

/-- With `mod = 3`, an `F2` prefix (`rep_prefix = 242`), REX.W set, in 64-bit mode with SSE2: form
6, `CVTTSD2SI_GPR64q_XMMsd`. -/
theorem selectLegacy1Opcode2C_run_of_f2_w1_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (hw : context.rex_w = 1)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_2C context true a b c true e f modrm = .ok 6 := by
  simp [Select_Legacy_1_Opcode_2C, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`2C` decoder with an `F2` prefix (`rep_prefix = 242`), REX.W set and a register ModRM
(`mod = 3`), with SSE2 reported, runs `CVTTSD2SI_GPR64q_XMMsd` (a `PartialSpecM` form) from the
state after the ModRM fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode2C_run_of_f2_w1_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (hw : context.rex_w = 1)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2C ip context).run s =
      (X86.Instructions.CVTTSD2SI_GPR64q_XMMsd (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2C
  decode_modrm_form_sse2_partial s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode2C_run_of_f2_w1_register context hrep hw a b c e f modrm
      hmod)

/-- With `mod ≠ 3`, an `F3` prefix (`rep_prefix = 243`), REX.W clear, in 64-bit mode with SSE: form
7, `CVTTSS2SI_GPR32d_MEMss`. -/
theorem selectLegacy1Opcode2C_run_of_f3_w0_memory (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hw : context.rex_w = 0)
    (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_2C context true a b true d e f modrm = .ok 7 := by
  simp [Select_Legacy_1_Opcode_2C, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`2C` decoder with an `F3` prefix (`rep_prefix = 243`), REX.W clear and a memory ModRM
(`mod ≠ 3`), with SSE reported, runs `CVTTSS2SI_GPR32d_MEMss` (a `PartialSpecM` form) from the state
after the ModRM fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode2C_run_of_f3_w0_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hw : context.rex_w = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2C ip context).run s =
      (X86.Instructions.CVTTSS2SI_GPR32d_MEMss (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2C
  decode_modrm_form_sse_partial s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode2C_run_of_f3_w0_memory context hrep hw a b d e f modrm
      hmod)

/-- With `mod = 3`, an `F3` prefix (`rep_prefix = 243`), REX.W clear, in 64-bit mode with SSE: form
8, `CVTTSS2SI_GPR32d_XMMss`. -/
theorem selectLegacy1Opcode2C_run_of_f3_w0_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hw : context.rex_w = 0)
    (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_2C context true a b true d e f modrm = .ok 8 := by
  simp [Select_Legacy_1_Opcode_2C, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`2C` decoder with an `F3` prefix (`rep_prefix = 243`), REX.W clear and a register
ModRM (`mod = 3`), with SSE reported, runs `CVTTSS2SI_GPR32d_XMMss` (a `PartialSpecM` form) from the
state after the ModRM fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode2C_run_of_f3_w0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hw : context.rex_w = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2C ip context).run s =
      (X86.Instructions.CVTTSS2SI_GPR32d_XMMss (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2C
  decode_modrm_form_sse_partial s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode2C_run_of_f3_w0_register context hrep hw a b d e f modrm
      hmod)

/-- With `mod ≠ 3`, an `F3` prefix (`rep_prefix = 243`), REX.W set, in 64-bit mode with SSE: form 9,
`CVTTSS2SI_GPR64q_MEMss`. -/
theorem selectLegacy1Opcode2C_run_of_f3_w1_memory (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hw : context.rex_w = 1)
    (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_2C context true a b true d e f modrm = .ok 9 := by
  simp [Select_Legacy_1_Opcode_2C, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`2C` decoder with an `F3` prefix (`rep_prefix = 243`), REX.W set and a memory ModRM
(`mod ≠ 3`), with SSE reported, runs `CVTTSS2SI_GPR64q_MEMss` (a `PartialSpecM` form) from the state
after the ModRM fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode2C_run_of_f3_w1_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hw : context.rex_w = 1)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2C ip context).run s =
      (X86.Instructions.CVTTSS2SI_GPR64q_MEMss (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2C
  decode_modrm_form_sse_partial s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode2C_run_of_f3_w1_memory context hrep hw a b d e f modrm
      hmod)

/-- With `mod = 3`, an `F3` prefix (`rep_prefix = 243`), REX.W set, in 64-bit mode with SSE: form
10, `CVTTSS2SI_GPR64q_XMMss`. -/
theorem selectLegacy1Opcode2C_run_of_f3_w1_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hw : context.rex_w = 1)
    (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_2C context true a b true d e f modrm = .ok 10 := by
  simp [Select_Legacy_1_Opcode_2C, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`2C` decoder with an `F3` prefix (`rep_prefix = 243`), REX.W set and a register ModRM
(`mod = 3`), with SSE reported, runs `CVTTSS2SI_GPR64q_XMMss` (a `PartialSpecM` form) from the state
after the ModRM fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode2C_run_of_f3_w1_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hw : context.rex_w = 1)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2C ip context).run s =
      (X86.Instructions.CVTTSS2SI_GPR64q_XMMss (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2C
  decode_modrm_form_sse_partial s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode2C_run_of_f3_w1_register context hrep hw a b d e f modrm
      hmod)

/-- With `mod = 3` and no `66` prefix, `rep_prefix = 0` in 64-bit mode, with SSE: form 12,
`CVTTPS2PI_MMXq_XMMq`. -/
theorem selectLegacy1Opcode2C_run_of_mmx_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (hrep : context.rep_prefix = 0)
    (a b d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_2C context true a b true d e f modrm = .ok 12 := by
  simp [Select_Legacy_1_Opcode_2C, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-2C decoder with no `66` prefix, `rep_prefix = 0` and a register ModRM (`mod = 3`),
with SSE reported, runs `CVTTPS2PI_MMXq_XMMq` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1Opcode2C_run_of_mmx_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2C ip context).run s =
      (X86.Instructions.CVTTPS2PI_MMXq_XMMq (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2C
  decode_modrm_form_sse_partial s t ip hfetch hmode hf hsse
    (fun a b d e f =>
      selectLegacy1Opcode2C_run_of_mmx_register context hosz hrep a b d e f modrm hmod)

/-- With `mod ≠ 3` and no `66` prefix, `rep_prefix = 0` in 64-bit mode, with SSE: form 11,
`CVTTPS2PI_MMXq_MEMq`. -/
theorem selectLegacy1Opcode2C_run_of_mmx_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (hrep : context.rep_prefix = 0)
    (a b d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_2C context true a b true d e f modrm = .ok 11 := by
  simp [Select_Legacy_1_Opcode_2C, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-2C decoder with no `66` prefix, `rep_prefix = 0` and a memory ModRM (`mod ≠ 3`), with
SSE reported, runs `CVTTPS2PI_MMXq_MEMq` from the state after the ModRM fetch, at `ip + 2`, with the
ModRM fields. -/
theorem decodeLegacy1Opcode2C_run_of_mmx_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2C ip context).run s =
      (X86.Instructions.CVTTPS2PI_MMXq_MEMq (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2C
  decode_modrm_form_sse_partial s t ip hfetch hmode hf hsse
    (fun a b d e f =>
      selectLegacy1Opcode2C_run_of_mmx_memory context hosz hrep a b d e f modrm hmod)

/-- With `mod = 3` and a `66` prefix, `rep_prefix = 0` in 64-bit mode, with SSE2: form 2,
`CVTTPD2PI_MMXq_XMMpd`. -/
theorem selectLegacy1Opcode2C_run_of_66_mmx_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_2C context true a b c true e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_2C, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-2C decoder with a `66` prefix, `rep_prefix = 0` and a register ModRM (`mod = 3`),
with SSE2 reported, runs `CVTTPD2PI_MMXq_XMMpd` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1Opcode2C_run_of_66_mmx_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2C ip context).run s =
      (X86.Instructions.CVTTPD2PI_MMXq_XMMpd (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2C
  decode_modrm_form_sse2_partial s t ip hfetch hmode hf hsse2
    (fun a b c e f =>
      selectLegacy1Opcode2C_run_of_66_mmx_register context hosz hrep a b c e f modrm hmod)

/-- With `mod ≠ 3` and a `66` prefix, `rep_prefix = 0` in 64-bit mode, with SSE2: form 1,
`CVTTPD2PI_MMXq_MEMpd`. -/
theorem selectLegacy1Opcode2C_run_of_66_mmx_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_2C context true a b c true e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_2C, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-2C decoder with a `66` prefix, `rep_prefix = 0` and a memory ModRM (`mod ≠ 3`), with
SSE2 reported, runs `CVTTPD2PI_MMXq_MEMpd` from the state after the ModRM fetch, at `ip + 2`, with
the ModRM fields. -/
theorem decodeLegacy1Opcode2C_run_of_66_mmx_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_2C ip context).run s =
      (X86.Instructions.CVTTPD2PI_MMXq_MEMpd (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_2C
  decode_modrm_form_sse2_partial s t ip hfetch hmode hf hsse2
    (fun a b c e f =>
      selectLegacy1Opcode2C_run_of_66_mmx_memory context hosz hrep a b c e f modrm hmod)

end X86Proofs
