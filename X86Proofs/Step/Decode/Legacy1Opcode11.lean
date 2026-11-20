import X86Proofs.Step.Sse

/-!
# Opcode `0F 11`: `MOVUPS`, `MOVUPD`, `MOVSS xmm/m, xmm`, `MOVSD xmm/m, xmm`

The one place that looks inside lean-x86's opcode-`11` decoder (`Decode_Legacy_1_Opcode_11`) and its
form selection (`Select_Legacy_1_Opcode_11`), architecture rule 5. In 64-bit mode the selection
picks, for `mod ≠ 3` / `mod = 3`: without a `66` or REP prefix and with SSE, `MOVUPS_MEMps_XMMps` /
`MOVUPS_XMMps_XMMps_0F11`; after `66` with SSE2, `MOVUPD_MEMpd_XMMpd` / `MOVUPD_XMMpd_XMMpd_0F11`;
after `F3` with SSE, `MOVSS_MEMss_XMMss_1` / `MOVSS_XMMss_XMMss_0F11`; after `F2` with SSE2,
`MOVSD_XMM_MEMsd_XMMsd_1` / `MOVSD_XMM_XMMsd_XMMsd_0F11`
(`Instructions/{Movups,Movupd,Movss,Movsd}/Generated`). For each,
a `selectLegacy1Opcode11_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy1Opcode11_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`, `ip` the
second opcode byte's address) to the call of that form at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcode11` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod ≠ 3`, an `F3` prefix (`rep_prefix = 243`), in 64-bit mode with SSE: form 4,
`MOVSS_MEMss_XMMss_1`. -/
theorem selectLegacy1Opcode11_run_of_f3_memory (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_11 context true a b true d e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_11, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-11 decoder with an `F3` prefix (`rep_prefix = 243`) and a memory ModRM (`mod ≠ 3`),
with SSE reported, runs `MOVSS_MEMss_XMMss_1` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1Opcode11_run_of_f3_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_11 ip context).run s =
      (X86.Instructions.MOVSS_MEMss_XMMss_1 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_11
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode11_run_of_f3_memory context hrep a b d e f
      modrm hmod)

/-- With `mod = 3`, an `F3` prefix (`rep_prefix = 243`), in 64-bit mode with SSE: form 3,
`MOVSS_XMMss_XMMss_0F11`. -/
theorem selectLegacy1Opcode11_run_of_f3_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_11 context true a b true d e f modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_11, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-11 decoder with an `F3` prefix (`rep_prefix = 243`) and a register ModRM (`mod = 3`),
with SSE reported, runs `MOVSS_XMMss_XMMss_0F11` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1Opcode11_run_of_f3_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_11 ip context).run s =
      (X86.Instructions.MOVSS_XMMss_XMMss_0F11 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_11
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode11_run_of_f3_register context hrep a b d e f
      modrm hmod)

/-- With `mod ≠ 3`, no `66` prefix and `rep_prefix = 0`, in 64-bit mode with SSE: form 5,
`MOVUPS_MEMps_XMMps`. -/
theorem selectLegacy1Opcode11_run_of_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_11 context true a b true d e f modrm = .ok 5 := by
  simp [Select_Legacy_1_Opcode_11, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-11 decoder with no `66` prefix and `rep_prefix = 0` and a memory ModRM (`mod ≠ 3`),
with SSE reported, runs `MOVUPS_MEMps_XMMps` from the state after the ModRM fetch, at `ip + 2`, with
the ModRM fields. -/
theorem decodeLegacy1Opcode11_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_11 ip context).run s =
      (X86.Instructions.MOVUPS_MEMps_XMMps (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_11
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode11_run_of_memory context hosz hrep a b d e f
      modrm hmod)

/-- With `mod = 3`, no `66` prefix and `rep_prefix = 0`, in 64-bit mode with SSE: form 6,
`MOVUPS_XMMps_XMMps_0F11`. -/
theorem selectLegacy1Opcode11_run_of_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_11 context true a b true d e f modrm = .ok 6 := by
  simp [Select_Legacy_1_Opcode_11, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-11 decoder with no `66` prefix and `rep_prefix = 0` and a register ModRM (`mod = 3`),
with SSE reported, runs `MOVUPS_XMMps_XMMps_0F11` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1Opcode11_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_11 ip context).run s =
      (X86.Instructions.MOVUPS_XMMps_XMMps_0F11 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_11
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode11_run_of_register context hosz hrep a b d e f
      modrm hmod)

/-- With `mod ≠ 3`, a `66` prefix and `rep_prefix = 0`, in 64-bit mode with SSE2: form 7,
`MOVUPD_MEMpd_XMMpd`. -/
theorem selectLegacy1Opcode11_run_of_66_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_11 context true a b c true e f modrm = .ok 7 := by
  simp [Select_Legacy_1_Opcode_11, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-11 decoder with a `66` prefix and `rep_prefix = 0` and a memory ModRM (`mod ≠ 3`),
with SSE2 reported, runs `MOVUPD_MEMpd_XMMpd` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1Opcode11_run_of_66_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_11 ip context).run s =
      (X86.Instructions.MOVUPD_MEMpd_XMMpd (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_11
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode11_run_of_66_memory context hosz hrep a b c e f
      modrm hmod)

/-- With `mod = 3`, a `66` prefix and `rep_prefix = 0`, in 64-bit mode with SSE2: form 8,
`MOVUPD_XMMpd_XMMpd_0F11`. -/
theorem selectLegacy1Opcode11_run_of_66_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_11 context true a b c true e f modrm = .ok 8 := by
  simp [Select_Legacy_1_Opcode_11, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-11 decoder with a `66` prefix and `rep_prefix = 0` and a register ModRM (`mod = 3`),
with SSE2 reported, runs `MOVUPD_XMMpd_XMMpd_0F11` from the state after the ModRM fetch, at `ip +
2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode11_run_of_66_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_11 ip context).run s =
      (X86.Instructions.MOVUPD_XMMpd_XMMpd_0F11 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_11
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode11_run_of_66_register context hosz hrep a b c e f
      modrm hmod)

/-- With `mod ≠ 3`, an `F2` prefix (`rep_prefix = 242`), in 64-bit mode with SSE2: form 2,
`MOVSD_XMM_MEMsd_XMMsd_1`. -/
theorem selectLegacy1Opcode11_run_of_f2_memory (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_11 context true a b c true e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_11, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-11 decoder with an `F2` prefix (`rep_prefix = 242`) and a memory ModRM (`mod ≠ 3`),
with SSE2 reported, runs `MOVSD_XMM_MEMsd_XMMsd_1` from the state after the ModRM fetch, at `ip +
2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode11_run_of_f2_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_11 ip context).run s =
      (X86.Instructions.MOVSD_XMM_MEMsd_XMMsd_1 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_11
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode11_run_of_f2_memory context hrep a b c e f
      modrm hmod)

/-- With `mod = 3`, an `F2` prefix (`rep_prefix = 242`), in 64-bit mode with SSE2: form 1,
`MOVSD_XMM_XMMsd_XMMsd_0F11`. -/
theorem selectLegacy1Opcode11_run_of_f2_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_11 context true a b c true e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_11, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-11 decoder with an `F2` prefix (`rep_prefix = 242`) and a register ModRM (`mod = 3`),
with SSE2 reported, runs `MOVSD_XMM_XMMsd_XMMsd_0F11` from the state after the ModRM fetch, at `ip +
2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode11_run_of_f2_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_11 ip context).run s =
      (X86.Instructions.MOVSD_XMM_XMMsd_XMMsd_0F11 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_11
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode11_run_of_f2_register context hrep a b c e f
      modrm hmod)

end X86Proofs
