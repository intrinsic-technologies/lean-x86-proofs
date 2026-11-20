import X86Proofs.Step.Sse

/-!
# Opcode `0F 10`: `MOVUPS`, `MOVUPD`, `MOVSS xmm, xmm/m`, `MOVSD xmm, xmm/m`

The one place that looks inside lean-x86's opcode-`10` decoder (`Decode_Legacy_1_Opcode_10`) and its
form selection (`Select_Legacy_1_Opcode_10`), architecture rule 5. In 64-bit mode the selection
picks, for `mod ≠ 3` / `mod = 3`: without a `66` or REP prefix and with SSE, `MOVUPS_XMMps_MEMps`
(`Instructions/Movups`, hand-written) / `MOVUPS_XMMps_XMMps_0F10`; after `66` with SSE2,
`MOVUPD_XMMpd_MEMpd` / `MOVUPD_XMMpd_XMMpd_0F10`; after `F3` with SSE, `MOVSS_XMMdq_MEMss_1` /
`MOVSS_XMMss_XMMss_0F10`; after `F2` with SSE2, `MOVSD_XMM_XMMdq_MEMsd_1` /
`MOVSD_XMM_XMMsd_XMMsd_0F10` (`Instructions/{Movups,Movupd,Movss,Movsd}/Generated`). For each,
a `selectLegacy1Opcode10_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy1Opcode10_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`, `ip`
the second opcode byte's address) to the call of that form at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcode10` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod ≠ 3`, no `66`/`F2`/`F3` prefix, in 64-bit mode with SSE: form 5,
`MOVUPS_XMMps_MEMps`. -/
theorem selectLegacy1Opcode10_run_of_memory (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0) (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_10 context true a b true d e f modrm = .ok 5 := by
  simp [Select_Legacy_1_Opcode_10, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/--
The opcode-`0F 10` decoder with a memory ModRM (`mod ≠ 3`). If fetching the byte after the opcode
at `ip` returns the ModRM byte and leaves state `t` (in 64-bit mode, decoder features answered,
SSE reported), the decoder runs `MOVUPS_XMMps_MEMps` from `t` with `ip + 2` and the ModRM fields.
-/
theorem decodeLegacy1Opcode10_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_10 ip context).run s =
      (X86.Instructions.MOVUPS_XMMps_MEMps (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_10
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 5 3) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run_sse t (fun mode a b c d e f =>
    Select_Legacy_1_Opcode_10 context mode a b c d e f modrm) _ 5 hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode10_run_of_memory context hosz hrep a b d e f modrm hmod)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

/-- With `mod ≠ 3`, an `F3` prefix (`rep_prefix = 243`), in 64-bit mode with SSE: form 3,
`MOVSS_XMMdq_MEMss_1`. -/
theorem selectLegacy1Opcode10_run_of_f3_memory (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_10 context true a b true d e f modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_10, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-10 decoder with an `F3` prefix (`rep_prefix = 243`) and a memory ModRM (`mod ≠ 3`),
with SSE reported, runs `MOVSS_XMMdq_MEMss_1` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1Opcode10_run_of_f3_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_10 ip context).run s =
      (X86.Instructions.MOVSS_XMMdq_MEMss_1 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_10
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode10_run_of_f3_memory context hrep a b d e f
      modrm hmod)

/-- With `mod = 3`, an `F3` prefix (`rep_prefix = 243`), in 64-bit mode with SSE: form 4,
`MOVSS_XMMss_XMMss_0F10`. -/
theorem selectLegacy1Opcode10_run_of_f3_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_10 context true a b true d e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_10, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-10 decoder with an `F3` prefix (`rep_prefix = 243`) and a register ModRM (`mod = 3`),
with SSE reported, runs `MOVSS_XMMss_XMMss_0F10` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1Opcode10_run_of_f3_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_10 ip context).run s =
      (X86.Instructions.MOVSS_XMMss_XMMss_0F10 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_10
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode10_run_of_f3_register context hrep a b d e f
      modrm hmod)

/-- With `mod = 3`, no `66` prefix and `rep_prefix = 0`, in 64-bit mode with SSE: form 6,
`MOVUPS_XMMps_XMMps_0F10`. -/
theorem selectLegacy1Opcode10_run_of_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (a b d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_10 context true a b true d e f modrm = .ok 6 := by
  simp [Select_Legacy_1_Opcode_10, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-10 decoder with no `66` prefix and `rep_prefix = 0` and a register ModRM (`mod = 3`),
with SSE reported, runs `MOVUPS_XMMps_XMMps_0F10` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1Opcode10_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_10 ip context).run s =
      (X86.Instructions.MOVUPS_XMMps_XMMps_0F10 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_10
  decode_modrm_form_sse s t ip hfetch hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode10_run_of_register context hosz hrep a b d e f
      modrm hmod)

/-- With `mod ≠ 3`, a `66` prefix and `rep_prefix = 0`, in 64-bit mode with SSE2: form 7,
`MOVUPD_XMMpd_MEMpd`. -/
theorem selectLegacy1Opcode10_run_of_66_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_10 context true a b c true e f modrm = .ok 7 := by
  simp [Select_Legacy_1_Opcode_10, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-10 decoder with a `66` prefix and `rep_prefix = 0` and a memory ModRM (`mod ≠ 3`),
with SSE2 reported, runs `MOVUPD_XMMpd_MEMpd` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM fields. -/
theorem decodeLegacy1Opcode10_run_of_66_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_10 ip context).run s =
      (X86.Instructions.MOVUPD_XMMpd_MEMpd (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_10
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode10_run_of_66_memory context hosz hrep a b c e f
      modrm hmod)

/-- With `mod = 3`, a `66` prefix and `rep_prefix = 0`, in 64-bit mode with SSE2: form 8,
`MOVUPD_XMMpd_XMMpd_0F10`. -/
theorem selectLegacy1Opcode10_run_of_66_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_10 context true a b c true e f modrm = .ok 8 := by
  simp [Select_Legacy_1_Opcode_10, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-10 decoder with a `66` prefix and `rep_prefix = 0` and a register ModRM (`mod = 3`),
with SSE2 reported, runs `MOVUPD_XMMpd_XMMpd_0F10` from the state after the ModRM fetch, at `ip +
2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode10_run_of_66_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_10 ip context).run s =
      (X86.Instructions.MOVUPD_XMMpd_XMMpd_0F10 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_10
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode10_run_of_66_register context hosz hrep a b c e f
      modrm hmod)

/-- With `mod ≠ 3`, an `F2` prefix (`rep_prefix = 242`), in 64-bit mode with SSE2: form 1,
`MOVSD_XMM_XMMdq_MEMsd_1`. -/
theorem selectLegacy1Opcode10_run_of_f2_memory (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_10 context true a b c true e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_10, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-10 decoder with an `F2` prefix (`rep_prefix = 242`) and a memory ModRM (`mod ≠ 3`),
with SSE2 reported, runs `MOVSD_XMM_XMMdq_MEMsd_1` from the state after the ModRM fetch, at `ip +
2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode10_run_of_f2_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_10 ip context).run s =
      (X86.Instructions.MOVSD_XMM_XMMdq_MEMsd_1 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_10
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode10_run_of_f2_memory context hrep a b c e f
      modrm hmod)

/-- With `mod = 3`, an `F2` prefix (`rep_prefix = 242`), in 64-bit mode with SSE2: form 2,
`MOVSD_XMM_XMMsd_XMMsd_0F10`. -/
theorem selectLegacy1Opcode10_run_of_f2_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_10 context true a b c true e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_10, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-10 decoder with an `F2` prefix (`rep_prefix = 242`) and a register ModRM (`mod = 3`),
with SSE2 reported, runs `MOVSD_XMM_XMMsd_XMMsd_0F10` from the state after the ModRM fetch, at `ip +
2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode10_run_of_f2_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_10 ip context).run s =
      (X86.Instructions.MOVSD_XMM_XMMsd_XMMsd_0F10 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_10
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode10_run_of_f2_register context hrep a b c e f
      modrm hmod)

end X86Proofs
