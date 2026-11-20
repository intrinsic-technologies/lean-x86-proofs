import X86Proofs.Step.Sse

/-!
# Opcode `0F 5B`: `CVTDQ2PS`

The one place that looks inside lean-x86's opcode-`5B` decoder (`Decode_Legacy_1_Opcode_5B`) and its
form selection (`Select_Legacy_1_Opcode_5B`), architecture rule 5. For each form the library uses, a
`selectLegacy1Opcode5B_run_of_…` lemma gives the form the selection picks (by the `66` and REP
prefixes, `mod`, and the CPUID feature it requires), and a `decodeLegacy1Opcode5B_run_of_…` lemma
runs the decoder (from the ModRM fetch at `ip + 1`, `ip` the second opcode byte's address) to the
call of that form at `ip + 2`. The decoder may diverge (`PartialSpecM`: the `66` and `F3` forms,
CVTPS2DQ and CVTTPS2DQ, convert to integers with `FP.To_Int`, and run as they are); CVTDQ2PS is
total and runs through `liftTotal`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcode5B` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod ≠ 3`, no `66` or REP prefix, in 64-bit mode with SSE2: form 1,
`CVTDQ2PS_XMMps_MEMdq`. -/
theorem selectLegacy1Opcode5B_run_of_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_5B context true a b c true e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_5B, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd, HOr.hOr,
    OrOp.or, strictOr]

/-- The opcode-`5B` decoder with no `66` or REP prefix and a memory ModRM (`mod ≠ 3`), with SSE2
reported, runs `CVTDQ2PS_XMMps_MEMdq` from the state after the ModRM fetch, at `ip + 2`, with the
ModRM fields. -/
theorem decodeLegacy1Opcode5B_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_5B ip context).run s =
      some ((X86.Instructions.CVTDQ2PS_XMMps_MEMdq (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t) := by
  unfold Decode_Legacy_1_Opcode_5B
  decode_modrm_form_sse2_partial s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode5B_run_of_memory context hosz hrep a b c e f
      modrm hmod)

/-- With `mod = 3`, no `66` or REP prefix, in 64-bit mode with SSE2: form 2,
`CVTDQ2PS_XMMps_XMMdq`. -/
theorem selectLegacy1Opcode5B_run_of_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_5B context true a b c true e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_5B, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd, HOr.hOr,
    OrOp.or, strictOr]

/-- The opcode-`5B` decoder with no `66` or REP prefix and a register ModRM (`mod = 3`), with SSE2
reported, runs `CVTDQ2PS_XMMps_XMMdq` from the state after the ModRM fetch, at `ip + 2`, with the
ModRM fields. -/
theorem decodeLegacy1Opcode5B_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_5B ip context).run s =
      some ((X86.Instructions.CVTDQ2PS_XMMps_XMMdq (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t) := by
  unfold Decode_Legacy_1_Opcode_5B
  decode_modrm_form_sse2_partial s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode5B_run_of_register context hosz hrep a b c e f
      modrm hmod)

/-- With `mod ≠ 3`, a `66` prefix and no REP prefix, in 64-bit mode with SSE2: form 3,
`CVTPS2DQ_XMMdq_MEMps`. -/
theorem selectLegacy1Opcode5B_run_of_66_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_5B context true a b c true e f modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_5B, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd, HOr.hOr,
    OrOp.or, strictOr]

/-- The opcode-`5B` decoder with a `66` prefix, no REP prefix and a memory ModRM (`mod ≠ 3`), with
SSE2 reported, runs `CVTPS2DQ_XMMdq_MEMps` (a `PartialSpecM` form) from the state after the ModRM
fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode5B_run_of_66_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_5B ip context).run s =
      (X86.Instructions.CVTPS2DQ_XMMdq_MEMps (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_5B
  decode_modrm_form_sse2_partial s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode5B_run_of_66_memory context hosz hrep a b c e f
      modrm hmod)

/-- With `mod = 3`, a `66` prefix and no REP prefix, in 64-bit mode with SSE2: form 4,
`CVTPS2DQ_XMMdq_XMMps`. -/
theorem selectLegacy1Opcode5B_run_of_66_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_5B context true a b c true e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_5B, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrep, HAnd.hAnd, AndOp.and, strictAnd, HOr.hOr,
    OrOp.or, strictOr]

/-- The opcode-`5B` decoder with a `66` prefix, no REP prefix and a register ModRM (`mod = 3`),
with SSE2 reported, runs `CVTPS2DQ_XMMdq_XMMps` (a `PartialSpecM` form) from the state after the
ModRM fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode5B_run_of_66_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hrep : context.rep_prefix = 0)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_5B ip context).run s =
      (X86.Instructions.CVTPS2DQ_XMMdq_XMMps (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_5B
  decode_modrm_form_sse2_partial s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode5B_run_of_66_register context hosz hrep a b c e f
      modrm hmod)

/-- With `mod ≠ 3` and an `F3` prefix (`rep_prefix = 243`), in 64-bit mode with SSE2: form 5,
`CVTTPS2DQ_XMMdq_MEMps`. -/
theorem selectLegacy1Opcode5B_run_of_f3_memory (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_5B context true a b c true e f modrm = .ok 5 := by
  simp [Select_Legacy_1_Opcode_5B, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd, HOr.hOr,
    OrOp.or, strictOr]

/-- The opcode-`5B` decoder with an `F3` prefix and a memory ModRM (`mod ≠ 3`), with SSE2
reported, runs `CVTTPS2DQ_XMMdq_MEMps` (a `PartialSpecM` form) from the state after the ModRM
fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode5B_run_of_f3_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_5B ip context).run s =
      (X86.Instructions.CVTTPS2DQ_XMMdq_MEMps (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_5B
  decode_modrm_form_sse2_partial s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode5B_run_of_f3_memory context hrep a b c e f modrm hmod)

/-- With `mod = 3` and an `F3` prefix (`rep_prefix = 243`), in 64-bit mode with SSE2: form 6,
`CVTTPS2DQ_XMMdq_XMMps`. -/
theorem selectLegacy1Opcode5B_run_of_f3_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_5B context true a b c true e f modrm = .ok 6 := by
  simp [Select_Legacy_1_Opcode_5B, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd, HOr.hOr,
    OrOp.or, strictOr]

/-- The opcode-`5B` decoder with an `F3` prefix and a register ModRM (`mod = 3`), with SSE2
reported, runs `CVTTPS2DQ_XMMdq_XMMps` (a `PartialSpecM` form) from the state after the ModRM
fetch, at `ip + 2`, with the ModRM fields. -/
theorem decodeLegacy1Opcode5B_run_of_f3_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_5B ip context).run s =
      (X86.Instructions.CVTTPS2DQ_XMMdq_XMMps (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_5B
  decode_modrm_form_sse2_partial s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode5B_run_of_f3_register context hrep a b c e f modrm hmod)

end X86Proofs
