import X86Proofs.Step.Sse

/-!
# Opcode `0F 6C`: `PUNPCKLQDQ`

The one place that looks inside lean-x86's opcode-`6C` decoder (`Decode_Legacy_1_Opcode_6C`) and its
form selection (`Select_Legacy_1_Opcode_6C`), architecture rule 5. In 64-bit mode the selection
picks, after `66` and with SSE2, `PUNPCKLQDQ_XMMdq_XMMq` for `mod = 3` and `PUNPCKLQDQ_XMMdq_MEMdq`
otherwise (`Instructions/Punpcklqdq/Generated/{XX,XM}`). For each, a
`selectLegacy1Opcode6C_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy1Opcode6C_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`, `ip` the
second opcode byte's address) to the call of that form at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcode6C` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod ≠ 3` and a `66` prefix in 64-bit mode, with SSE2: form 1, `PUNPCKLQDQ_XMMdq_MEMdq`. -/
theorem selectLegacy1Opcode6C_run_of_66_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_6C context true a b c true e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_6C, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-6C decoder with a `66` prefix and a memory ModRM (`mod ≠ 3`), with SSE2 reported,
runs `PUNPCKLQDQ_XMMdq_MEMdq` from the state after the ModRM fetch, at `ip + 2`, with the ModRM
fields. -/
theorem decodeLegacy1Opcode6C_run_of_66_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_6C ip context).run s =
      (X86.Instructions.PUNPCKLQDQ_XMMdq_MEMdq (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_6C
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode6C_run_of_66_memory context hosz a b c e f modrm hmod)

/-- With `mod = 3` and a `66` prefix in 64-bit mode, with SSE2: form 2, `PUNPCKLQDQ_XMMdq_XMMq`. -/
theorem selectLegacy1Opcode6C_run_of_66_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_6C context true a b c true e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_6C, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-6C decoder with a `66` prefix and a register ModRM (`mod = 3`), with SSE2 reported,
runs `PUNPCKLQDQ_XMMdq_XMMq` from the state after the ModRM fetch, at `ip + 2`, with the ModRM
fields. -/
theorem decodeLegacy1Opcode6C_run_of_66_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_6C ip context).run s =
      (X86.Instructions.PUNPCKLQDQ_XMMdq_XMMq (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_6C
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode6C_run_of_66_register context hosz a b c e f modrm hmod)

end X86Proofs
