import X86Proofs.Step.Decode

/-!
# Opcode `0F 1E`: `ENDBR64`

The one place that looks inside lean-x86's opcode-`1E` decoder (`Decode_Legacy_1_Opcode_1E`) and its
form selection (`Select_Legacy_1_Opcode_1E`), architecture rule 5, for the ModRM byte `FA` after
`F3` (`F3 0F 1E FA`, ENDBR64). The selection depends on the CPUID CET_SS feature: reported, it picks
`ENDBR64` (form 1); not reported, the reserved NOP `NOP_GPRv_GPRv_0F1E` (form 16). Both run at
`ip + 2` (`Instructions/Endbr64`); the decoder lemma takes the feature's answer `cet`
(`decode_modrm_form_cetSS`). With a memory operand it picks the reserved NOP `NOP_MEMv_GPRv_0F1E`
(form 2) whatever the prefixes (`…_run_of_nop_memory`, `Instructions/Nop/Generated/M1E`). The other
forms of `0F 1E` (the CET shadow-stack instructions and the other reserved register NOPs) are not
covered.

The dispatch to this decoder is `decodeLegacy1_run_of_opcode1E` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With ModRM `FA`, `F3` and the CPUID CET_SS feature in 64-bit mode, opcode 1E's form selection
picks form 1, `ENDBR64`. -/
theorem selectLegacy1Opcode1E_run_of_endbr64 (context : Instruction_Context)
    (hrep : context.rep_prefix = 243) (a b c d f : Bool) :
    Select_Legacy_1_Opcode_1E context true a b c d true f 0xFA = .ok 1 := by
  simp [Select_Legacy_1_Opcode_1E, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- With ModRM `FA` and `F3` in 64-bit mode, without the CPUID CET_SS feature, opcode 1E's form
selection picks form 16, `NOP_GPRv_GPRv_0F1E`. -/
theorem selectLegacy1Opcode1E_run_of_endbr64_nop (context : Instruction_Context)
    (hrep : context.rep_prefix = 243) (a b c d f : Bool) :
    Select_Legacy_1_Opcode_1E context true a b c d false f 0xFA = .ok 16 := by
  simp [Select_Legacy_1_Opcode_1E, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hrep, HAnd.hAnd, AndOp.and, strictAnd, HOr.hOr, OrOp.or, strictOr]

/-- The opcode-1E decoder with ModRM `FA` and `F3` runs, from the state after the ModRM fetch at
`ip + 2`, `ENDBR64` if CPUID reports CET_SS (`cet = true`), else `NOP_GPRv_GPRv_0F1E`. -/
theorem decodeLegacy1Opcode1E_run_of_endbr64 [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode t) (hf : DecoderFeatures t) (cet : Bool)
    (hc : Prelude.ReportsCPUFeature Bindings.processor t CPUID_CET_SS_Encoding cet)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok 0xFA, t)) :
    (Decode_Legacy_1_Opcode_1E ip context).run s =
      (if cet then X86.Instructions.ENDBR64 (BitVec.add ip 2#64) context
        else X86.Instructions.NOP_GPRv_GPRv_0F1E (BitVec.add ip 2#64) context).run t := by
  unfold Decode_Legacy_1_Opcode_1E
  cases cet
  · decode_modrm_form_cetSS s t ip hfetch hmode hf hc
      (fun a b c d f => selectLegacy1Opcode1E_run_of_endbr64_nop context hrep a b c d f)
  · decode_modrm_form_cetSS s t ip hfetch hmode hf hc
      (fun a b c d f => selectLegacy1Opcode1E_run_of_endbr64 context hrep a b c d f)

/-- With `mod ≠ 3` in 64-bit mode, opcode 1E's form selection picks form 2, the reserved NOP
`NOP_MEMv_GPRv_0F1E`, whatever the prefixes and CPUID features. -/
theorem selectLegacy1Opcode1E_run_of_nop_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_1E context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_1E, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-1E decoder with a memory ModRM (`mod ≠ 3`) runs `NOP_MEMv_GPRv_0F1E` from the state
`t` after the ModRM fetch (in 64-bit mode, decoder features answered), at `ip + 2` (the address
after the ModRM byte) with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy1Opcode1E_run_of_nop_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_1E ip context).run s =
      (X86.Instructions.NOP_MEMv_GPRv_0F1E (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_1E
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1Opcode1E_run_of_nop_memory context a b c d e f modrm hmod)

end X86Proofs
