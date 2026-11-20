import X86Proofs.Step.Decode

/-!
# Opcode `0F BD`: `BSR r, r/m`

The one place that looks inside lean-x86's opcode-`BD` decoder (`Decode_Legacy_1_Opcode_BD`) and its
form selection (`Select_Legacy_1_Opcode_BD`), architecture rule 5. Without a REP prefix the
selection depends only on `mod`: the register form (`mod = 3`, `BSR_GPRv_GPRv_0`,
`Instructions/Bsr/Generated/RR`) and the memory form (`BSR_GPRv_MEMv_0`, `RM`). With `F3` it picks
LZCNT or BSR by the CPUID LZCNT feature: with LZCNT reported, `LZCNT_GPRv_GPRv` and
`LZCNT_GPRv_MEMv` (`Instructions/Lzcnt/Generated/RR`, `RM`; the decoder lemmas take the feature's
answer, `decode_modrm_form_lzcnt`). For each, a
`selectLegacy1OpcodeBD_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy1OpcodeBD_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`, `ip` the
second opcode byte's address) to the call of that form at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcodeBD` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3`, no REP prefix in 64-bit mode, opcode BD's form selection picks form 3,
`BSR_GPRv_GPRv_0`. -/
theorem selectLegacy1OpcodeBD_run_of_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 0)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_BD context true a b c d e f modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_BD, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd,
    HOr.hOr, OrOp.or, strictOr]

/-- The opcode-BD decoder with a register ModRM (`mod = 3`, no REP prefix) runs `BSR_GPRv_GPRv_0`
from the state after the ModRM fetch, at `ip + 2`, with the ModRM `reg` and `rm` fields. -/
theorem decodeLegacy1OpcodeBD_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BD ip context).run s =
      (X86.Instructions.BSR_GPRv_GPRv_0 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BD
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeBD_run_of_register context hrep a b c d e f modrm hmod)

/-- With `mod ≠ 3`, no REP prefix in 64-bit mode, opcode BD's form selection picks form 4,
`BSR_GPRv_MEMv_0`. -/
theorem selectLegacy1OpcodeBD_run_of_memory (context : Instruction_Context)
    (hrep : context.rep_prefix = 0)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_BD context true a b c d e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_BD, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd,
    HOr.hOr, OrOp.or, strictOr]

/-- The opcode-BD decoder with a memory ModRM (`mod ≠ 3`, no REP prefix) runs `BSR_GPRv_MEMv_0` from
the state after the ModRM fetch, at `ip + 2`, with the ModRM `mod`, `reg` and `rm` fields. -/
theorem decodeLegacy1OpcodeBD_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BD ip context).run s =
      (X86.Instructions.BSR_GPRv_MEMv_0 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BD
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeBD_run_of_memory context hrep a b c d e f modrm hmod)

/-- With `mod = 3`, `F3` and the CPUID LZCNT feature in 64-bit mode, opcode BD's form selection
picks form 1, `LZCNT_GPRv_GPRv`. -/
theorem selectLegacy1OpcodeBD_run_of_lzcnt_register (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_BD context true true b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_BD, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-BD decoder with a register ModRM (`mod = 3`), `F3` and LZCNT reported runs
`LZCNT_GPRv_GPRv` from the state after the ModRM fetch, at `ip + 2`, with the ModRM `reg` and
`rm` fields. -/
theorem decodeLegacy1OpcodeBD_run_of_lzcnt_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hl : Prelude.ReportsCPUFeature Bindings.processor t CPUID_LZCNT_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BD ip context).run s =
      (X86.Instructions.LZCNT_GPRv_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BD
  decode_modrm_form_lzcnt s t ip hfetch hmode hf hl
    (fun b c d e f => selectLegacy1OpcodeBD_run_of_lzcnt_register context hrep b c d e f modrm hmod)

/-- With `mod ≠ 3`, `F3` and the CPUID LZCNT feature in 64-bit mode, opcode BD's form selection
picks form 2, `LZCNT_GPRv_MEMv`. -/
theorem selectLegacy1OpcodeBD_run_of_lzcnt_memory (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_BD context true true b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_BD, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hrep, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-BD decoder with a memory ModRM (`mod ≠ 3`), `F3` and LZCNT reported runs
`LZCNT_GPRv_MEMv` from the state after the ModRM fetch, at `ip + 2`, with the ModRM `mod`, `reg`
and `rm` fields. -/
theorem decodeLegacy1OpcodeBD_run_of_lzcnt_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hl : Prelude.ReportsCPUFeature Bindings.processor t CPUID_LZCNT_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BD ip context).run s =
      (X86.Instructions.LZCNT_GPRv_MEMv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BD
  decode_modrm_form_lzcnt s t ip hfetch hmode hf hl
    (fun b c d e f => selectLegacy1OpcodeBD_run_of_lzcnt_memory context hrep b c d e f modrm hmod)

end X86Proofs
