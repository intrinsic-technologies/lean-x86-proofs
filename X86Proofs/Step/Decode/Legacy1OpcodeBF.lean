import X86Proofs.Step.Decode

/-!
# Opcode `0F BF`: `MOVSX r, r/m16`

The one place that looks inside lean-x86's opcode-`BF` decoder (`Decode_Legacy_1_Opcode_BF`) and its
form selection (`Select_Legacy_1_Opcode_BF`), architecture rule 5. The register form (`mod = 3`,
`MOVSX_GPRv_GPR16`, `Instructions/Movsx/Generated/RR16`) takes the operand size from the context;
with a memory operand there is one form per destination size (`Instructions/Movsx/Generated/RM16`),
chosen by REX.W and the `66` prefix: `MOVSX_GPR64_MEMw_0` (REX.W), `MOVSX_GPR32_MEMw_0` (neither),
`MOVSX_GPR16_MEMw` (`66` without REX.W). For each form, a `selectLegacy1OpcodeBF_run_of_…` lemma
gives the form the selection picks, and a `decodeLegacy1OpcodeBF_run_of_…` lemma runs the decoder
(from the ModRM fetch at `ip + 1`, `ip` the second opcode byte's address) to the call of that form
at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcodeBF` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` in 64-bit mode, opcode BF's form selection picks form 4, `MOVSX_GPRv_GPR16`. -/
theorem selectLegacy1OpcodeBF_run_of_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_BF context true a b c d e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_BF, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-BF decoder with a register ModRM (`mod = 3`) runs `MOVSX_GPRv_GPR16` from the state
after the ModRM fetch, at `ip + 2`, with the ModRM `reg` and `rm` fields. -/
theorem decodeLegacy1OpcodeBF_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BF ip context).run s =
      (X86.Instructions.MOVSX_GPRv_GPR16 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BF
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1OpcodeBF_run_of_register context a b c d e f modrm hmod)

/-- With `mod ≠ 3`, `osz_prefix_present = true`, `rex_w = 0` in 64-bit mode, opcode BF's form
selection picks form 1, `MOVSX_GPR16_MEMw`. -/
theorem selectLegacy1OpcodeBF_run_of_memory16 (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hosz : context.osz_prefix_present = true) (hw : context.rex_w = 0) :
    Select_Legacy_1_Opcode_BF context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_BF, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-BF decoder with a memory ModRM (`mod ≠ 3`) and a `66` prefix without REX.W runs
`MOVSX_GPR16_MEMw` from the state after the ModRM fetch, at `ip + 2`, with the ModRM `mod`, `reg`
and `rm` fields. -/
theorem decodeLegacy1OpcodeBF_run_of_memory16 [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hosz : context.osz_prefix_present = true) (hw : context.rex_w = 0)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BF ip context).run s =
      (X86.Instructions.MOVSX_GPR16_MEMw (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BF
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1OpcodeBF_run_of_memory16 context a b c d e f modrm hmod hosz hw)

/-- With `mod ≠ 3`, `osz_prefix_present = false`, `rex_w = 0` in 64-bit mode, opcode BF's form
selection picks form 2, `MOVSX_GPR32_MEMw_0`. -/
theorem selectLegacy1OpcodeBF_run_of_memory32 (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hosz : context.osz_prefix_present = false) (hw : context.rex_w = 0) :
    Select_Legacy_1_Opcode_BF context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_BF, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-BF decoder with a memory ModRM (`mod ≠ 3`), no `66` prefix and no REX.W runs
`MOVSX_GPR32_MEMw_0` from the state after the ModRM fetch, at `ip + 2`, with the ModRM `mod`, `reg`
and `rm` fields. -/
theorem decodeLegacy1OpcodeBF_run_of_memory32 [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hosz : context.osz_prefix_present = false) (hw : context.rex_w = 0)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BF ip context).run s =
      (X86.Instructions.MOVSX_GPR32_MEMw_0 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BF
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1OpcodeBF_run_of_memory32 context a b c d e f modrm hmod hosz hw)

/-- With `mod ≠ 3`, `rex_w = 1` in 64-bit mode, opcode BF's form selection picks form 3,
`MOVSX_GPR64_MEMw_0`. -/
theorem selectLegacy1OpcodeBF_run_of_memory64 (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hw : context.rex_w = 1) :
    Select_Legacy_1_Opcode_BF context true a b c d e f modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_BF, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-BF decoder with a memory ModRM (`mod ≠ 3`) and REX.W runs `MOVSX_GPR64_MEMw_0` from
the state after the ModRM fetch, at `ip + 2`, with the ModRM `mod`, `reg` and `rm` fields. -/
theorem decodeLegacy1OpcodeBF_run_of_memory64 [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hw : context.rex_w = 1)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BF ip context).run s =
      (X86.Instructions.MOVSX_GPR64_MEMw_0 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BF
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1OpcodeBF_run_of_memory64 context a b c d e f modrm hmod hw)

end X86Proofs
