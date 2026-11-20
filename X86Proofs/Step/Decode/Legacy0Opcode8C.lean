import X86Proofs.Step.Decode

/-!
# Opcode `8C`: `MOV r/m, Sreg`

The one place that looks inside lean-x86's opcode-`8C` decoder (`Decode_Legacy_0_Opcode_8C`) and its
form selection (`Select_Legacy_0_Opcode_8C`), architecture rule 5. The selection depends only on
`mod`: `mod = 3` picks `MOV_GPRv_SEG` (`Instructions/MovSreg/Generated/RS`), a memory operand
`MOV_MEMw_SEG` (`Instructions/MovSreg/Generated/MS`); the forms check the ModRM `reg` field (the
segment register) themselves. A `selectLegacy0Opcode8C_run_of_…` lemma gives the form the selection
picks, and a `decodeLegacy0Opcode8C_run_of_…` lemma runs the decoder (from the ModRM fetch at
`ip + 1`) to the call of that form at `ip + 2`.

`Decode_Legacy_0`'s dispatch to this decoder is `decodeLegacy0_run_of_opcode8C`
(`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` in 64-bit mode, opcode 8C's form selection picks form 1, `MOV_GPRv_SEG`. -/
theorem selectLegacy0Opcode8C_run_of_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_0_Opcode_8C context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_8C, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-8C decoder with `mod = 3` runs `MOV_GPRv_SEG` from the state `t` after the ModRM
fetch (in 64-bit mode, decoder features answered) with `Next_IP` `ip + 2` and the ModRM `reg` (the
segment register) and `rm` fields. -/
theorem decodeLegacy0Opcode8C_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_8C ip context).run s =
      (X86.Instructions.MOV_GPRv_SEG (BitVec.add ip 2#64) context (modrm.extractLsb' 3 3)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_8C
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode8C_run_of_register context a b c d e f modrm hmod)

/-- With `mod ≠ 3` in 64-bit mode, opcode 8C's form selection picks form 2, `MOV_MEMw_SEG`. -/
theorem selectLegacy0Opcode8C_run_of_memory (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_0_Opcode_8C context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_8C, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-8C decoder with a memory ModRM (`mod ≠ 3`) runs `MOV_MEMw_SEG` from the state `t`
after the ModRM fetch at `ip + 2` (the address after the ModRM byte) with the ModRM `mod`, `reg` and
`rm` fields. -/
theorem decodeLegacy0Opcode8C_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_8C ip context).run s =
      (X86.Instructions.MOV_MEMw_SEG (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_8C
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode8C_run_of_memory context a b c d e f modrm hmod)

end X86Proofs
