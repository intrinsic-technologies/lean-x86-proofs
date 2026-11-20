import X86Proofs.Step.Decode

/-!
# Opcodes `0F 40`–`0F 4F`: `CMOVcc r, r/m`

The one place that looks inside lean-x86's opcode-`40` decoder (`Decode_Legacy_1_Opcode_40`) and
its form selection (`Select_Legacy_1_Opcode_40`), architecture rule 5. The decoders of `41`–`4F`
and their forms (`CMOVNO_GPRv_GPRv`, …) are copies of these, equal by `rfl`, and
`Decode_Legacy_1` hands each the opcode byte, whose low four bits the form takes as the condition;
so `decodeLegacy1_run_of_cmovOpcode` (`Step/Escape.lean`) dispatches all sixteen to the `40`
decoder, and these lemmas cover every condition. The selection depends only on `mod`: the
register form (`mod = 3`, `CMOVO_GPRv_GPRv`, `Instructions/Cmov/Generated/RR`) and the memory
form (`CMOVO_GPRv_MEMv`, `RM`). For each, a `selectLegacy1Opcode40_run_of_…` lemma gives the form
the selection picks, and a `decodeLegacy1Opcode40_run_of_…` lemma runs the decoder (from the ModRM
fetch at `ip + 1`, `ip` the second opcode byte's address) to the call of that form at `ip + 2`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` in 64-bit mode, opcode 40's form selection picks form 1, `CMOVO_GPRv_GPRv`. -/
theorem selectLegacy1Opcode40_run_of_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_40 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_40, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-40 decoder with a register ModRM (`mod = 3`) runs `CMOVO_GPRv_GPRv` from the state
after the ModRM fetch, at `ip + 2`, with the ModRM `reg` and `rm` fields and the opcode byte. -/
theorem decodeLegacy1Opcode40_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (op modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_40 ip context op).run s =
      (X86.Instructions.CMOVO_GPRv_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) op).run t := by
  unfold Decode_Legacy_1_Opcode_40
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1Opcode40_run_of_register context a b c d e f modrm hmod)

/-- With `mod ≠ 3` in 64-bit mode, opcode 40's form selection picks form 2, `CMOVO_GPRv_MEMv`. -/
theorem selectLegacy1Opcode40_run_of_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_40 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_40, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-40 decoder with a memory ModRM (`mod ≠ 3`) runs `CMOVO_GPRv_MEMv` from the state
after the ModRM fetch, at `ip + 2`, with the ModRM `mod`, `reg` and `rm` fields and the opcode
byte. -/
theorem decodeLegacy1Opcode40_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (op modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_40 ip context op).run s =
      (X86.Instructions.CMOVO_GPRv_MEMv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) op).run t := by
  unfold Decode_Legacy_1_Opcode_40
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1Opcode40_run_of_memory context a b c d e f modrm hmod)

end X86Proofs
