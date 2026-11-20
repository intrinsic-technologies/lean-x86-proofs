import X86Proofs.Step.Decode

/-!
# Opcodes `0F 90`–`0F 9F`: `SETcc r/m8`

The one place that looks inside lean-x86's opcode-`90` decoder (`Decode_Legacy_1_Opcode_90`) and
its form selection (`Select_Legacy_1_Opcode_90`), architecture rule 5. The decoders of `91`–`9F`
and their forms (`SETNO_GPR8`, …) are copies of these, equal by `rfl`, and `Decode_Legacy_1`
hands each the opcode byte, whose low four bits the form takes as the condition; so
`decodeLegacy1_run_of_setccOpcode` (`Step/Escape.lean`) dispatches all sixteen to the `90` decoder,
and these lemmas cover every condition. The selection depends only on `mod` (the ModRM `reg` field
is ignored): the register form (`mod = 3`, `SETO_GPR8`, `Instructions/Setcc/Generated/R8`) and the
memory form (`SETO_MEMb`, `M8`). For each, a `selectLegacy1Opcode90_run_of_…` lemma gives the form
the selection picks, and a `decodeLegacy1Opcode90_run_of_…` lemma runs the decoder (from the ModRM
fetch at `ip + 1`, `ip` the second opcode byte's address) to the call of that form at `ip + 2`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` in 64-bit mode, opcode 90's form selection picks form 1, `SETO_GPR8`. -/
theorem selectLegacy1Opcode90_run_of_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_90 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_90, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-90 decoder with a register ModRM (`mod = 3`) runs `SETO_GPR8` from the state after
the ModRM fetch, at `ip + 2`, with the ModRM `rm` field and the opcode byte. -/
theorem decodeLegacy1Opcode90_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (op modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_90 ip context op).run s =
      (X86.Instructions.SETO_GPR8 (BitVec.add ip 2#64) context (modrm.extractLsb' 0 3) op).run
        t := by
  unfold Decode_Legacy_1_Opcode_90
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1Opcode90_run_of_register context a b c d e f modrm hmod)

/-- With `mod ≠ 3` in 64-bit mode, opcode 90's form selection picks form 2, `SETO_MEMb`. -/
theorem selectLegacy1Opcode90_run_of_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_90 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_90, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-90 decoder with a memory ModRM (`mod ≠ 3`) runs `SETO_MEMb` from the state after
the ModRM fetch, at `ip + 2`, with the ModRM `mod` and `rm` fields and the opcode byte. -/
theorem decodeLegacy1Opcode90_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (op modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_90 ip context op).run s =
      (X86.Instructions.SETO_MEMb (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3) op).run t := by
  unfold Decode_Legacy_1_Opcode_90
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1Opcode90_run_of_memory context a b c d e f modrm hmod)

end X86Proofs
