import X86Proofs.Step.Decode

/-!
# Opcode `0F B6`: `MOVZX r, r/m8`

The one place that looks inside lean-x86's opcode-`B6` decoder (`Decode_Legacy_1_Opcode_B6`) and its
form selection (`Select_Legacy_1_Opcode_B6`), architecture rule 5. The selection depends only on
`mod`: the register form (`mod = 3`, `MOVZX_GPRv_GPR8`, `Instructions/Movzx/Generated/RR8`) and the
memory form (`MOVZX_GPRv_MEMb_1`, `RM8`). For each form, a `selectLegacy1OpcodeB6_run_of_…` lemma
gives the form the selection picks, and a `decodeLegacy1OpcodeB6_run_of_…` lemma runs the decoder
(from the ModRM fetch at `ip + 1`, `ip` the second opcode byte's address) to the call of that form
at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcodeB6` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` in 64-bit mode, opcode B6's form selection picks form 1, `MOVZX_GPRv_GPR8`. -/
theorem selectLegacy1OpcodeB6_run_of_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_B6 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_B6, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-B6 decoder with a register ModRM (`mod = 3`) runs `MOVZX_GPRv_GPR8` from the state
after the ModRM fetch, at `ip + 2`, with the ModRM `reg` and `rm` fields. -/
theorem decodeLegacy1OpcodeB6_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_B6 ip context).run s =
      (X86.Instructions.MOVZX_GPRv_GPR8 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_B6
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1OpcodeB6_run_of_register context a b c d e f modrm hmod)

/-- With `mod ≠ 3` in 64-bit mode, opcode B6's form selection picks form 2, `MOVZX_GPRv_MEMb_1`. -/
theorem selectLegacy1OpcodeB6_run_of_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_B6 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_B6, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-B6 decoder with a memory ModRM (`mod ≠ 3`) runs `MOVZX_GPRv_MEMb_1` from the state
after the ModRM fetch, at `ip + 2`, with the ModRM `mod`, `reg` and `rm` fields. -/
theorem decodeLegacy1OpcodeB6_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_B6 ip context).run s =
      (X86.Instructions.MOVZX_GPRv_MEMb_1 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_B6
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1OpcodeB6_run_of_memory context a b c d e f modrm hmod)

end X86Proofs
