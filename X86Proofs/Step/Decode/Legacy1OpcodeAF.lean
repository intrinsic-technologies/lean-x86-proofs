import X86Proofs.Step.Decode

/-!
# Opcode `0F AF`: `IMUL r, r/m`

The one place that looks inside lean-x86's opcode-`AF` decoder (`Decode_Legacy_1_Opcode_AF`) and
its form selection (`Select_Legacy_1_Opcode_AF`), architecture rule 5. The selection depends only
on `mod`: the register form (`mod = 3`, `IMUL_GPRv_GPRv`, `Instructions/Imul/Generated/RR`) and the
memory form (`IMUL_GPRv_MEMv`, `Instructions/Imul/Generated/RM`). For each, a
`selectLegacy1OpcodeAF_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy1OpcodeAF_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`, `ip` the
second opcode byte's address) to the call of that form at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcodeAF` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` in 64-bit mode, opcode AF's form selection picks form 1, `IMUL_GPRv_GPRv`. -/
theorem selectLegacy1OpcodeAF_run_of_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_AF context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_AF, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure, Except.bind,
    Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-AF decoder with a register ModRM runs `IMUL_GPRv_GPRv` from the state after the ModRM
fetch, at `ip + 2`, with the ModRM `reg` and `rm` fields. -/
theorem decodeLegacy1OpcodeAF_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_AF ip context).run s =
      (X86.Instructions.IMUL_GPRv_GPRv (BitVec.add ip 2#64) context (modrm.extractLsb' 3 3)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_AF
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeAF_run_of_register context a b c d e f modrm hmod)

/-- With `mod ≠ 3` in 64-bit mode, opcode AF's form selection picks form 2, `IMUL_GPRv_MEMv`. -/
theorem selectLegacy1OpcodeAF_run_of_memory (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_AF context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_AF, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure, Except.bind,
    Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-AF decoder with a memory ModRM runs `IMUL_GPRv_MEMv` from the state after the ModRM
fetch, at `ip + 2`, with the ModRM `mod`, `reg` and `rm` fields. -/
theorem decodeLegacy1OpcodeAF_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_AF ip context).run s =
      (X86.Instructions.IMUL_GPRv_MEMv (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_AF
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeAF_run_of_memory context a b c d e f modrm hmod)

end X86Proofs
