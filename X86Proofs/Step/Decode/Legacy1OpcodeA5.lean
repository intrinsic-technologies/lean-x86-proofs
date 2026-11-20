import X86Proofs.Step.Decode

/-!
# Opcode `0F A5`: `SHLD r/m, r, CL`

The one place that looks inside lean-x86's opcode-`A5` decoder (`Decode_Legacy_1_Opcode_A5`) and its
form selection (`Select_Legacy_1_Opcode_A5`), architecture rule 5. The selection depends only on
`mod`: the register form (`mod = 3`, `SHLD_GPRv_GPRv_CL`, `Instructions/Shld/Generated/RRCl`) and
the memory form (`SHLD_MEMv_GPRv_CL`, `Instructions/Shld/Generated/MRCl`). The forms read the count
from CL. For each, a `selectLegacy1OpcodeA5_run_of_…` lemma gives the form the selection picks, and
a `decodeLegacy1OpcodeA5_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`, `ip`
the second opcode byte's address) to the call of that form at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcodeA5` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` in 64-bit mode, opcode A5's form selection picks form 1, `SHLD_GPRv_GPRv_CL`. -/
theorem selectLegacy1OpcodeA5_run_of_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_A5 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_A5, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-A5 decoder with a register ModRM runs `SHLD_GPRv_GPRv_CL` from the state after the
ModRM fetch, at `ip + 2`, with the ModRM `reg` and `rm` fields. -/
theorem decodeLegacy1OpcodeA5_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_A5 ip context).run s =
      (X86.Instructions.SHLD_GPRv_GPRv_CL (BitVec.add ip 2#64) context (modrm.extractLsb' 3 3)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_A5
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeA5_run_of_register context a b c d e f modrm hmod)

/-- With `mod ≠ 3` in 64-bit mode, opcode A5's form selection picks form 2, `SHLD_MEMv_GPRv_CL`. -/
theorem selectLegacy1OpcodeA5_run_of_memory (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_A5 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_A5, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-A5 decoder with a memory ModRM runs `SHLD_MEMv_GPRv_CL` from the state after the
ModRM fetch, at `ip + 2`, with the ModRM `mod`, `reg` and `rm` fields. -/
theorem decodeLegacy1OpcodeA5_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_A5 ip context).run s =
      (X86.Instructions.SHLD_MEMv_GPRv_CL (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_A5
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeA5_run_of_memory context a b c d e f modrm hmod)

end X86Proofs
