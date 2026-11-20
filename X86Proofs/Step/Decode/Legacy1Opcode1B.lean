import X86Proofs.Step.Decode

/-!
# Opcode `0F 1B`: reserved hint NOP `NOP r/m, r`

The one place that looks inside lean-x86's opcode-`0F 1B` decoder (`Decode_Legacy_1_Opcode_1B`) and
its form selection (`Select_Legacy_1_Opcode_1B`), architecture rule 5. For each ModRM case the
library uses (`mod = 3`, `NOP_GPRv_GPRv_0F1B`, and a memory operand, `NOP_MEMv_GPRv_0F1B`; any
`reg`; `Instructions/Nop/Generated`), a `selectLegacy1Opcode1B_run_of_…` lemma gives the form the
selection picks, and a `decodeLegacy1Opcode1B_run_of_…` lemma runs the decoder (from the ModRM fetch
at `ip + 1`, `ip` the second opcode byte's address) to the call of that form at `ip + 2`.

`Decode_Legacy_1`'s dispatch to this decoder is `decodeLegacy1_run_of_opcode1B`
(`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` in 64-bit mode, opcode `0F 1B`'s form selection picks form 2,
`NOP_GPRv_GPRv_0F1B`. -/
theorem selectLegacy1Opcode1B_run_of_nop_register (context : Instruction_Context)
    (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_1B context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_1B, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`0F 1B` decoder with `mod = 3` runs `NOP_GPRv_GPRv_0F1B` from the state `t` after the
ModRM fetch (in 64-bit mode, decoder features answered), with `Next_IP` `ip + 2`. -/
theorem decodeLegacy1Opcode1B_run_of_nop_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_1B ip context).run s =
      (X86.Instructions.NOP_GPRv_GPRv_0F1B (BitVec.add ip 2#64) context).run t := by
  unfold Decode_Legacy_1_Opcode_1B
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1Opcode1B_run_of_nop_register context a b c d e f modrm hmod)

/-- With `mod ≠ 3` in 64-bit mode, opcode `0F 1B`'s form selection picks form 1,
`NOP_MEMv_GPRv_0F1B`. -/
theorem selectLegacy1Opcode1B_run_of_nop_memory (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_1B context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_1B, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`0F 1B` decoder with `mod ≠ 3` runs `NOP_MEMv_GPRv_0F1B` from the state `t` after the
ModRM fetch (in 64-bit mode, decoder features answered), at `ip + 2` (the address after the ModRM
byte) with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy1Opcode1B_run_of_nop_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_1B ip context).run s =
      (X86.Instructions.NOP_MEMv_GPRv_0F1B (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_1B
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1Opcode1B_run_of_nop_memory context a b c d e f modrm hmod)

end X86Proofs
