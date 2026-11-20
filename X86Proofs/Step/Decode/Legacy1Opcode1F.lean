import X86Proofs.Step.Decode

/-!
# Opcode `0F 1F`: `NOP r/m` (the multi-byte NOP)

The one place that looks inside lean-x86's opcode-`0F 1F` decoder (`Decode_Legacy_1_Opcode_1F`) and
its form selection (`Select_Legacy_1_Opcode_1F`), architecture rule 5. For each ModRM case the
library uses — `reg = 0` with `mod = 3` (`Instructions/Nop`) and with a memory operand
(`Instructions/NopMem`) — a `selectLegacy1Opcode1F_run_of_…` lemma gives the form the selection
picks, and a `decodeLegacy1Opcode1F_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip +
1`, `ip` the second opcode byte's address) to the call of that form at `ip + 2`.

`Decode_Legacy_1`'s dispatch to this decoder is `decodeLegacy1_run_of_opcode1F`
(`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` and `reg = 0` in 64-bit mode, opcode `0F 1F`'s form selection picks form 1,
`NOP_GPRv_0F1F`. -/
theorem selectLegacy1Opcode1F_run_of_nop_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_1_Opcode_1F context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_1F, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/--
The opcode-`0F 1F` decoder with a register ModRM and `reg = 0`. If fetching the byte after the
second opcode byte at `ip` returns a ModRM byte with `mod = 3` and `reg = 0` and leaves state `t`
(in 64-bit mode, decoder features answered), the decoder runs `NOP_GPRv_0F1F` from `t` with
`Next_IP` `ip + 2`.
-/
theorem decodeLegacy1Opcode1F_run_of_nop_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_1F ip context).run s =
      (X86.Instructions.NOP_GPRv_0F1F (BitVec.add ip 2#64) context).run t := by
  unfold Decode_Legacy_1_Opcode_1F
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1Opcode1F_run_of_nop_register context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3` and `reg = 0` in 64-bit mode, opcode `0F 1F`'s form selection picks form 2,
`NOP_MEMv_0F1F`. -/
theorem selectLegacy1Opcode1F_run_of_nop_memory (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_1_Opcode_1F context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_1F, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/--
The opcode-`0F 1F` decoder with a memory ModRM and `reg = 0`. If fetching the byte after the
second opcode byte at `ip` returns a ModRM byte with `mod ≠ 3` and `reg = 0` and leaves state `t`
(in 64-bit mode, decoder features answered), the decoder runs `NOP_MEMv_0F1F` from `t` at `ip + 2`
(the address after the ModRM byte) with the ModRM `mod` and `rm` fields.
-/
theorem decodeLegacy1Opcode1F_run_of_nop_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_1F ip context).run s =
      (X86.Instructions.NOP_MEMv_0F1F (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_1F
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1Opcode1F_run_of_nop_memory context a b c d e f modrm hmod hreg)

end X86Proofs
