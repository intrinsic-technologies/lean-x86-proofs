import X86Proofs.Step.Decode

/-!
# Opcode `8F`: group 1A (`POP r/m`)

The one place that looks inside lean-x86's opcode-`8F` decoder (`Decode_Legacy_0_Opcode_8F`) and
its form selection (`Select_Legacy_0_Opcode_8F`), architecture rule 5. For each ModRM case the
library uses — `reg = 0` with `mod = 3` (`POP r64`, `Instructions/Pop/Generated/R`) and with a
memory operand (`POP m64`, `POP m16`, `Instructions/Pop/Generated/M`) — a
`selectLegacy0Opcode8F_run_of_…` lemma gives the form the selection picks (it does not look at the
operand size), and a `decodeLegacy0Opcode8F_run_of_…` lemma runs the decoder (from the ModRM fetch
at `ip + 1`) to the call of that form at `ip + 2`. For a new case, add the pair here (the decoder
lemma is `decode_modrm_form`).

`Decode_Legacy_0`'s dispatch to this decoder is `decodeLegacy0_run_of_opcode8F`
(`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` and `reg = 0` in 64-bit mode, opcode 8F's form selection picks form 1,
`POP_GPRv_8F`. -/
theorem selectLegacy0Opcode8F_run_of_pop_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_8F context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_8F, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-8F decoder with a register ModRM and `reg = 0` runs `POP_GPRv_8F` at `ip + 2` with
the ModRM `rm` field. -/
theorem decodeLegacy0Opcode8F_run_of_pop_register [Bindings] (s t : RamState)
    (ip : BitVec 64) (context : Instruction_Context) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_8F ip context).run s =
      (X86.Instructions.POP_GPRv_8F (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_8F
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode8F_run_of_pop_register context a b c d e f
      modrm hmod hreg)

/-- With `mod ≠ 3` and `reg = 0` in 64-bit mode, opcode 8F's form selection picks form 2,
`POP_MEMv`. -/
theorem selectLegacy0Opcode8F_run_of_pop_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_8F context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_8F, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-8F decoder with a memory ModRM and `reg = 0` runs `POP_MEMv` at `ip + 2` with the
ModRM `mod` and `rm` fields. -/
theorem decodeLegacy0Opcode8F_run_of_pop_memory [Bindings] (s t : RamState)
    (ip : BitVec 64) (context : Instruction_Context) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_8F ip context).run s =
      (X86.Instructions.POP_MEMv (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_8F
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode8F_run_of_pop_memory context a b c d e f
      modrm hmod hreg)

end X86Proofs
