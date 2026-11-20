import X86Proofs.Step.Decode

/-!
# Opcode `0F A3`: `BT r/m, r`

The one place that looks inside lean-x86's opcode-`A3` decoder (`Decode_Legacy_1_Opcode_A3`) and its
form selection (`Select_Legacy_1_Opcode_A3`), architecture rule 5. The library uses the register
form (`mod = 3`, `BT_GPRv_GPRv`, `Instructions/Bt/Generated/RR`) and the memory form
(`mod ≠ 3`, `BT_MEMv_GPRv`, `Instructions/Bt/Generated/MR`), whose register bit
offset also moves the address (`bitStringOffset`). For each, a `selectLegacy1OpcodeA3_run_of_…`
lemma gives the form the selection picks, and a `decodeLegacy1OpcodeA3_run_of_…` lemma runs the
decoder (from the ModRM fetch at `ip + 1`, `ip` the second opcode byte's address) to the call of
that form at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcodeA3` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` in 64-bit mode, opcode A3's form selection picks form 1, `BT_GPRv_GPRv`. -/
theorem selectLegacy1OpcodeA3_run_of_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_A3 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_A3, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-A3 decoder with a register ModRM (`mod = 3`) runs `BT_GPRv_GPRv` from the state after
the ModRM fetch, at `ip + 2`, with the ModRM `reg` and `rm` fields. -/
theorem decodeLegacy1OpcodeA3_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_A3 ip context).run s =
      (X86.Instructions.BT_GPRv_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_A3
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeA3_run_of_register context a b c d e f modrm hmod)

/-- With `mod ≠ 3` in 64-bit mode, opcode A3's form selection picks form 2,
`BT_MEMv_GPRv`. -/
theorem selectLegacy1OpcodeA3_run_of_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_A3 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_A3, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-A3 decoder with a memory ModRM (`mod ≠ 3`) runs `BT_MEMv_GPRv` from the
state after the ModRM fetch, at `ip + 2`, with the ModRM `mod`, `reg` and `rm` fields. -/
theorem decodeLegacy1OpcodeA3_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_A3 ip context).run s =
      (X86.Instructions.BT_MEMv_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_A3
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1OpcodeA3_run_of_memory context a b c d e f modrm hmod)

end X86Proofs
