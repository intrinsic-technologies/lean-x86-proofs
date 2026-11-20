import X86Proofs.Step.Decode

/-!
# Opcode `3A`: `CMP r8, r/m8`

The one place that looks inside lean-x86's opcode-`3A` decoder (`Decode_Legacy_0_Opcode_3A`) and its
form selection (`Select_Legacy_0_Opcode_3A`), architecture rule 5. Several instruction folders use
the opcode, each through the lemmas here. For each ModRM case the library uses — `mod = 3`
(`Instructions/Cmp/Generated/R8Rev`) and a memory operand (`Instructions/Cmp/Generated/R8M8`) — a
`selectLegacy0Opcode3A_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy0Opcode3A_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`) to the
call of that form at `ip + 2`. For a new case, add the pair here (the decoder lemma is
`decode_modrm_form`).

`Decode_Legacy_0`'s dispatch to this decoder is `decodeLegacy0_run_of_opcode3A`
(`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` in 64-bit mode, opcode 3A's form selection picks form 1, `CMP_GPR8_GPR8_3A`. -/
theorem selectLegacy0Opcode3A_run_of_register (context : Instruction_Context) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_0_Opcode_3A context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_3A, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/--
The opcode-3A decoder with a register ModRM. If fetching the byte after the opcode at `ip`
returns a ModRM byte with `mod = 3` and leaves state `t` (in 64-bit mode, decoder features
answered), the decoder runs `CMP_GPR8_GPR8_3A` from `t` with `Next_IP` `ip + 2` and the ModRM
`reg` and `rm` fields.
-/
theorem decodeLegacy0Opcode3A_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_3A ip context).run s =
      (X86.Instructions.CMP_GPR8_GPR8_3A (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_3A
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode3A_run_of_register context a b c d e f modrm hmod)

/-- With `mod ≠ 3` in 64-bit mode, opcode 3A's form selection picks form 2, `CMP_GPR8_MEMb`. -/
theorem selectLegacy0Opcode3A_run_of_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_0_Opcode_3A context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_3A, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-3A decoder with a memory ModRM runs `CMP_GPR8_MEMb` from the state after the ModRM
fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode3A_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_3A ip context).run s =
      (X86.Instructions.CMP_GPR8_MEMb (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_3A
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode3A_run_of_memory context a b c d e f modrm hmod)

end X86Proofs
