import X86Proofs.Step.Decode

/-!
# Opcode `0B`: `OR r, r/m`

The one place that looks inside lean-x86's opcode-`0B` decoder (`Decode_Legacy_0_Opcode_0B`) and its
form selection (`Select_Legacy_0_Opcode_0B`), architecture rule 5. Several instruction folders use
the opcode, each through the lemmas here. For each ModRM case the library uses — `mod = 3`
(`Instructions/Or/Generated/Rev`) and a memory operand (`Instructions/Or/Generated/RM`) — a
`selectLegacy0Opcode0B_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy0Opcode0B_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`) to the
call of that form at `ip + 2`. For a new case, add the pair here (the decoder lemma is
`decode_modrm_form`).

`Decode_Legacy_0`'s dispatch to this decoder is `decodeLegacy0_run_of_opcode0B`
(`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` in 64-bit mode, opcode 0B's form selection picks form 1, `OR_GPRv_GPRv_0B`. -/
theorem selectLegacy0Opcode0B_run_of_register (context : Instruction_Context) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_0_Opcode_0B context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_0B, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/--
The opcode-0B decoder with a register ModRM. If fetching the byte after the opcode at `ip`
returns a ModRM byte with `mod = 3` and leaves state `t` (in 64-bit mode, decoder features
answered), the decoder runs `OR_GPRv_GPRv_0B` from `t` with `Next_IP` `ip + 2` and the ModRM
`reg` and `rm` fields.
-/
theorem decodeLegacy0Opcode0B_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_0B ip context).run s =
      (X86.Instructions.OR_GPRv_GPRv_0B (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_0B
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode0B_run_of_register context a b c d e f modrm hmod)

/-- With `mod ≠ 3` in 64-bit mode, opcode 0B's form selection picks form 2, `OR_GPRv_MEMv`. -/
theorem selectLegacy0Opcode0B_run_of_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_0_Opcode_0B context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_0B, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-0B decoder with a memory ModRM runs `OR_GPRv_MEMv` from the state after the ModRM
fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode0B_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_0B ip context).run s =
      (X86.Instructions.OR_GPRv_MEMv (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_0B
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode0B_run_of_memory context a b c d e f modrm hmod)

end X86Proofs
