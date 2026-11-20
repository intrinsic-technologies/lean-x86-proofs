import X86Proofs.Step.Decode

/-!
# Opcode `63`: `MOVSXD r, r/m32`

The one place that looks inside lean-x86's opcode-`63` decoder (`Decode_Legacy_0_Opcode_63`) and its
form selection (`Select_Legacy_0_Opcode_63`), architecture rule 5. The register form (`mod = 3`,
`MOVSXD_GPRv_GPRz`, `Instructions/Movsxd/Generated/RR32`) takes the operand size from the context;
with a memory operand REX.W chooses between `MOVSXD_GPR64_MEMd_0` (a doubleword sign-extended to 64
bits) and `MOVSXD_GPRz_MEMz` (a 32- or 16-bit copy), `Instructions/Movsxd/Generated/RM32`. For each
form, a `selectLegacy0Opcode63_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy0Opcode63_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`, `ip` the
opcode byte's address) to the call of that form at `ip + 2`.

The dispatch to this decoder is `decodeLegacy0_run_of_opcode63` (`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod ≠ 3`, `rex_w = 1` in 64-bit mode, opcode 63's form selection picks form 1,
`MOVSXD_GPR64_MEMd_0`. -/
theorem selectLegacy0Opcode63_run_of_memory64 (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hw : context.rex_w = 1) :
    Select_Legacy_0_Opcode_63 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_63, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-63 decoder with a memory ModRM (`mod ≠ 3`) and REX.W runs `MOVSXD_GPR64_MEMd_0` from
the state after the ModRM fetch, at `ip + 2`, with the ModRM `mod`, `reg` and `rm` fields. -/
theorem decodeLegacy0Opcode63_run_of_memory64 [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hw : context.rex_w = 1)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_63 ip context).run s =
      (X86.Instructions.MOVSXD_GPR64_MEMd_0 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_63
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy0Opcode63_run_of_memory64 context a b c d e f modrm hmod hw)

/-- With `mod = 3` in 64-bit mode, opcode 63's form selection picks form 2, `MOVSXD_GPRv_GPRz`. -/
theorem selectLegacy0Opcode63_run_of_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_0_Opcode_63 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_63, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-63 decoder with a register ModRM (`mod = 3`) runs `MOVSXD_GPRv_GPRz` from the state
after the ModRM fetch, at `ip + 2`, with the ModRM `reg` and `rm` fields. -/
theorem decodeLegacy0Opcode63_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_63 ip context).run s =
      (X86.Instructions.MOVSXD_GPRv_GPRz (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_63
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy0Opcode63_run_of_register context a b c d e f modrm hmod)

/-- With `mod ≠ 3`, `rex_w = 0` in 64-bit mode, opcode 63's form selection picks form 3,
`MOVSXD_GPRz_MEMz`. -/
theorem selectLegacy0Opcode63_run_of_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hw : context.rex_w = 0) :
    Select_Legacy_0_Opcode_63 context true a b c d e f modrm = .ok 3 := by
  simp [Select_Legacy_0_Opcode_63, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hw, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-63 decoder with a memory ModRM (`mod ≠ 3`) without REX.W runs `MOVSXD_GPRz_MEMz` from
the state after the ModRM fetch, at `ip + 2`, with the ModRM `mod`, `reg` and `rm` fields. -/
theorem decodeLegacy0Opcode63_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hw : context.rex_w = 0)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_63 ip context).run s =
      (X86.Instructions.MOVSXD_GPRz_MEMz (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_63
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy0Opcode63_run_of_memory context a b c d e f modrm hmod hw)

end X86Proofs
