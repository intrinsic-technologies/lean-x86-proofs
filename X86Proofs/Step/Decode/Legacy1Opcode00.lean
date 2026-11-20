import X86Proofs.Step.Decode

/-!
# Opcode `0F 00`: group 6 (`SLDT`, `STR`, …)

The one place that looks inside lean-x86's opcode-`0F 00` decoder (`Decode_Legacy_1_Opcode_00`) and
its form selection (`Select_Legacy_1_Opcode_00`), architecture rule 5. For each ModRM case the
library uses (`reg = 0`, SLDT, and `reg = 1`, STR, each with `mod = 3` and with a memory operand;
`Instructions/{Sldt,Str}/Generated`), a `selectLegacy1Opcode00_run_of_…` lemma gives the form the
selection picks, and a `decodeLegacy1Opcode00_run_of_…` lemma runs the decoder (from the ModRM fetch
at `ip + 1`, `ip` the second opcode byte's address) to the call of that form at `ip + 2`. The other
forms of the group are privileged (#GP at CPL 3) or descriptor-table probes, not covered.

`Decode_Legacy_1`'s dispatch to this decoder is `decodeLegacy1_run_of_opcode00`
(`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` and `reg = 0` in 64-bit mode, opcode `0F 00`'s form selection picks form 7,
`SLDT_GPRv`. -/
theorem selectLegacy1Opcode00_run_of_sldt_register (context : Instruction_Context)
    (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_1_Opcode_00 context true a b c d e f modrm = .ok 7 := by
  simp [Select_Legacy_1_Opcode_00, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`0F 00` decoder with `mod = 3` and `reg = 0` runs `SLDT_GPRv` from the state `t`
after the ModRM fetch (in 64-bit mode, decoder features answered), with `Next_IP` `ip + 2` and the
ModRM `rm` field. -/
theorem decodeLegacy1Opcode00_run_of_sldt_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_00 ip context).run s =
      (X86.Instructions.SLDT_GPRv (BitVec.add ip 2#64) context (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_00
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1Opcode00_run_of_sldt_register context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3` and `reg = 0` in 64-bit mode, opcode `0F 00`'s form selection picks form 8,
`SLDT_MEMw`. -/
theorem selectLegacy1Opcode00_run_of_sldt_memory (context : Instruction_Context)
    (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_1_Opcode_00 context true a b c d e f modrm = .ok 8 := by
  simp [Select_Legacy_1_Opcode_00, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`0F 00` decoder with `mod ≠ 3` and `reg = 0` runs `SLDT_MEMw` from the state `t`
after the ModRM fetch (in 64-bit mode, decoder features answered), at `ip + 2` (the address after
the ModRM byte) with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy1Opcode00_run_of_sldt_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_00 ip context).run s =
      (X86.Instructions.SLDT_MEMw (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_00
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1Opcode00_run_of_sldt_memory context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 1` in 64-bit mode, opcode `0F 00`'s form selection picks form 9,
`STR_GPRv`. -/
theorem selectLegacy1Opcode00_run_of_str_register (context : Instruction_Context)
    (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_1_Opcode_00 context true a b c d e f modrm = .ok 9 := by
  simp [Select_Legacy_1_Opcode_00, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`0F 00` decoder with `mod = 3` and `reg = 1` runs `STR_GPRv` from the state `t` after
the ModRM fetch (in 64-bit mode, decoder features answered), with `Next_IP` `ip + 2` and the ModRM
`rm` field. -/
theorem decodeLegacy1Opcode00_run_of_str_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_00 ip context).run s =
      (X86.Instructions.STR_GPRv (BitVec.add ip 2#64) context (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_00
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1Opcode00_run_of_str_register context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3` and `reg = 1` in 64-bit mode, opcode `0F 00`'s form selection picks form 10,
`STR_MEMw`. -/
theorem selectLegacy1Opcode00_run_of_str_memory (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_1_Opcode_00 context true a b c d e f modrm = .ok 10 := by
  simp [Select_Legacy_1_Opcode_00, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`0F 00` decoder with `mod ≠ 3` and `reg = 1` runs `STR_MEMw` from the state `t` after
the ModRM fetch (in 64-bit mode, decoder features answered), at `ip + 2` (the address after the
ModRM byte) with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy1Opcode00_run_of_str_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_00 ip context).run s =
      (X86.Instructions.STR_MEMw (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_00
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1Opcode00_run_of_str_memory context a b c d e f modrm hmod hreg)

end X86Proofs
