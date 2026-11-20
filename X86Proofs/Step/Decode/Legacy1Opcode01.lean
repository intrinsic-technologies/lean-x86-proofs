import X86Proofs.Step.Decode

/-!
# Opcode `0F 01`: group 7 (`SMSW`, `SGDT`, …)

The one place that looks inside lean-x86's opcode-`0F 01` decoder (`Decode_Legacy_1_Opcode_01`) and
its form selection (`Select_Legacy_1_Opcode_01`), architecture rule 5. For each ModRM case the
library uses (`reg = 4`, SMSW, with `mod = 3` and with a memory operand;
`Instructions/Smsw/Generated`), a `selectLegacy1Opcode01_run_of_…` lemma gives the form the
selection picks, and a `decodeLegacy1Opcode01_run_of_…` lemma runs the decoder (from the ModRM fetch
at `ip + 1`, `ip` the second opcode byte's address) to the call of that form at `ip + 2`. The other
forms of the group are privileged (#GP at CPL 3) or descriptor-table probes, not covered.

`Decode_Legacy_1`'s dispatch to this decoder is `decodeLegacy1_run_of_opcode01`
(`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` and `reg = 4` in 64-bit mode, opcode `0F 01`'s form selection picks form 8,
`SMSW_GPRv`. -/
theorem selectLegacy1Opcode01_run_of_smsw_register (context : Instruction_Context)
    (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_1_Opcode_01 context true a b c d e f modrm = .ok 8 := by
  simp [Select_Legacy_1_Opcode_01, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`0F 01` decoder with `mod = 3` and `reg = 4` runs `SMSW_GPRv` from the state `t`
after the ModRM fetch (in 64-bit mode, decoder features answered), with `Next_IP` `ip + 2` and the
ModRM `rm` field. -/
theorem decodeLegacy1Opcode01_run_of_smsw_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_01 ip context).run s =
      (X86.Instructions.SMSW_GPRv (BitVec.add ip 2#64) context (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_01
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1Opcode01_run_of_smsw_register context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3` and `reg = 4` in 64-bit mode, opcode `0F 01`'s form selection picks form 9,
`SMSW_MEMw`. -/
theorem selectLegacy1Opcode01_run_of_smsw_memory (context : Instruction_Context)
    (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_1_Opcode_01 context true a b c d e f modrm = .ok 9 := by
  simp [Select_Legacy_1_Opcode_01, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`0F 01` decoder with `mod ≠ 3` and `reg = 4` runs `SMSW_MEMw` from the state `t`
after the ModRM fetch (in 64-bit mode, decoder features answered), at `ip + 2` (the address after
the ModRM byte) with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy1Opcode01_run_of_smsw_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_01 ip context).run s =
      (X86.Instructions.SMSW_MEMw (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_01
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1Opcode01_run_of_smsw_memory context a b c d e f modrm hmod hreg)

end X86Proofs
