import X86Proofs.Step.Decode

/-!
# Opcode `0F B1`: `CMPXCHG r/m, r`

The one place that looks inside lean-x86's opcode-`B1` decoder (`Decode_Legacy_1_Opcode_B1`) and its
form selection (`Select_Legacy_1_Opcode_B1`), architecture rule 5. The selection depends on `mod`
and the LOCK prefix: the register form (`mod = 3`, `CMPXCHG_GPRv_GPRv`,
`Instructions/Cmpxchg/Generated/RR`), the memory form without LOCK (`CMPXCHG_MEMv_GPRv`, `MR`) and
the locked memory form (`CMPXCHG_LOCK_MEMv_GPRv`, `…_lock` below). For each form, a
`selectLegacy1OpcodeB1_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy1OpcodeB1_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`, `ip` the
second opcode byte's address) to the call of that form at `ip + 2`.

The `…_lock` pairs are the same cases with a LOCK prefix (`lock_prefix_present = true`),
selecting the `<OP>_LOCK_…` form (the generated `…Lock` rows).

The dispatch to this decoder is `decodeLegacy1_run_of_opcodeB1` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` in 64-bit mode, opcode B1's form selection picks form 1, `CMPXCHG_GPRv_GPRv`. -/
theorem selectLegacy1OpcodeB1_run_of_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_B1 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_B1, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-B1 decoder with a register ModRM (`mod = 3`) runs `CMPXCHG_GPRv_GPRv` from the state
after the ModRM fetch, at `ip + 2`, with the ModRM `reg` and `rm` fields. -/
theorem decodeLegacy1OpcodeB1_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_B1 ip context).run s =
      (X86.Instructions.CMPXCHG_GPRv_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_B1
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1OpcodeB1_run_of_register context a b c d e f modrm hmod)

/-- With `mod ≠ 3`, `lock_prefix_present = false` in 64-bit mode, opcode B1's form selection picks
form 2, `CMPXCHG_MEMv_GPRv`. -/
theorem selectLegacy1OpcodeB1_run_of_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hlock : context.lock_prefix_present = false) :
    Select_Legacy_1_Opcode_B1 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_B1, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-B1 decoder with a memory ModRM (`mod ≠ 3`) and no LOCK prefix runs
`CMPXCHG_MEMv_GPRv` from the state after the ModRM fetch, at `ip + 2`, with the ModRM `mod`, `reg`
and `rm` fields. -/
theorem decodeLegacy1OpcodeB1_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_B1 ip context).run s =
      (X86.Instructions.CMPXCHG_MEMv_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_B1
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1OpcodeB1_run_of_memory context a b c d e f modrm hmod hlock)

/-- With `mod ≠ 3`, `lock_prefix_present = true` in 64-bit mode, opcode B1's form selection picks
form 3, `CMPXCHG_LOCK_MEMv_GPRv`. -/
theorem selectLegacy1OpcodeB1_run_of_memory_lock (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hlock : context.lock_prefix_present = true) :
    Select_Legacy_1_Opcode_B1 context true a b c d e f modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_B1, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-B1 decoder with a memory ModRM (`mod ≠ 3`) and a LOCK prefix runs
`CMPXCHG_LOCK_MEMv_GPRv` from the state after the ModRM fetch, at `ip + 2`, with the ModRM `mod`,
`reg`
and `rm` fields. -/
theorem decodeLegacy1OpcodeB1_run_of_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_B1 ip context).run s =
      (X86.Instructions.CMPXCHG_LOCK_MEMv_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_B1
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1OpcodeB1_run_of_memory_lock context a b c d e f modrm hmod hlock)

end X86Proofs
