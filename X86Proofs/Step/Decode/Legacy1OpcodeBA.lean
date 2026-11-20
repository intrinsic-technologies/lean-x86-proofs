import X86Proofs.Step.Decode

/-!
# Opcode `0F BA`: group 8, `BT`/`BTS`/`BTR`/`BTC r/m, imm8`

The one place that looks inside lean-x86's opcode-`BA` decoder (`Decode_Legacy_1_Opcode_BA`) and its
form selection (`Select_Legacy_1_Opcode_BA`), architecture rule 5. Group 8: the ModRM `reg` digit
picks BT (`/4`), BTS (`/5`), BTR (`/6`) or BTC (`/7`) with an immediate bit offset, for a register
(`mod = 3`, `<OP>_GPRv_IMMb`, `Instructions/<Op>/Generated/Imm8`) or a memory bit base
(`<OP>_MEMv_IMMb`, `MImm8`; BTS, BTR and BTC without a LOCK prefix, whose LOCK forms are separate).
The forms fetch the immediate themselves. For each, a `selectLegacy1OpcodeBA_run_of_…` lemma gives
the form the selection picks, and a `decodeLegacy1OpcodeBA_run_of_…` lemma runs the decoder (from
the ModRM fetch at `ip + 1`, `ip` the second opcode byte's address) to the call of that form at
`ip + 2`.

The `…_lock` pairs are the same cases with a LOCK prefix (`lock_prefix_present = true`),
selecting the `<OP>_LOCK_…` form (the generated `…Lock` rows).

The dispatch to this decoder is `decodeLegacy1_run_of_opcodeBA` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3`, `reg = 4` in 64-bit mode, opcode BA's form selection picks form 10,
`BT_GPRv_IMMb`. -/
theorem selectLegacy1OpcodeBA_run_of_r4_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_1_Opcode_BA context true a b c d e f modrm = .ok 10 := by
  simp [Select_Legacy_1_Opcode_BA, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-BA decoder with a register ModRM (`mod = 3`, `reg = 4`) runs `BT_GPRv_IMMb` from the
state after the ModRM fetch, at `ip + 2`, with the ModRM `rm` field. -/
theorem decodeLegacy1OpcodeBA_run_of_r4_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BA ip context).run s =
      (X86.Instructions.BT_GPRv_IMMb (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BA
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeBA_run_of_r4_register context a b c d e f modrm hmod
      hreg)

/-- With `mod ≠ 3`, `reg = 4` in 64-bit mode, opcode BA's form selection picks form 11,
`BT_MEMv_IMMb`. -/
theorem selectLegacy1OpcodeBA_run_of_r4_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_1_Opcode_BA context true a b c d e f modrm = .ok 11 := by
  simp [Select_Legacy_1_Opcode_BA, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-BA decoder with a memory ModRM (`mod ≠ 3`, `reg = 4`) runs `BT_MEMv_IMMb` from the
state after the ModRM fetch, at `ip + 2`, with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy1OpcodeBA_run_of_r4_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BA ip context).run s =
      (X86.Instructions.BT_MEMv_IMMb (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BA
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeBA_run_of_r4_memory context a b c d e f modrm hmod hreg)

/-- With `mod = 3`, `reg = 5` in 64-bit mode, opcode BA's form selection picks form 1,
`BTS_GPRv_IMMb`. -/
theorem selectLegacy1OpcodeBA_run_of_r5_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_1_Opcode_BA context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_BA, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-BA decoder with a register ModRM (`mod = 3`, `reg = 5`) runs `BTS_GPRv_IMMb` from the
state after the ModRM fetch, at `ip + 2`, with the ModRM `rm` field. -/
theorem decodeLegacy1OpcodeBA_run_of_r5_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BA ip context).run s =
      (X86.Instructions.BTS_GPRv_IMMb (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BA
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeBA_run_of_r5_register context a b c d e f modrm hmod
      hreg)

/-- With `mod ≠ 3`, `reg = 5`, no LOCK prefix in 64-bit mode, opcode BA's form selection picks form
2, `BTS_MEMv_IMMb`. -/
theorem selectLegacy1OpcodeBA_run_of_r5_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_1_Opcode_BA context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_BA, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-BA decoder with a memory ModRM (`mod ≠ 3`, `reg = 5`, no LOCK prefix) runs
`BTS_MEMv_IMMb` from the state after the ModRM fetch, at `ip + 2`, with the ModRM `mod` and `rm`
fields. -/
theorem decodeLegacy1OpcodeBA_run_of_r5_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3)
    (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BA ip context).run s =
      (X86.Instructions.BTS_MEMv_IMMb (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BA
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeBA_run_of_r5_memory context hlock a b c d e f modrm hmod
      hreg)

/-- With `mod = 3`, `reg = 6` in 64-bit mode, opcode BA's form selection picks form 4,
`BTR_GPRv_IMMb`. -/
theorem selectLegacy1OpcodeBA_run_of_r6_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_1_Opcode_BA context true a b c d e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_BA, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-BA decoder with a register ModRM (`mod = 3`, `reg = 6`) runs `BTR_GPRv_IMMb` from the
state after the ModRM fetch, at `ip + 2`, with the ModRM `rm` field. -/
theorem decodeLegacy1OpcodeBA_run_of_r6_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BA ip context).run s =
      (X86.Instructions.BTR_GPRv_IMMb (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BA
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeBA_run_of_r6_register context a b c d e f modrm hmod
      hreg)

/-- With `mod ≠ 3`, `reg = 6`, no LOCK prefix in 64-bit mode, opcode BA's form selection picks form
5, `BTR_MEMv_IMMb`. -/
theorem selectLegacy1OpcodeBA_run_of_r6_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_1_Opcode_BA context true a b c d e f modrm = .ok 5 := by
  simp [Select_Legacy_1_Opcode_BA, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-BA decoder with a memory ModRM (`mod ≠ 3`, `reg = 6`, no LOCK prefix) runs
`BTR_MEMv_IMMb` from the state after the ModRM fetch, at `ip + 2`, with the ModRM `mod` and `rm`
fields. -/
theorem decodeLegacy1OpcodeBA_run_of_r6_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3)
    (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BA ip context).run s =
      (X86.Instructions.BTR_MEMv_IMMb (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BA
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeBA_run_of_r6_memory context hlock a b c d e f modrm hmod
      hreg)

/-- With `mod = 3`, `reg = 7` in 64-bit mode, opcode BA's form selection picks form 7,
`BTC_GPRv_IMMb`. -/
theorem selectLegacy1OpcodeBA_run_of_r7_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_1_Opcode_BA context true a b c d e f modrm = .ok 7 := by
  simp [Select_Legacy_1_Opcode_BA, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-BA decoder with a register ModRM (`mod = 3`, `reg = 7`) runs `BTC_GPRv_IMMb` from the
state after the ModRM fetch, at `ip + 2`, with the ModRM `rm` field. -/
theorem decodeLegacy1OpcodeBA_run_of_r7_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BA ip context).run s =
      (X86.Instructions.BTC_GPRv_IMMb (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BA
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeBA_run_of_r7_register context a b c d e f modrm hmod
      hreg)

/-- With `mod ≠ 3`, `reg = 7`, no LOCK prefix in 64-bit mode, opcode BA's form selection picks form
8, `BTC_MEMv_IMMb`. -/
theorem selectLegacy1OpcodeBA_run_of_r7_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_1_Opcode_BA context true a b c d e f modrm = .ok 8 := by
  simp [Select_Legacy_1_Opcode_BA, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-BA decoder with a memory ModRM (`mod ≠ 3`, `reg = 7`, no LOCK prefix) runs
`BTC_MEMv_IMMb` from the state after the ModRM fetch, at `ip + 2`, with the ModRM `mod` and `rm`
fields. -/
theorem decodeLegacy1OpcodeBA_run_of_r7_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3)
    (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BA ip context).run s =
      (X86.Instructions.BTC_MEMv_IMMb (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BA
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeBA_run_of_r7_memory context hlock a b c d e f modrm hmod
      hreg)

/-- With `mod ≠ 3`, `reg = 5`, a LOCK prefix in 64-bit mode, opcode BA's form selection picks form
2, `BTS_LOCK_MEMv_IMMb`. -/
theorem selectLegacy1OpcodeBA_run_of_r5_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_1_Opcode_BA context true a b c d e f modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_BA, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-BA decoder with a memory ModRM (`mod ≠ 3`, `reg = 5`, a LOCK prefix) runs
`BTS_LOCK_MEMv_IMMb` from the state after the ModRM fetch, at `ip + 2`, with the ModRM `mod` and
`rm`
fields. -/
theorem decodeLegacy1OpcodeBA_run_of_r5_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3)
    (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BA ip context).run s =
      (X86.Instructions.BTS_LOCK_MEMv_IMMb (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BA
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeBA_run_of_r5_memory_lock context hlock a b c d e f modrm
      hmod
      hreg)

/-- With `mod ≠ 3`, `reg = 6`, a LOCK prefix in 64-bit mode, opcode BA's form selection picks form
5, `BTR_LOCK_MEMv_IMMb`. -/
theorem selectLegacy1OpcodeBA_run_of_r6_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_1_Opcode_BA context true a b c d e f modrm = .ok 6 := by
  simp [Select_Legacy_1_Opcode_BA, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-BA decoder with a memory ModRM (`mod ≠ 3`, `reg = 6`, a LOCK prefix) runs
`BTR_LOCK_MEMv_IMMb` from the state after the ModRM fetch, at `ip + 2`, with the ModRM `mod` and
`rm`
fields. -/
theorem decodeLegacy1OpcodeBA_run_of_r6_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3)
    (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BA ip context).run s =
      (X86.Instructions.BTR_LOCK_MEMv_IMMb (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BA
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeBA_run_of_r6_memory_lock context hlock a b c d e f modrm
      hmod
      hreg)

/-- With `mod ≠ 3`, `reg = 7`, a LOCK prefix in 64-bit mode, opcode BA's form selection picks form
8, `BTC_LOCK_MEMv_IMMb`. -/
theorem selectLegacy1OpcodeBA_run_of_r7_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_1_Opcode_BA context true a b c d e f modrm = .ok 9 := by
  simp [Select_Legacy_1_Opcode_BA, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-BA decoder with a memory ModRM (`mod ≠ 3`, `reg = 7`, a LOCK prefix) runs
`BTC_LOCK_MEMv_IMMb` from the state after the ModRM fetch, at `ip + 2`, with the ModRM `mod` and
`rm`
fields. -/
theorem decodeLegacy1OpcodeBA_run_of_r7_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3)
    (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BA ip context).run s =
      (X86.Instructions.BTC_LOCK_MEMv_IMMb (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BA
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeBA_run_of_r7_memory_lock context hlock a b c d e f modrm
      hmod
      hreg)

end X86Proofs
