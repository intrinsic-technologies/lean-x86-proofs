import X86Proofs.Step.Decode

/-!
# Opcode `FF`: group 5 (`INC`/`DEC`/`CALL`/`JMP`/`PUSH r/m`)

The one place that looks inside lean-x86's opcode-`FF` decoder (`Decode_Legacy_0_Opcode_FF`) and its
form selection (`Select_Legacy_0_Opcode_FF`), architecture rule 5. Several instruction folders use
the opcode, each through the lemmas here. For each ModRM case the library uses — `reg = 0` (`INC`,
`Instructions/Inc`) and `reg = 1` (`DEC`, `Instructions/Dec`) with `mod = 3`, `reg = 2`
(`CALL r/m64`, `Instructions/Call`) with `mod = 3` and with a memory operand, and `reg = 0` and
`reg = 1` with a memory operand and no LOCK prefix (`INC m`, `DEC m`,
`Instructions/{Inc,Dec}/Generated/M`), `reg = 4` (`JMP r/m64`, `Instructions/Jmp/Generated/{R,M}`)
and `reg = 6` (`PUSH r/m64`, `Instructions/Push/Generated/{R,M}`) with `mod = 3` and with a memory
operand — a `selectLegacy0OpcodeFF_run_of_…` lemma gives the form the
selection picks, and a `decodeLegacy0OpcodeFF_run_of_…` lemma runs the decoder (from the ModRM fetch
at `ip + 1`) to the call of that form at `ip + 2`. For a new case, add the pair here (the decoder
lemma is `decode_modrm_form`).

The `…_lock` pairs are the same cases with a LOCK prefix (`lock_prefix_present = true`),
selecting the `<OP>_LOCK_…` form (the generated `…Lock` rows).

`Decode_Legacy_0`'s dispatch to this decoder is `decodeLegacy0_run_of_opcodeFF`
(`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` and `reg = 0` in 64-bit mode, opcode FF's form selection picks form 12,
`INC_GPRv_FFr0`. -/
theorem selectLegacy0OpcodeFF_run_of_inc_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_FF context true a b c d e f modrm = .ok 12 := by
  simp [Select_Legacy_0_Opcode_FF, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-FF decoder with a register ModRM and `reg = 0`. If fetching the byte after the opcode at
`ip` returns a ModRM byte with `mod = 3` and `reg = 0` and leaves state `t` (in 64-bit mode, decoder
features answered), the decoder runs `INC_GPRv_FFr0` from `t` with `Next_IP` `ip + 2` and the
ModRM `rm` field.
-/
theorem decodeLegacy0OpcodeFF_run_of_inc_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_FF ip context).run s =
      (X86.Instructions.INC_GPRv_FFr0 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_FF
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeFF_run_of_inc_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 1` in 64-bit mode, opcode FF's form selection picks form 9,
`DEC_GPRv_FFr1`. -/
theorem selectLegacy0OpcodeFF_run_of_dec_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_FF context true a b c d e f modrm = .ok 9 := by
  simp [Select_Legacy_0_Opcode_FF, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-FF decoder with a register ModRM and `reg = 1`. If fetching the byte after the opcode at
`ip` returns a ModRM byte with `mod = 3` and `reg = 1` and leaves state `t` (in 64-bit mode, decoder
features answered), the decoder runs `DEC_GPRv_FFr1` from `t` with `Next_IP` `ip + 2` and the
ModRM `rm` field.
-/
theorem decodeLegacy0OpcodeFF_run_of_dec_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_FF ip context).run s =
      (X86.Instructions.DEC_GPRv_FFr1 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_FF
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeFF_run_of_dec_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 2` in 64-bit mode, opcode FF's form selection picks form 3,
`CALL_NEAR_GPRv`. -/
theorem selectLegacy0OpcodeFF_run_of_call_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_0_Opcode_FF context true a b c d e f modrm = .ok 3 := by
  simp [Select_Legacy_0_Opcode_FF, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-FF decoder with a register ModRM and `reg = 2` runs `CALL_NEAR_GPRv` at `ip + 2`
(the address after the ModRM byte) with the ModRM `rm` field. -/
theorem decodeLegacy0OpcodeFF_run_of_call_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_FF ip context).run s =
      (X86.Instructions.CALL_NEAR_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_FF
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeFF_run_of_call_register context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3` and `reg = 2` in 64-bit mode, opcode FF's form selection picks form 4,
`CALL_NEAR_MEMv`. -/
theorem selectLegacy0OpcodeFF_run_of_call_memory (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_0_Opcode_FF context true a b c d e f modrm = .ok 4 := by
  simp [Select_Legacy_0_Opcode_FF, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-FF decoder with a memory ModRM and `reg = 2` runs `CALL_NEAR_MEMv` at `ip + 2`
with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy0OpcodeFF_run_of_call_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_FF ip context).run s =
      (X86.Instructions.CALL_NEAR_MEMv (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_FF
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeFF_run_of_call_memory context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3`, `reg = 0` and no LOCK prefix in 64-bit mode, opcode FF's form selection picks
form 13, `INC_MEMv`. -/
theorem selectLegacy0OpcodeFF_run_of_inc_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_FF context true a b c d e f modrm = .ok 13 := by
  simp [Select_Legacy_0_Opcode_FF, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-FF decoder with a memory ModRM, `reg = 0` and no LOCK prefix runs `INC_MEMv`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeFF_run_of_inc_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_FF ip context).run s =
      (X86.Instructions.INC_MEMv (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_FF
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeFF_run_of_inc_memory context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 1` and no LOCK prefix in 64-bit mode, opcode FF's form selection picks
form 10, `DEC_MEMv`. -/
theorem selectLegacy0OpcodeFF_run_of_dec_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_FF context true a b c d e f modrm = .ok 10 := by
  simp [Select_Legacy_0_Opcode_FF, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-FF decoder with a memory ModRM, `reg = 1` and no LOCK prefix runs `DEC_MEMv`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeFF_run_of_dec_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_FF ip context).run s =
      (X86.Instructions.DEC_MEMv (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_FF
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeFF_run_of_dec_memory context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod = 3` and `reg = 4` in 64-bit mode, opcode FF's form selection picks form 7,
`JMP_GPRv`. -/
theorem selectLegacy0OpcodeFF_run_of_jmp_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_0_Opcode_FF context true a b c d e f modrm = .ok 7 := by
  simp [Select_Legacy_0_Opcode_FF, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-FF decoder with a register ModRM and `reg = 4` runs `JMP_GPRv` at `ip + 2`
(the address after the ModRM byte) with the ModRM `rm` field. -/
theorem decodeLegacy0OpcodeFF_run_of_jmp_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_FF ip context).run s =
      (X86.Instructions.JMP_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_FF
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeFF_run_of_jmp_register context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3` and `reg = 4` in 64-bit mode, opcode FF's form selection picks form 8,
`JMP_MEMv`. -/
theorem selectLegacy0OpcodeFF_run_of_jmp_memory (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_0_Opcode_FF context true a b c d e f modrm = .ok 8 := by
  simp [Select_Legacy_0_Opcode_FF, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-FF decoder with a memory ModRM and `reg = 4` runs `JMP_MEMv` at `ip + 2`
with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy0OpcodeFF_run_of_jmp_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_FF ip context).run s =
      (X86.Instructions.JMP_MEMv (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_FF
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeFF_run_of_jmp_memory context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 6` in 64-bit mode, opcode FF's form selection picks form 1,
`PUSH_GPRv_FFr6`. -/
theorem selectLegacy0OpcodeFF_run_of_push_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_0_Opcode_FF context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_FF, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-FF decoder with a register ModRM and `reg = 6` runs `PUSH_GPRv_FFr6` at `ip + 2`
(the address after the ModRM byte) with the ModRM `rm` field. -/
theorem decodeLegacy0OpcodeFF_run_of_push_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_FF ip context).run s =
      (X86.Instructions.PUSH_GPRv_FFr6 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_FF
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeFF_run_of_push_register context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3` and `reg = 6` in 64-bit mode, opcode FF's form selection picks form 2,
`PUSH_MEMv`. -/
theorem selectLegacy0OpcodeFF_run_of_push_memory (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_0_Opcode_FF context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_FF, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-FF decoder with a memory ModRM and `reg = 6` runs `PUSH_MEMv` at `ip + 2`
with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy0OpcodeFF_run_of_push_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_FF ip context).run s =
      (X86.Instructions.PUSH_MEMv (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_FF
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeFF_run_of_push_memory context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3`, `reg = 0` and a LOCK prefix in 64-bit mode, opcode FF's form selection picks
form 14, `INC_LOCK_MEMv`. -/
theorem selectLegacy0OpcodeFF_run_of_inc_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_FF context true a b c d e f modrm = .ok 14 := by
  simp [Select_Legacy_0_Opcode_FF, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-FF decoder with a memory ModRM, `reg = 0` and a LOCK prefix runs `INC_LOCK_MEMv`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeFF_run_of_inc_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_FF ip context).run s =
      (X86.Instructions.INC_LOCK_MEMv (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_FF
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeFF_run_of_inc_memory_lock context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 1` and a LOCK prefix in 64-bit mode, opcode FF's form selection picks
form 11, `DEC_LOCK_MEMv`. -/
theorem selectLegacy0OpcodeFF_run_of_dec_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_FF context true a b c d e f modrm = .ok 11 := by
  simp [Select_Legacy_0_Opcode_FF, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-FF decoder with a memory ModRM, `reg = 1` and a LOCK prefix runs `DEC_LOCK_MEMv`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeFF_run_of_dec_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_FF ip context).run s =
      (X86.Instructions.DEC_LOCK_MEMv (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_FF
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeFF_run_of_dec_memory_lock context hlock a b c d e f modrm
      hmod hreg)

end X86Proofs
