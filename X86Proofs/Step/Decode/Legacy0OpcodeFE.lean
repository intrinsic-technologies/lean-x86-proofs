import X86Proofs.Step.Decode

/-!
# Opcode `FE`: group 4 (`INC r/m8`, `DEC r/m8`)

The one place that looks inside lean-x86's opcode-`FE` decoder (`Decode_Legacy_0_Opcode_FE`) and its
form selection (`Select_Legacy_0_Opcode_FE`), architecture rule 5. Several instruction folders use
the opcode, each through the lemmas here. For each ModRM case the library uses — `reg = 0`
(`INC r8`, `Instructions/Inc/Generated/R8`) and `reg = 1` (`DEC r8`,
`Instructions/Dec/Generated/R8`) with `mod = 3`, and both with a memory operand and no LOCK prefix
(`INC m8`, `DEC m8`, `Instructions/{Inc,Dec}/Generated/M8`) — a `selectLegacy0OpcodeFE_run_of_…`
lemma gives the form the selection picks, and a `decodeLegacy0OpcodeFE_run_of_…` lemma runs the
decoder (from the ModRM fetch at `ip + 1`) to the call of that form at `ip + 2`. For a new case, add
the pair here (the decoder lemma is `decode_modrm_form`).

The `…_lock` pairs are the same cases with a LOCK prefix (`lock_prefix_present = true`),
selecting the `<OP>_LOCK_…` form (the generated `…Lock` rows).

`Decode_Legacy_0`'s dispatch to this decoder is `decodeLegacy0_run_of_opcodeFE`
(`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` and `reg = 0` in 64-bit mode, opcode FE's form selection picks form 4,
`INC_GPR8`. -/
theorem selectLegacy0OpcodeFE_run_of_inc_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_FE context true a b c d e f modrm = .ok 4 := by
  simp [Select_Legacy_0_Opcode_FE, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-FE decoder with a register ModRM and `reg = 0`. If fetching the byte after the opcode at
`ip` returns a ModRM byte with `mod = 3` and `reg = 0` and leaves state `t` (in 64-bit mode, decoder
features answered), the decoder runs `INC_GPR8` from `t` with `Next_IP` `ip + 2` and the
ModRM `rm` field.
-/
theorem decodeLegacy0OpcodeFE_run_of_inc_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_FE ip context).run s =
      (X86.Instructions.INC_GPR8 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_FE
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeFE_run_of_inc_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 1` in 64-bit mode, opcode FE's form selection picks form 1,
`DEC_GPR8`. -/
theorem selectLegacy0OpcodeFE_run_of_dec_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_FE context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_FE, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-FE decoder with a register ModRM and `reg = 1`. If fetching the byte after the opcode at
`ip` returns a ModRM byte with `mod = 3` and `reg = 1` and leaves state `t` (in 64-bit mode, decoder
features answered), the decoder runs `DEC_GPR8` from `t` with `Next_IP` `ip + 2` and the
ModRM `rm` field.
-/
theorem decodeLegacy0OpcodeFE_run_of_dec_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_FE ip context).run s =
      (X86.Instructions.DEC_GPR8 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_FE
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeFE_run_of_dec_register context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3`, `reg = 0` and no LOCK prefix in 64-bit mode, opcode FE's form selection picks
form 5, `INC_MEMb`. -/
theorem selectLegacy0OpcodeFE_run_of_inc_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_FE context true a b c d e f modrm = .ok 5 := by
  simp [Select_Legacy_0_Opcode_FE, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-FE decoder with a memory ModRM, `reg = 0` and no LOCK prefix runs `INC_MEMb`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeFE_run_of_inc_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_FE ip context).run s =
      (X86.Instructions.INC_MEMb (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_FE
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeFE_run_of_inc_memory context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 1` and no LOCK prefix in 64-bit mode, opcode FE's form selection picks
form 2, `DEC_MEMb`. -/
theorem selectLegacy0OpcodeFE_run_of_dec_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_FE context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_FE, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-FE decoder with a memory ModRM, `reg = 1` and no LOCK prefix runs `DEC_MEMb`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeFE_run_of_dec_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_FE ip context).run s =
      (X86.Instructions.DEC_MEMb (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_FE
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeFE_run_of_dec_memory context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 0` and a LOCK prefix in 64-bit mode, opcode FE's form selection picks
form 6, `INC_LOCK_MEMb`. -/
theorem selectLegacy0OpcodeFE_run_of_inc_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_FE context true a b c d e f modrm = .ok 6 := by
  simp [Select_Legacy_0_Opcode_FE, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-FE decoder with a memory ModRM, `reg = 0` and a LOCK prefix runs `INC_LOCK_MEMb`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeFE_run_of_inc_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_FE ip context).run s =
      (X86.Instructions.INC_LOCK_MEMb (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_FE
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeFE_run_of_inc_memory_lock context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 1` and a LOCK prefix in 64-bit mode, opcode FE's form selection picks
form 3, `DEC_LOCK_MEMb`. -/
theorem selectLegacy0OpcodeFE_run_of_dec_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_FE context true a b c d e f modrm = .ok 3 := by
  simp [Select_Legacy_0_Opcode_FE, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-FE decoder with a memory ModRM, `reg = 1` and a LOCK prefix runs `DEC_LOCK_MEMb`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeFE_run_of_dec_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_FE ip context).run s =
      (X86.Instructions.DEC_LOCK_MEMb (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_FE
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeFE_run_of_dec_memory_lock context hlock a b c d e f modrm
      hmod hreg)

end X86Proofs
