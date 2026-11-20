import X86Proofs.Step.Decode

/-!
# Opcode `D1`: group 2 with count 1 (`ROL`/…/`SAR r/m, 1`)

The one place that looks inside lean-x86's opcode-`D1` decoder (`Decode_Legacy_0_Opcode_D1`) and its
form selection (`Select_Legacy_0_Opcode_D1`), architecture rule 5. Several instruction folders use
the opcode, each through the lemmas here. For each ModRM case the library uses — `mod = 3` with
`reg = 0` (`ROL`, `Instructions/Rol`), 1 (`ROR`, `Instructions/Ror`), 2 (`RCL`, `Instructions/Rcl`),
3 (`RCR`, `Instructions/Rcr`), 4 (`SHL`, `Instructions/Shl`), 5 (`SHR`, `Instructions/Shr`) and 7
(`SAR`, `Instructions/Sar`), and the same digits with a memory operand
(`Instructions/<Op>/Generated/M…`) — a `selectLegacy0OpcodeD1_run_of_…` lemma gives the form the
selection picks, and a `decodeLegacy0OpcodeD1_run_of_…` lemma runs the decoder (from the ModRM fetch
at `ip + 1`) to the call of that form at `ip + 2`. For a new case, add the pair here (the decoder
lemma is `decode_modrm_form`). `reg = 6`, an undocumented alias of `SHL`, is `Instructions/Sal`'s.

`Decode_Legacy_0`'s dispatch to this decoder is `decodeLegacy0_run_of_opcodeD1`
(`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` and `reg = 0` in 64-bit mode, opcode D1's form selection picks form 9,
`ROL_GPRv_ONE`. -/
theorem selectLegacy0OpcodeD1_run_of_rol_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_D1 context true a b c d e f modrm = .ok 9 := by
  simp [Select_Legacy_0_Opcode_D1, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-D1 decoder with a register ModRM and `reg = 0`. If fetching the byte after the opcode at
`ip` returns a ModRM byte with `mod = 3` and `reg = 0` and leaves state `t` (in 64-bit mode, decoder
features answered), the decoder runs `ROL_GPRv_ONE` from `t` with `ip + 2` (the next instruction's
address) and the ModRM `rm` field.
-/
theorem decodeLegacy0OpcodeD1_run_of_rol_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D1 ip context).run s =
      (X86.Instructions.ROL_GPRv_ONE (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_D1
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD1_run_of_rol_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 5` in 64-bit mode, opcode D1's form selection picks form 3,
`SHR_GPRv_ONE`. -/
theorem selectLegacy0OpcodeD1_run_of_shr_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_0_Opcode_D1 context true a b c d e f modrm = .ok 3 := by
  simp [Select_Legacy_0_Opcode_D1, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-D1 decoder with a register ModRM and `reg = 5`. If fetching the byte after the opcode at
`ip` returns a ModRM byte with `mod = 3` and `reg = 5` and leaves state `t` (in 64-bit mode, decoder
features answered), the decoder runs `SHR_GPRv_ONE` from `t` with `ip + 2` (the next instruction's
address) and the ModRM `rm` field.
-/
theorem decodeLegacy0OpcodeD1_run_of_shr_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D1 ip context).run s =
      (X86.Instructions.SHR_GPRv_ONE (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_D1
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD1_run_of_shr_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 1` in 64-bit mode, opcode D1's form selection picks form 11,
`ROR_GPRv_ONE`. -/
theorem selectLegacy0OpcodeD1_run_of_ror_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_D1 context true a b c d e f modrm = .ok 11 := by
  simp [Select_Legacy_0_Opcode_D1, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-D1 decoder with a register ModRM and `reg = 1`. If fetching the byte after the opcode at
`ip` returns a ModRM byte with `mod = 3` and `reg = 1` and leaves state `t` (in 64-bit mode, decoder
features answered), the decoder runs `ROR_GPRv_ONE` from `t` with `ip + 2` (the next instruction's
address) and the ModRM `rm` field.
-/
theorem decodeLegacy0OpcodeD1_run_of_ror_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D1 ip context).run s =
      (X86.Instructions.ROR_GPRv_ONE (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_D1
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD1_run_of_ror_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 2` in 64-bit mode, opcode D1's form selection picks form 13,
`RCL_GPRv_ONE`. -/
theorem selectLegacy0OpcodeD1_run_of_rcl_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_0_Opcode_D1 context true a b c d e f modrm = .ok 13 := by
  simp [Select_Legacy_0_Opcode_D1, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-D1 decoder with a register ModRM and `reg = 2`. If fetching the byte after the opcode at
`ip` returns a ModRM byte with `mod = 3` and `reg = 2` and leaves state `t` (in 64-bit mode, decoder
features answered), the decoder runs `RCL_GPRv_ONE` from `t` with `ip + 2` (the next instruction's
address) and the ModRM `rm` field.
-/
theorem decodeLegacy0OpcodeD1_run_of_rcl_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D1 ip context).run s =
      (X86.Instructions.RCL_GPRv_ONE (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_D1
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD1_run_of_rcl_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 3` in 64-bit mode, opcode D1's form selection picks form 15,
`RCR_GPRv_ONE`. -/
theorem selectLegacy0OpcodeD1_run_of_rcr_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_0_Opcode_D1 context true a b c d e f modrm = .ok 15 := by
  simp [Select_Legacy_0_Opcode_D1, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-D1 decoder with a register ModRM and `reg = 3`. If fetching the byte after the opcode at
`ip` returns a ModRM byte with `mod = 3` and `reg = 3` and leaves state `t` (in 64-bit mode, decoder
features answered), the decoder runs `RCR_GPRv_ONE` from `t` with `ip + 2` (the next instruction's
address) and the ModRM `rm` field.
-/
theorem decodeLegacy0OpcodeD1_run_of_rcr_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D1 ip context).run s =
      (X86.Instructions.RCR_GPRv_ONE (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_D1
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD1_run_of_rcr_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 4` in 64-bit mode, opcode D1's form selection picks form 1,
`SHL_GPRv_ONE_D1r4`. -/
theorem selectLegacy0OpcodeD1_run_of_shl_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_0_Opcode_D1 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_D1, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-D1 decoder with a register ModRM and `reg = 4`. If fetching the byte after the opcode at
`ip` returns a ModRM byte with `mod = 3` and `reg = 4` and leaves state `t` (in 64-bit mode, decoder
features answered), the decoder runs `SHL_GPRv_ONE_D1r4` from `t` with `ip + 2` (the next instruction's
address) and the ModRM `rm` field.
-/
theorem decodeLegacy0OpcodeD1_run_of_shl_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D1 ip context).run s =
      (X86.Instructions.SHL_GPRv_ONE_D1r4 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_D1
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD1_run_of_shl_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 7` in 64-bit mode, opcode D1's form selection picks form 7,
`SAR_GPRv_ONE`. -/
theorem selectLegacy0OpcodeD1_run_of_sar_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_0_Opcode_D1 context true a b c d e f modrm = .ok 7 := by
  simp [Select_Legacy_0_Opcode_D1, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-D1 decoder with a register ModRM and `reg = 7`. If fetching the byte after the opcode at
`ip` returns a ModRM byte with `mod = 3` and `reg = 7` and leaves state `t` (in 64-bit mode, decoder
features answered), the decoder runs `SAR_GPRv_ONE` from `t` with `ip + 2` (the next instruction's
address) and the ModRM `rm` field.
-/
theorem decodeLegacy0OpcodeD1_run_of_sar_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D1 ip context).run s =
      (X86.Instructions.SAR_GPRv_ONE (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_D1
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD1_run_of_sar_register context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3`, `reg = 0` in 64-bit mode, opcode D1's form selection picks
form 10, `ROL_MEMv_ONE`. -/
theorem selectLegacy0OpcodeD1_run_of_rol_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_D1 context true a b c d e f modrm = .ok 10 := by
  simp [Select_Legacy_0_Opcode_D1, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D1 decoder with a memory ModRM, `reg = 0` runs `ROL_MEMv_ONE`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeD1_run_of_rol_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D1 ip context).run s =
      (X86.Instructions.ROL_MEMv_ONE (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_D1
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD1_run_of_rol_memory context a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 1` in 64-bit mode, opcode D1's form selection picks
form 12, `ROR_MEMv_ONE`. -/
theorem selectLegacy0OpcodeD1_run_of_ror_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_D1 context true a b c d e f modrm = .ok 12 := by
  simp [Select_Legacy_0_Opcode_D1, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D1 decoder with a memory ModRM, `reg = 1` runs `ROR_MEMv_ONE`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeD1_run_of_ror_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D1 ip context).run s =
      (X86.Instructions.ROR_MEMv_ONE (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_D1
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD1_run_of_ror_memory context a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 2` in 64-bit mode, opcode D1's form selection picks
form 14, `RCL_MEMv_ONE`. -/
theorem selectLegacy0OpcodeD1_run_of_rcl_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_0_Opcode_D1 context true a b c d e f modrm = .ok 14 := by
  simp [Select_Legacy_0_Opcode_D1, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D1 decoder with a memory ModRM, `reg = 2` runs `RCL_MEMv_ONE`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeD1_run_of_rcl_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D1 ip context).run s =
      (X86.Instructions.RCL_MEMv_ONE (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_D1
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD1_run_of_rcl_memory context a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 3` in 64-bit mode, opcode D1's form selection picks
form 16, `RCR_MEMv_ONE`. -/
theorem selectLegacy0OpcodeD1_run_of_rcr_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_0_Opcode_D1 context true a b c d e f modrm = .ok 16 := by
  simp [Select_Legacy_0_Opcode_D1, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D1 decoder with a memory ModRM, `reg = 3` runs `RCR_MEMv_ONE`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeD1_run_of_rcr_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D1 ip context).run s =
      (X86.Instructions.RCR_MEMv_ONE (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_D1
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD1_run_of_rcr_memory context a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 4` in 64-bit mode, opcode D1's form selection picks
form 2, `SHL_MEMv_ONE_D1r4`. -/
theorem selectLegacy0OpcodeD1_run_of_shl_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_0_Opcode_D1 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_D1, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D1 decoder with a memory ModRM, `reg = 4` runs `SHL_MEMv_ONE_D1r4`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeD1_run_of_shl_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D1 ip context).run s =
      (X86.Instructions.SHL_MEMv_ONE_D1r4 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_D1
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD1_run_of_shl_memory context a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 5` in 64-bit mode, opcode D1's form selection picks
form 4, `SHR_MEMv_ONE`. -/
theorem selectLegacy0OpcodeD1_run_of_shr_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_0_Opcode_D1 context true a b c d e f modrm = .ok 4 := by
  simp [Select_Legacy_0_Opcode_D1, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D1 decoder with a memory ModRM, `reg = 5` runs `SHR_MEMv_ONE`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeD1_run_of_shr_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D1 ip context).run s =
      (X86.Instructions.SHR_MEMv_ONE (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_D1
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD1_run_of_shr_memory context a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 7` in 64-bit mode, opcode D1's form selection picks
form 8, `SAR_MEMv_ONE`. -/
theorem selectLegacy0OpcodeD1_run_of_sar_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_0_Opcode_D1 context true a b c d e f modrm = .ok 8 := by
  simp [Select_Legacy_0_Opcode_D1, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D1 decoder with a memory ModRM, `reg = 7` runs `SAR_MEMv_ONE`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeD1_run_of_sar_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D1 ip context).run s =
      (X86.Instructions.SAR_MEMv_ONE (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_D1
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD1_run_of_sar_memory context a b c d e f modrm
      hmod hreg)

/-- With `mod = 3` and `reg = 6` in 64-bit mode, opcode D1's form selection picks form 5, SHL /6
(`SHL_GPR…_D1r6`, an undocumented alias of SHL /4). -/
theorem selectLegacy0OpcodeD1_run_of_sal_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_0_Opcode_D1 context true a b c d e f modrm = .ok 5 := by
  simp [Select_Legacy_0_Opcode_D1, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/-- The opcode-D1 decoder with a register ModRM and `reg = 6` runs SHL /6's form from the state
after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeD1_run_of_sal_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D1 ip context).run s =
      (X86.Instructions.SHL_GPRv_ONE_D1r6 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_D1
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD1_run_of_sal_register context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3` and `reg = 6` in 64-bit mode, opcode D1's form selection picks form 6, SHL /6
(`SHL_MEM…_D1r6`, an undocumented alias of SHL /4). -/
theorem selectLegacy0OpcodeD1_run_of_sal_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_0_Opcode_D1 context true a b c d e f modrm = .ok 6 := by
  simp [Select_Legacy_0_Opcode_D1, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D1 decoder with a memory ModRM and `reg = 6` runs SHL /6's form from the state
after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeD1_run_of_sal_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D1 ip context).run s =
      (X86.Instructions.SHL_MEMv_ONE_D1r6 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_D1
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD1_run_of_sal_memory context a b c d e f modrm
      hmod hreg)

end X86Proofs
