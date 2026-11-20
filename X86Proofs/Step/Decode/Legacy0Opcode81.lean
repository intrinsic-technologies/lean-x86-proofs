import X86Proofs.Step.Decode

/-!
# Opcode `81`: group 1 with a full-size immediate (`… r/m, imm16/imm32`)

The one place that looks inside lean-x86's opcode-`81` decoder (`Decode_Legacy_0_Opcode_81`) and its
form selection (`Select_Legacy_0_Opcode_81`), architecture rule 5. Several instruction folders use
the opcode, each through the lemmas here. For each ModRM `reg` digit with `mod = 3` (`ADD`, `OR`,
`ADC`, `SBB`, `AND`, `SUB`, `XOR`, `CMP` of a register; `Instructions/<Op>/Generated/Imm32`), and
for each digit with a memory operand and no LOCK prefix (`Instructions/<Op>/Generated/MImm32`) — a
`selectLegacy0Opcode81_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy0Opcode81_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`) to the
call of that form at `ip + 2` (the form fetches the immediate itself). For a new case, add the pair
here (the decoder lemma is `decode_modrm_form`).

The `…_lock` pairs are the same cases with a LOCK prefix (`lock_prefix_present = true`),
selecting the `<OP>_LOCK_…` form (the generated `…Lock` rows).

`Decode_Legacy_0`'s dispatch to this decoder is `decodeLegacy0_run_of_opcode81`
(`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` and `reg = 0` in 64-bit mode, opcode 81's form selection picks form
1, `ADD_GPRv_IMMz`. -/
theorem selectLegacy0Opcode81_run_of_r0_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-81 decoder with a register ModRM and `reg = 0`. If fetching the byte after
the opcode at `ip` returns a ModRM byte with `mod = 3`, `reg = 0` and leaves state `t` (in
64-bit mode, decoder features answered), the decoder runs `ADD_GPRv_IMMz` from `t` with `ip + 2`
(the address of the immediate) and the ModRM `rm` field.
-/
theorem decodeLegacy0Opcode81_run_of_r0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.ADD_GPRv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r0_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 1` in 64-bit mode, opcode 81's form selection picks form
21, `OR_GPRv_IMMz`. -/
theorem selectLegacy0Opcode81_run_of_r1_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 21 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-81 decoder with a register ModRM and `reg = 1`. If fetching the byte after
the opcode at `ip` returns a ModRM byte with `mod = 3`, `reg = 1` and leaves state `t` (in
64-bit mode, decoder features answered), the decoder runs `OR_GPRv_IMMz` from `t` with `ip + 2`
(the address of the immediate) and the ModRM `rm` field.
-/
theorem decodeLegacy0Opcode81_run_of_r1_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.OR_GPRv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r1_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 2` in 64-bit mode, opcode 81's form selection picks form
4, `ADC_GPRv_IMMz`. -/
theorem selectLegacy0Opcode81_run_of_r2_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 4 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-81 decoder with a register ModRM and `reg = 2`. If fetching the byte after
the opcode at `ip` returns a ModRM byte with `mod = 3`, `reg = 2` and leaves state `t` (in
64-bit mode, decoder features answered), the decoder runs `ADC_GPRv_IMMz` from `t` with `ip + 2`
(the address of the immediate) and the ModRM `rm` field.
-/
theorem decodeLegacy0Opcode81_run_of_r2_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.ADC_GPRv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r2_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 3` in 64-bit mode, opcode 81's form selection picks form
7, `SBB_GPRv_IMMz`. -/
theorem selectLegacy0Opcode81_run_of_r3_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 7 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-81 decoder with a register ModRM and `reg = 3`. If fetching the byte after
the opcode at `ip` returns a ModRM byte with `mod = 3`, `reg = 3` and leaves state `t` (in
64-bit mode, decoder features answered), the decoder runs `SBB_GPRv_IMMz` from `t` with `ip + 2`
(the address of the immediate) and the ModRM `rm` field.
-/
theorem decodeLegacy0Opcode81_run_of_r3_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.SBB_GPRv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r3_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 4` in 64-bit mode, opcode 81's form selection picks form
18, `AND_GPRv_IMMz`. -/
theorem selectLegacy0Opcode81_run_of_r4_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 18 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-81 decoder with a register ModRM and `reg = 4`. If fetching the byte after
the opcode at `ip` returns a ModRM byte with `mod = 3`, `reg = 4` and leaves state `t` (in
64-bit mode, decoder features answered), the decoder runs `AND_GPRv_IMMz` from `t` with `ip + 2`
(the address of the immediate) and the ModRM `rm` field.
-/
theorem decodeLegacy0Opcode81_run_of_r4_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.AND_GPRv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r4_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 5` in 64-bit mode, opcode 81's form selection picks form
13, `SUB_GPRv_IMMz`. -/
theorem selectLegacy0Opcode81_run_of_r5_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 13 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-81 decoder with a register ModRM and `reg = 5`. If fetching the byte after
the opcode at `ip` returns a ModRM byte with `mod = 3`, `reg = 5` and leaves state `t` (in
64-bit mode, decoder features answered), the decoder runs `SUB_GPRv_IMMz` from `t` with `ip + 2`
(the address of the immediate) and the ModRM `rm` field.
-/
theorem decodeLegacy0Opcode81_run_of_r5_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.SUB_GPRv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r5_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 6` in 64-bit mode, opcode 81's form selection picks form
10, `XOR_GPRv_IMMz`. -/
theorem selectLegacy0Opcode81_run_of_r6_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 10 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-81 decoder with a register ModRM and `reg = 6`. If fetching the byte after
the opcode at `ip` returns a ModRM byte with `mod = 3`, `reg = 6` and leaves state `t` (in
64-bit mode, decoder features answered), the decoder runs `XOR_GPRv_IMMz` from `t` with `ip + 2`
(the address of the immediate) and the ModRM `rm` field.
-/
theorem decodeLegacy0Opcode81_run_of_r6_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.XOR_GPRv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r6_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 7` in 64-bit mode, opcode 81's form selection picks form
16, `CMP_GPRv_IMMz`. -/
theorem selectLegacy0Opcode81_run_of_r7_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 16 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-81 decoder with a register ModRM and `reg = 7`. If fetching the byte after
the opcode at `ip` returns a ModRM byte with `mod = 3`, `reg = 7` and leaves state `t` (in
64-bit mode, decoder features answered), the decoder runs `CMP_GPRv_IMMz` from `t` with `ip + 2`
(the address of the immediate) and the ModRM `rm` field.
-/
theorem decodeLegacy0Opcode81_run_of_r7_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.CMP_GPRv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r7_register context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3`, `reg = 0` and no LOCK prefix in 64-bit mode, opcode 81's form selection picks
form 2, `ADD_MEMv_IMMz`. -/
theorem selectLegacy0Opcode81_run_of_r0_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-81 decoder with a memory ModRM, `reg = 0` and no LOCK prefix runs `ADD_MEMv_IMMz`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode81_run_of_r0_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.ADD_MEMv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r0_memory context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 1` and no LOCK prefix in 64-bit mode, opcode 81's form selection picks
form 22, `OR_MEMv_IMMz`. -/
theorem selectLegacy0Opcode81_run_of_r1_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 22 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-81 decoder with a memory ModRM, `reg = 1` and no LOCK prefix runs `OR_MEMv_IMMz` from
the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode81_run_of_r1_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.OR_MEMv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r1_memory context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 2` and no LOCK prefix in 64-bit mode, opcode 81's form selection picks
form 5, `ADC_MEMv_IMMz`. -/
theorem selectLegacy0Opcode81_run_of_r2_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 5 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-81 decoder with a memory ModRM, `reg = 2` and no LOCK prefix runs `ADC_MEMv_IMMz`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode81_run_of_r2_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.ADC_MEMv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r2_memory context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 3` and no LOCK prefix in 64-bit mode, opcode 81's form selection picks
form 8, `SBB_MEMv_IMMz`. -/
theorem selectLegacy0Opcode81_run_of_r3_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 8 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-81 decoder with a memory ModRM, `reg = 3` and no LOCK prefix runs `SBB_MEMv_IMMz`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode81_run_of_r3_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3) (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.SBB_MEMv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r3_memory context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 4` and no LOCK prefix in 64-bit mode, opcode 81's form selection picks
form 19, `AND_MEMv_IMMz`. -/
theorem selectLegacy0Opcode81_run_of_r4_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 19 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-81 decoder with a memory ModRM, `reg = 4` and no LOCK prefix runs `AND_MEMv_IMMz`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode81_run_of_r4_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.AND_MEMv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r4_memory context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 5` and no LOCK prefix in 64-bit mode, opcode 81's form selection picks
form 14, `SUB_MEMv_IMMz`. -/
theorem selectLegacy0Opcode81_run_of_r5_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 14 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-81 decoder with a memory ModRM, `reg = 5` and no LOCK prefix runs `SUB_MEMv_IMMz`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode81_run_of_r5_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.SUB_MEMv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r5_memory context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 6` and no LOCK prefix in 64-bit mode, opcode 81's form selection picks
form 11, `XOR_MEMv_IMMz`. -/
theorem selectLegacy0Opcode81_run_of_r6_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 11 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-81 decoder with a memory ModRM, `reg = 6` and no LOCK prefix runs `XOR_MEMv_IMMz`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode81_run_of_r6_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.XOR_MEMv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r6_memory context hlock a b c d e f modrm
      hmod hreg)

/--
With `mod ≠ 3`, `reg = 7` in 64-bit mode, opcode 81's form selection picks form 17, `CMP_MEMv_IMMz`.
-/
theorem selectLegacy0Opcode81_run_of_r7_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 17 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-81 decoder with a memory ModRM, `reg = 7` runs `CMP_MEMv_IMMz` from the state after
the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode81_run_of_r7_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.CMP_MEMv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r7_memory context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3`, `reg = 0` and a LOCK prefix in 64-bit mode, opcode 81's form selection picks
form 3, `ADD_LOCK_MEMv_IMMz`. -/
theorem selectLegacy0Opcode81_run_of_r0_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 3 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-81 decoder with a memory ModRM, `reg = 0` and a LOCK prefix runs `ADD_LOCK_MEMv_IMMz`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode81_run_of_r0_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.ADD_LOCK_MEMv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r0_memory_lock context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 1` and a LOCK prefix in 64-bit mode, opcode 81's form selection picks
form 23, `OR_LOCK_MEMv_IMMz`. -/
theorem selectLegacy0Opcode81_run_of_r1_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 23 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-81 decoder with a memory ModRM, `reg = 1` and a LOCK prefix runs `OR_LOCK_MEMv_IMMz`
from
the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode81_run_of_r1_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.OR_LOCK_MEMv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r1_memory_lock context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 2` and a LOCK prefix in 64-bit mode, opcode 81's form selection picks
form 6, `ADC_LOCK_MEMv_IMMz`. -/
theorem selectLegacy0Opcode81_run_of_r2_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 6 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-81 decoder with a memory ModRM, `reg = 2` and a LOCK prefix runs `ADC_LOCK_MEMv_IMMz`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode81_run_of_r2_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.ADC_LOCK_MEMv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r2_memory_lock context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 3` and a LOCK prefix in 64-bit mode, opcode 81's form selection picks
form 9, `SBB_LOCK_MEMv_IMMz`. -/
theorem selectLegacy0Opcode81_run_of_r3_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 9 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-81 decoder with a memory ModRM, `reg = 3` and a LOCK prefix runs `SBB_LOCK_MEMv_IMMz`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode81_run_of_r3_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3) (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.SBB_LOCK_MEMv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r3_memory_lock context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 4` and a LOCK prefix in 64-bit mode, opcode 81's form selection picks
form 20, `AND_LOCK_MEMv_IMMz`. -/
theorem selectLegacy0Opcode81_run_of_r4_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 20 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-81 decoder with a memory ModRM, `reg = 4` and a LOCK prefix runs `AND_LOCK_MEMv_IMMz`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode81_run_of_r4_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.AND_LOCK_MEMv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r4_memory_lock context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 5` and a LOCK prefix in 64-bit mode, opcode 81's form selection picks
form 15, `SUB_LOCK_MEMv_IMMz`. -/
theorem selectLegacy0Opcode81_run_of_r5_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 15 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-81 decoder with a memory ModRM, `reg = 5` and a LOCK prefix runs `SUB_LOCK_MEMv_IMMz`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode81_run_of_r5_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.SUB_LOCK_MEMv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r5_memory_lock context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 6` and a LOCK prefix in 64-bit mode, opcode 81's form selection picks
form 12, `XOR_LOCK_MEMv_IMMz`. -/
theorem selectLegacy0Opcode81_run_of_r6_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_0_Opcode_81 context true a b c d e f modrm = .ok 12 := by
  simp [Select_Legacy_0_Opcode_81, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-81 decoder with a memory ModRM, `reg = 6` and a LOCK prefix runs `XOR_LOCK_MEMv_IMMz`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode81_run_of_r6_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_81 ip context).run s =
      (X86.Instructions.XOR_LOCK_MEMv_IMMz (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_81
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode81_run_of_r6_memory_lock context hlock a b c d e f modrm
      hmod hreg)

end X86Proofs
