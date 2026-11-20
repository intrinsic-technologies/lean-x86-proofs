import X86Proofs.Step.Decode

/-!
# Opcode `F7`: group 3 (`TEST r/m, imm32`, `NOT`, `NEG`, `MUL`, …)

The one place that looks inside lean-x86's opcode-`F7` decoder (`Decode_Legacy_0_Opcode_F7`) and its
form selection (`Select_Legacy_0_Opcode_F7`), architecture rule 5. Several instruction folders use
the opcode, each through the lemmas here. For each ModRM case the library uses — `reg = 0`
(`TEST r, imm32`, `Instructions/Test/Generated/Imm32`), `reg = 2` (`NOT`, `Instructions/Not`) and
`reg = 3` (`NEG`, `Instructions/Neg`) with `mod = 3`, and `reg = 0` with a memory operand
(`TEST m, imm32`, `Instructions/Test/Generated/MImm32`), `reg = 2` and `reg = 3` with a memory
operand and no LOCK prefix (`NOT m`, `NEG m`, `Instructions/{Not,Neg}/Generated/M`) — a
`selectLegacy0OpcodeF7_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy0OpcodeF7_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`) to the
call of that form at `ip + 2` (`TEST`'s form fetches the immediate itself). The one-operand
multiply and divide — `reg = 4` (`MUL`), `5` (`IMUL`), `6` (`DIV`), `7` (`IDIV`) — have such a
pair with `mod = 3` and with a memory operand (`Instructions/{Mul,Imul,Div,Idiv}/Generated/{R,M}`);
their memory forms' selection does not depend on LOCK (the form checks it). For a new case, add the pair here
(the decoder lemma is `decode_modrm_form`).

TEST's undocumented alias `reg = 1` (`TEST_GPRv_IMMz_F7r1`, `TEST_MEMv_IMMz_F7r1`) has a pair with
`mod = 3` and with a memory operand (`…_r1_register`, `…_r1_memory`); the alias forms' bodies are
the `reg = 0` forms', so the decoder lemmas are stated with those
(`Instructions/Test/Generated/Imm32R1`, `MImm32R1`).

The `…_lock` pairs are the same cases with a LOCK prefix (`lock_prefix_present = true`),
selecting the `<OP>_LOCK_…` form (the generated `…Lock` rows).

`Decode_Legacy_0`'s dispatch to this decoder is `decodeLegacy0_run_of_opcodeF7`
(`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` and `reg = 2` in 64-bit mode, opcode F7's form selection picks form 12,
`NOT_GPRv`. -/
theorem selectLegacy0OpcodeF7_run_of_not_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_0_Opcode_F7 context true a b c d e f modrm = .ok 12 := by
  simp [Select_Legacy_0_Opcode_F7, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-F7 decoder with a register ModRM and `reg = 2`. If fetching the byte after the opcode at
`ip` returns a ModRM byte with `mod = 3` and `reg = 2` and leaves state `t` (in 64-bit mode, decoder
features answered), the decoder runs `NOT_GPRv` from `t` with `Next_IP` `ip + 2` and the
ModRM `rm` field.
-/
theorem decodeLegacy0OpcodeF7_run_of_not_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_F7 ip context).run s =
      (X86.Instructions.NOT_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_F7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeF7_run_of_not_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 0` in 64-bit mode, opcode F7's form selection picks form
15, `TEST_GPRv_IMMz_F7r0`. -/
theorem selectLegacy0OpcodeF7_run_of_r0_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_F7 context true a b c d e f modrm = .ok 15 := by
  simp [Select_Legacy_0_Opcode_F7, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-F7 decoder with a register ModRM and `reg = 0`. If fetching the byte after
the opcode at `ip` returns a ModRM byte with `mod = 3`, `reg = 0` and leaves state `t` (in
64-bit mode, decoder features answered), the decoder runs `TEST_GPRv_IMMz_F7r0` from `t` with `ip + 2`
(the address of the immediate) and the ModRM `rm` field.
-/
theorem decodeLegacy0OpcodeF7_run_of_r0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_F7 ip context).run s =
      (X86.Instructions.TEST_GPRv_IMMz_F7r0 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_F7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeF7_run_of_r0_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 3` in 64-bit mode, opcode F7's form selection picks form 7,
`NEG_GPRv`. -/
theorem selectLegacy0OpcodeF7_run_of_neg_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_0_Opcode_F7 context true a b c d e f modrm = .ok 7 := by
  simp [Select_Legacy_0_Opcode_F7, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-F7 decoder with a register ModRM and `reg = 3`. If fetching the byte after the opcode at
`ip` returns a ModRM byte with `mod = 3` and `reg = 3` and leaves state `t` (in 64-bit mode, decoder
features answered), the decoder runs `NEG_GPRv` from `t` with `Next_IP` `ip + 2` and the
ModRM `rm` field.
-/
theorem decodeLegacy0OpcodeF7_run_of_neg_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_F7 ip context).run s =
      (X86.Instructions.NEG_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_F7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeF7_run_of_neg_register context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3`, `reg = 0` in 64-bit mode, opcode F7's form selection picks form 16,
`TEST_MEMv_IMMz_F7r0`. -/
theorem selectLegacy0OpcodeF7_run_of_r0_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_F7 context true a b c d e f modrm = .ok 16 := by
  simp [Select_Legacy_0_Opcode_F7, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-F7 decoder with a memory ModRM, `reg = 0` runs `TEST_MEMv_IMMz_F7r0` from the state
after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeF7_run_of_r0_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_F7 ip context).run s =
      (X86.Instructions.TEST_MEMv_IMMz_F7r0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_F7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeF7_run_of_r0_memory context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3`, `reg = 2` and no LOCK prefix in 64-bit mode, opcode F7's form selection picks
form 13, `NOT_MEMv`. -/
theorem selectLegacy0OpcodeF7_run_of_not_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_0_Opcode_F7 context true a b c d e f modrm = .ok 13 := by
  simp [Select_Legacy_0_Opcode_F7, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-F7 decoder with a memory ModRM, `reg = 2` and no LOCK prefix runs `NOT_MEMv`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeF7_run_of_not_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_F7 ip context).run s =
      (X86.Instructions.NOT_MEMv (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_F7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeF7_run_of_not_memory context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 3` and no LOCK prefix in 64-bit mode, opcode F7's form selection picks
form 8, `NEG_MEMv`. -/
theorem selectLegacy0OpcodeF7_run_of_neg_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_0_Opcode_F7 context true a b c d e f modrm = .ok 8 := by
  simp [Select_Legacy_0_Opcode_F7, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-F7 decoder with a memory ModRM, `reg = 3` and no LOCK prefix runs `NEG_MEMv`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeF7_run_of_neg_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3) (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_F7 ip context).run s =
      (X86.Instructions.NEG_MEMv (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_F7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeF7_run_of_neg_memory context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod = 3` and `reg = 4` in 64-bit mode, opcode F7's form selection picks form
3, `MUL_GPRv`. -/
theorem selectLegacy0OpcodeF7_run_of_mul_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_0_Opcode_F7 context true a b c d e f modrm = .ok 3 := by
  simp [Select_Legacy_0_Opcode_F7, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/-- The opcode-F7 decoder with a register ModRM and `reg = 4` runs `MUL_GPRv` from the state after
the ModRM fetch, with `Next_IP` `ip + 2` and the ModRM `rm` field. -/
theorem decodeLegacy0OpcodeF7_run_of_mul_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_F7 ip context).run s =
      (X86.Instructions.MUL_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_F7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeF7_run_of_mul_register context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3` and `reg = 4` in 64-bit mode, opcode F7's form selection picks form 4,
`MUL_MEMv`. -/
theorem selectLegacy0OpcodeF7_run_of_mul_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_0_Opcode_F7 context true a b c d e f modrm = .ok 4 := by
  simp [Select_Legacy_0_Opcode_F7, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-F7 decoder with a memory ModRM and `reg = 4` runs `MUL_MEMv` from the state after the
ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeF7_run_of_mul_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_F7 ip context).run s =
      (X86.Instructions.MUL_MEMv (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_F7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeF7_run_of_mul_memory context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 5` in 64-bit mode, opcode F7's form selection picks form
1, `IMUL_GPRv`. -/
theorem selectLegacy0OpcodeF7_run_of_imul_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_0_Opcode_F7 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_F7, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/-- The opcode-F7 decoder with a register ModRM and `reg = 5` runs `IMUL_GPRv` from the state after
the ModRM fetch, with `Next_IP` `ip + 2` and the ModRM `rm` field. -/
theorem decodeLegacy0OpcodeF7_run_of_imul_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_F7 ip context).run s =
      (X86.Instructions.IMUL_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_F7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeF7_run_of_imul_register context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3` and `reg = 5` in 64-bit mode, opcode F7's form selection picks form 2,
`IMUL_MEMv`. -/
theorem selectLegacy0OpcodeF7_run_of_imul_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_0_Opcode_F7 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_F7, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-F7 decoder with a memory ModRM and `reg = 5` runs `IMUL_MEMv` from the state after the
ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeF7_run_of_imul_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_F7 ip context).run s =
      (X86.Instructions.IMUL_MEMv (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_F7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeF7_run_of_imul_memory context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 6` in 64-bit mode, opcode F7's form selection picks form
5, `DIV_GPRv`. -/
theorem selectLegacy0OpcodeF7_run_of_div_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_0_Opcode_F7 context true a b c d e f modrm = .ok 5 := by
  simp [Select_Legacy_0_Opcode_F7, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/-- The opcode-F7 decoder with a register ModRM and `reg = 6` runs `DIV_GPRv` from the state after
the ModRM fetch, with `Next_IP` `ip + 2` and the ModRM `rm` field. -/
theorem decodeLegacy0OpcodeF7_run_of_div_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_F7 ip context).run s =
      (X86.Instructions.DIV_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_F7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeF7_run_of_div_register context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3` and `reg = 6` in 64-bit mode, opcode F7's form selection picks form 6,
`DIV_MEMv`. -/
theorem selectLegacy0OpcodeF7_run_of_div_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_0_Opcode_F7 context true a b c d e f modrm = .ok 6 := by
  simp [Select_Legacy_0_Opcode_F7, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-F7 decoder with a memory ModRM and `reg = 6` runs `DIV_MEMv` from the state after the
ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeF7_run_of_div_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_F7 ip context).run s =
      (X86.Instructions.DIV_MEMv (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_F7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeF7_run_of_div_memory context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 7` in 64-bit mode, opcode F7's form selection picks form
10, `IDIV_GPRv`. -/
theorem selectLegacy0OpcodeF7_run_of_idiv_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_0_Opcode_F7 context true a b c d e f modrm = .ok 10 := by
  simp [Select_Legacy_0_Opcode_F7, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/-- The opcode-F7 decoder with a register ModRM and `reg = 7` runs `IDIV_GPRv` from the state after
the ModRM fetch, with `Next_IP` `ip + 2` and the ModRM `rm` field. -/
theorem decodeLegacy0OpcodeF7_run_of_idiv_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_F7 ip context).run s =
      (X86.Instructions.IDIV_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_F7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeF7_run_of_idiv_register context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3` and `reg = 7` in 64-bit mode, opcode F7's form selection picks form 11,
`IDIV_MEMv`. -/
theorem selectLegacy0OpcodeF7_run_of_idiv_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_0_Opcode_F7 context true a b c d e f modrm = .ok 11 := by
  simp [Select_Legacy_0_Opcode_F7, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-F7 decoder with a memory ModRM and `reg = 7` runs `IDIV_MEMv` from the state after the
ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeF7_run_of_idiv_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_F7 ip context).run s =
      (X86.Instructions.IDIV_MEMv (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_F7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeF7_run_of_idiv_memory context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3`, `reg = 2` and a LOCK prefix in 64-bit mode, opcode F7's form selection picks
form 14, `NOT_LOCK_MEMv`. -/
theorem selectLegacy0OpcodeF7_run_of_not_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_0_Opcode_F7 context true a b c d e f modrm = .ok 14 := by
  simp [Select_Legacy_0_Opcode_F7, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-F7 decoder with a memory ModRM, `reg = 2` and a LOCK prefix runs `NOT_LOCK_MEMv`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeF7_run_of_not_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_F7 ip context).run s =
      (X86.Instructions.NOT_LOCK_MEMv (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_F7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeF7_run_of_not_memory_lock context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 3` and a LOCK prefix in 64-bit mode, opcode F7's form selection picks
form 9, `NEG_LOCK_MEMv`. -/
theorem selectLegacy0OpcodeF7_run_of_neg_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_0_Opcode_F7 context true a b c d e f modrm = .ok 9 := by
  simp [Select_Legacy_0_Opcode_F7, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-F7 decoder with a memory ModRM, `reg = 3` and a LOCK prefix runs `NEG_LOCK_MEMv`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0OpcodeF7_run_of_neg_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3) (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_F7 ip context).run s =
      (X86.Instructions.NEG_LOCK_MEMv (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_F7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeF7_run_of_neg_memory_lock context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod = 3` and `reg = 1` in 64-bit mode, opcode F7's form selection picks form 17,
`TEST_GPRv_IMMz_F7r1` (TEST's undocumented `/1` alias). -/
theorem selectLegacy0OpcodeF7_run_of_r1_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_F7 context true a b c d e f modrm = .ok 17 := by
  simp [Select_Legacy_0_Opcode_F7, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-F7 decoder with a register ModRM and `reg = 1` runs `TEST_GPRv_IMMz_F7r1`, whose body is
`TEST_GPRv_IMMz_F7r0`'s (the `/1` alias of TEST), so it is stated with the `/0` form: from the
state `t` after the ModRM fetch, with `ip + 2` (the address of the immediate) and the ModRM `rm`
field.
-/
theorem decodeLegacy0OpcodeF7_run_of_r1_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_F7 ip context).run s =
      (X86.Instructions.TEST_GPRv_IMMz_F7r0 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_F7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy0OpcodeF7_run_of_r1_register context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3` and `reg = 1` in 64-bit mode, opcode F7's form selection picks form 18,
`TEST_MEMv_IMMz_F7r1`. -/
theorem selectLegacy0OpcodeF7_run_of_r1_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_F7 context true a b c d e f modrm = .ok 18 := by
  simp [Select_Legacy_0_Opcode_F7, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-F7 decoder with a memory ModRM and `reg = 1` runs `TEST_MEMv_IMMz_F7r1`, whose body
is `TEST_MEMv_IMMz_F7r0`'s, from the state after the ModRM fetch, at the address after the ModRM
byte. -/
theorem decodeLegacy0OpcodeF7_run_of_r1_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_F7 ip context).run s =
      (X86.Instructions.TEST_MEMv_IMMz_F7r0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_F7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy0OpcodeF7_run_of_r1_memory context a b c d e f modrm hmod hreg)

end X86Proofs
