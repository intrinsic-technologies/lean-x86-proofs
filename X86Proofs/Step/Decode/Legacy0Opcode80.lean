import X86Proofs.Step.Decode

/-!
# Opcode `80`: group 1 with an 8-bit register and immediate (`… r/m8, imm8`)

The one place that looks inside lean-x86's opcode-`80` decoder (`Decode_Legacy_0_Opcode_80`) and its
form selection (`Select_Legacy_0_Opcode_80`), architecture rule 5. Several instruction folders use
the opcode, each through the lemmas here. For each ModRM `reg` digit with `mod = 3` (`ADD`, `OR`,
`ADC`, `SBB`, `AND`, `SUB`, `XOR`, `CMP` of a register; `Instructions/<Op>/Generated/R8Imm8`), and
for each digit with a memory operand and no LOCK prefix (a byte in memory;
`Instructions/<Op>/Generated/M8Imm8`) — a `selectLegacy0Opcode80_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy0Opcode80_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`) to the
call of that form at `ip + 2` (the form fetches the immediate itself). For a new case, add the pair
here (the decoder lemma is `decode_modrm_form`).

The `…_lock` pairs are the same cases with a LOCK prefix (`lock_prefix_present = true`),
selecting the `<OP>_LOCK_…` form (the generated `…Lock` rows).

`Decode_Legacy_0`'s dispatch to this decoder is `decodeLegacy0_run_of_opcode80`
(`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` and `reg = 0` in 64-bit mode, opcode 80's form selection picks form
1, `ADD_GPR8_IMMb_80r0`. -/
theorem selectLegacy0Opcode80_run_of_r0_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-80 decoder with a register ModRM and `reg = 0`. If fetching the byte after
the opcode at `ip` returns a ModRM byte with `mod = 3`, `reg = 0` and leaves state `t` (in
64-bit mode, decoder features answered), the decoder runs `ADD_GPR8_IMMb_80r0` from `t` with `ip + 2`
(the address of the immediate) and the ModRM `rm` field.
-/
theorem decodeLegacy0Opcode80_run_of_r0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.ADD_GPR8_IMMb_80r0 (BitVec.add ip 2#64) context (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r0_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 1` in 64-bit mode, opcode 80's form selection picks form
21, `OR_GPR8_IMMb_80r1`. -/
theorem selectLegacy0Opcode80_run_of_r1_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 21 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-80 decoder with a register ModRM and `reg = 1`. If fetching the byte after
the opcode at `ip` returns a ModRM byte with `mod = 3`, `reg = 1` and leaves state `t` (in
64-bit mode, decoder features answered), the decoder runs `OR_GPR8_IMMb_80r1` from `t` with `ip + 2`
(the address of the immediate) and the ModRM `rm` field.
-/
theorem decodeLegacy0Opcode80_run_of_r1_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.OR_GPR8_IMMb_80r1 (BitVec.add ip 2#64) context (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r1_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 2` in 64-bit mode, opcode 80's form selection picks form
4, `ADC_GPR8_IMMb_80r2`. -/
theorem selectLegacy0Opcode80_run_of_r2_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 4 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-80 decoder with a register ModRM and `reg = 2`. If fetching the byte after
the opcode at `ip` returns a ModRM byte with `mod = 3`, `reg = 2` and leaves state `t` (in
64-bit mode, decoder features answered), the decoder runs `ADC_GPR8_IMMb_80r2` from `t` with `ip + 2`
(the address of the immediate) and the ModRM `rm` field.
-/
theorem decodeLegacy0Opcode80_run_of_r2_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.ADC_GPR8_IMMb_80r2 (BitVec.add ip 2#64) context (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r2_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 3` in 64-bit mode, opcode 80's form selection picks form
7, `SBB_GPR8_IMMb_80r3`. -/
theorem selectLegacy0Opcode80_run_of_r3_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 7 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-80 decoder with a register ModRM and `reg = 3`. If fetching the byte after
the opcode at `ip` returns a ModRM byte with `mod = 3`, `reg = 3` and leaves state `t` (in
64-bit mode, decoder features answered), the decoder runs `SBB_GPR8_IMMb_80r3` from `t` with `ip + 2`
(the address of the immediate) and the ModRM `rm` field.
-/
theorem decodeLegacy0Opcode80_run_of_r3_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.SBB_GPR8_IMMb_80r3 (BitVec.add ip 2#64) context (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r3_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 4` in 64-bit mode, opcode 80's form selection picks form
18, `AND_GPR8_IMMb_80r4`. -/
theorem selectLegacy0Opcode80_run_of_r4_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 18 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-80 decoder with a register ModRM and `reg = 4`. If fetching the byte after
the opcode at `ip` returns a ModRM byte with `mod = 3`, `reg = 4` and leaves state `t` (in
64-bit mode, decoder features answered), the decoder runs `AND_GPR8_IMMb_80r4` from `t` with `ip + 2`
(the address of the immediate) and the ModRM `rm` field.
-/
theorem decodeLegacy0Opcode80_run_of_r4_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.AND_GPR8_IMMb_80r4 (BitVec.add ip 2#64) context (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r4_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 5` in 64-bit mode, opcode 80's form selection picks form
13, `SUB_GPR8_IMMb_80r5`. -/
theorem selectLegacy0Opcode80_run_of_r5_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 13 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-80 decoder with a register ModRM and `reg = 5`. If fetching the byte after
the opcode at `ip` returns a ModRM byte with `mod = 3`, `reg = 5` and leaves state `t` (in
64-bit mode, decoder features answered), the decoder runs `SUB_GPR8_IMMb_80r5` from `t` with `ip + 2`
(the address of the immediate) and the ModRM `rm` field.
-/
theorem decodeLegacy0Opcode80_run_of_r5_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.SUB_GPR8_IMMb_80r5 (BitVec.add ip 2#64) context (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r5_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 6` in 64-bit mode, opcode 80's form selection picks form
10, `XOR_GPR8_IMMb_80r6`. -/
theorem selectLegacy0Opcode80_run_of_r6_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 10 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-80 decoder with a register ModRM and `reg = 6`. If fetching the byte after
the opcode at `ip` returns a ModRM byte with `mod = 3`, `reg = 6` and leaves state `t` (in
64-bit mode, decoder features answered), the decoder runs `XOR_GPR8_IMMb_80r6` from `t` with `ip + 2`
(the address of the immediate) and the ModRM `rm` field.
-/
theorem decodeLegacy0Opcode80_run_of_r6_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.XOR_GPR8_IMMb_80r6 (BitVec.add ip 2#64) context (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r6_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 7` in 64-bit mode, opcode 80's form selection picks form
16, `CMP_GPR8_IMMb_80r7`. -/
theorem selectLegacy0Opcode80_run_of_r7_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 16 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

/--
The opcode-80 decoder with a register ModRM and `reg = 7`. If fetching the byte after
the opcode at `ip` returns a ModRM byte with `mod = 3`, `reg = 7` and leaves state `t` (in
64-bit mode, decoder features answered), the decoder runs `CMP_GPR8_IMMb_80r7` from `t` with `ip + 2`
(the address of the immediate) and the ModRM `rm` field.
-/
theorem decodeLegacy0Opcode80_run_of_r7_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.CMP_GPR8_IMMb_80r7 (BitVec.add ip 2#64) context (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r7_register context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3`, `reg = 6`, no LOCK prefix and 64-bit mode, opcode 80's form selection picks
form 11, `XOR_MEMb_IMMb_80r6`. -/
theorem selectLegacy0Opcode80_run_of_r6_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 11 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- With `mod ≠ 3`, `reg = 7` and 64-bit mode, opcode 80's form selection picks form 17,
`CMP_MEMb_IMMb_80r7` (it has no LOCK form). -/
theorem selectLegacy0Opcode80_run_of_r7_memory (context : Instruction_Context) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 17 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-80 decoder with a memory ModRM, `reg = 6` and no LOCK prefix runs
`XOR_MEMb_IMMb_80r6` at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode80_run_of_r6_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.XOR_MEMb_IMMb_80r6 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f =>
    Select_Legacy_0_Opcode_80 context mode a b c d e f modrm) _ 11 hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r6_memory context hlock a b c d e f modrm hmod hreg)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

/-- The opcode-80 decoder with a memory ModRM and `reg = 7` runs `CMP_MEMb_IMMb_80r7`. -/
theorem decodeLegacy0Opcode80_run_of_r7_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.CMP_MEMb_IMMb_80r7 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f =>
    Select_Legacy_0_Opcode_80 context mode a b c d e f modrm) _ 17 hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r7_memory context a b c d e f modrm hmod hreg)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

/-- With `mod ≠ 3`, `reg = 0` and no LOCK prefix in 64-bit mode, opcode 80's form selection picks
form 2, `ADD_MEMb_IMMb_80r0`. -/
theorem selectLegacy0Opcode80_run_of_r0_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-80 decoder with a memory ModRM, `reg = 0` and no LOCK prefix runs
`ADD_MEMb_IMMb_80r0` from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode80_run_of_r0_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.ADD_MEMb_IMMb_80r0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r0_memory context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 1` and no LOCK prefix in 64-bit mode, opcode 80's form selection picks
form 22, `OR_MEMb_IMMb_80r1`. -/
theorem selectLegacy0Opcode80_run_of_r1_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 22 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-80 decoder with a memory ModRM, `reg = 1` and no LOCK prefix runs `OR_MEMb_IMMb_80r1`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode80_run_of_r1_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.OR_MEMb_IMMb_80r1 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r1_memory context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 2` and no LOCK prefix in 64-bit mode, opcode 80's form selection picks
form 5, `ADC_MEMb_IMMb_80r2`. -/
theorem selectLegacy0Opcode80_run_of_r2_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 5 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-80 decoder with a memory ModRM, `reg = 2` and no LOCK prefix runs
`ADC_MEMb_IMMb_80r2` from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode80_run_of_r2_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.ADC_MEMb_IMMb_80r2 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r2_memory context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 3` and no LOCK prefix in 64-bit mode, opcode 80's form selection picks
form 8, `SBB_MEMb_IMMb_80r3`. -/
theorem selectLegacy0Opcode80_run_of_r3_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 8 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-80 decoder with a memory ModRM, `reg = 3` and no LOCK prefix runs
`SBB_MEMb_IMMb_80r3` from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode80_run_of_r3_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3) (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.SBB_MEMb_IMMb_80r3 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r3_memory context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 4` and no LOCK prefix in 64-bit mode, opcode 80's form selection picks
form 19, `AND_MEMb_IMMb_80r4`. -/
theorem selectLegacy0Opcode80_run_of_r4_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 19 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-80 decoder with a memory ModRM, `reg = 4` and no LOCK prefix runs
`AND_MEMb_IMMb_80r4` from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode80_run_of_r4_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.AND_MEMb_IMMb_80r4 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r4_memory context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 5` and no LOCK prefix in 64-bit mode, opcode 80's form selection picks
form 14, `SUB_MEMb_IMMb_80r5`. -/
theorem selectLegacy0Opcode80_run_of_r5_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 14 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-80 decoder with a memory ModRM, `reg = 5` and no LOCK prefix runs
`SUB_MEMb_IMMb_80r5` from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode80_run_of_r5_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.SUB_MEMb_IMMb_80r5 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r5_memory context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 0` and a LOCK prefix in 64-bit mode, opcode 80's form selection picks
form 3, `ADD_LOCK_MEMb_IMMb_80r0`. -/
theorem selectLegacy0Opcode80_run_of_r0_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 3 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-80 decoder with a memory ModRM, `reg = 0` and a LOCK prefix runs
`ADD_LOCK_MEMb_IMMb_80r0` from the state after the ModRM fetch, at the address after the ModRM
byte. -/
theorem decodeLegacy0Opcode80_run_of_r0_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.ADD_LOCK_MEMb_IMMb_80r0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r0_memory_lock context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 1` and a LOCK prefix in 64-bit mode, opcode 80's form selection picks
form 23, `OR_LOCK_MEMb_IMMb_80r1`. -/
theorem selectLegacy0Opcode80_run_of_r1_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 23 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-80 decoder with a memory ModRM, `reg = 1` and a LOCK prefix runs
`OR_LOCK_MEMb_IMMb_80r1`
from the state after the ModRM fetch, at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode80_run_of_r1_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.OR_LOCK_MEMb_IMMb_80r1 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r1_memory_lock context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 2` and a LOCK prefix in 64-bit mode, opcode 80's form selection picks
form 6, `ADC_LOCK_MEMb_IMMb_80r2`. -/
theorem selectLegacy0Opcode80_run_of_r2_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 6 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-80 decoder with a memory ModRM, `reg = 2` and a LOCK prefix runs
`ADC_LOCK_MEMb_IMMb_80r2` from the state after the ModRM fetch, at the address after the ModRM
byte. -/
theorem decodeLegacy0Opcode80_run_of_r2_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.ADC_LOCK_MEMb_IMMb_80r2 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r2_memory_lock context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 3` and a LOCK prefix in 64-bit mode, opcode 80's form selection picks
form 9, `SBB_LOCK_MEMb_IMMb_80r3`. -/
theorem selectLegacy0Opcode80_run_of_r3_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 9 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-80 decoder with a memory ModRM, `reg = 3` and a LOCK prefix runs
`SBB_LOCK_MEMb_IMMb_80r3` from the state after the ModRM fetch, at the address after the ModRM
byte. -/
theorem decodeLegacy0Opcode80_run_of_r3_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3) (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.SBB_LOCK_MEMb_IMMb_80r3 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r3_memory_lock context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 4` and a LOCK prefix in 64-bit mode, opcode 80's form selection picks
form 20, `AND_LOCK_MEMb_IMMb_80r4`. -/
theorem selectLegacy0Opcode80_run_of_r4_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 20 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-80 decoder with a memory ModRM, `reg = 4` and a LOCK prefix runs
`AND_LOCK_MEMb_IMMb_80r4` from the state after the ModRM fetch, at the address after the ModRM
byte. -/
theorem decodeLegacy0Opcode80_run_of_r4_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.AND_LOCK_MEMb_IMMb_80r4 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r4_memory_lock context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 5` and a LOCK prefix in 64-bit mode, opcode 80's form selection picks
form 15, `SUB_LOCK_MEMb_IMMb_80r5`. -/
theorem selectLegacy0Opcode80_run_of_r5_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 15 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-80 decoder with a memory ModRM, `reg = 5` and a LOCK prefix runs
`SUB_LOCK_MEMb_IMMb_80r5` from the state after the ModRM fetch, at the address after the ModRM
byte. -/
theorem decodeLegacy0Opcode80_run_of_r5_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.SUB_LOCK_MEMb_IMMb_80r5 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r5_memory_lock context hlock a b c d e f modrm
      hmod hreg)

/-- With `mod ≠ 3`, `reg = 6`, a LOCK prefix and 64-bit mode, opcode 80's form selection picks
form 12, `XOR_LOCK_MEMb_IMMb_80r6`. -/
theorem selectLegacy0Opcode80_run_of_r6_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 12 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-80 decoder with a memory ModRM, `reg = 6` and a LOCK prefix runs
`XOR_LOCK_MEMb_IMMb_80r6` at the address after the ModRM byte. -/
theorem decodeLegacy0Opcode80_run_of_r6_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.XOR_LOCK_MEMb_IMMb_80r6 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f =>
    Select_Legacy_0_Opcode_80 context mode a b c d e f modrm) _ 12 hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r6_memory_lock context hlock a b c d e f modrm
      hmod hreg)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

end X86Proofs
