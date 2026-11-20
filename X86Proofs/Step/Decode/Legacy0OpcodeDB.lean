import X86Proofs.Step.Decode

/-!
# Opcode `DB`: x87 `m32int`, `m80real`, FCMOVNB/NE/NBE/NU, FNCLEX, FNINIT, FUCOMI, FCOMI

The one place that looks inside lean-x86's opcode-`DB` decoder (`Decode_Legacy_0_Opcode_DB`) and
its form selection (`Select_Legacy_0_Opcode_DB`), architecture rule 5. The decoder may diverge
(`PartialSpecM`) and passes the opcode byte to the x87 forms (for FOP). For each register form
(`mod = 3`) the library uses, a `selectLegacy0OpcodeDB_run_of_r<reg>[_rm<rm>]_register` lemma gives
the form the selection picks, and a `decodeLegacy0OpcodeDB_run_of_…` lemma runs the decoder (from
the ModRM fetch at `ip + 1`) to the call of that form at `ip + 2` (`decode_modrm_form_partial`).
Register forms with an ST(i) operand are chosen by `mod` and `reg`; the others also by `rm`.
Memory forms (`mod ≠ 3`) are chosen by `reg` alone: `selectLegacy0OpcodeDB_run_of_r<reg>_memory`
and `decodeLegacy0OpcodeDB_run_of_r<reg>_memory`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3`, `reg = 5` in 64-bit mode, opcode DB's form selection picks form
1, `FUCOMI_ST0_X87`. -/
theorem selectLegacy0OpcodeDB_run_of_r5_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_0_Opcode_DB context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_DB, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DB decoder on a ModRM byte selecting `FUCOMI_ST0_X87` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDB_run_of_r5_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DB ip context 0xDB).run s =
      some ((X86.Instructions.FUCOMI_ST0_X87 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDB).run t) := by
  unfold Decode_Legacy_0_Opcode_DB
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDB_run_of_r5_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 6` in 64-bit mode, opcode DB's form selection picks form
2, `FCOMI_ST0_X87`. -/
theorem selectLegacy0OpcodeDB_run_of_r6_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_0_Opcode_DB context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_DB, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DB decoder on a ModRM byte selecting `FCOMI_ST0_X87` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDB_run_of_r6_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DB ip context 0xDB).run s =
      some ((X86.Instructions.FCOMI_ST0_X87 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDB).run t) := by
  unfold Decode_Legacy_0_Opcode_DB
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDB_run_of_r6_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 4`, `rm = 2` in 64-bit mode, opcode DB's form selection picks form
8, `FNCLEX`. -/
theorem selectLegacy0OpcodeDB_run_of_r4_rm2_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hrm : modrm.extractLsb' 0 3 = 2#3) :
    Select_Legacy_0_Opcode_DB context true a b c d e f modrm = .ok 8 := by
  simp [Select_Legacy_0_Opcode_DB, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DB decoder on a ModRM byte selecting `FNCLEX` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDB_run_of_r4_rm2_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hrm : modrm.extractLsb' 0 3 = 2#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DB ip context 0xDB).run s =
      some ((X86.Instructions.FNCLEX (BitVec.add ip 2#64) context).run t) := by
  unfold Decode_Legacy_0_Opcode_DB
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDB_run_of_r4_rm2_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 4`, `rm = 3` in 64-bit mode, opcode DB's form selection picks form
9, `FNINIT`. -/
theorem selectLegacy0OpcodeDB_run_of_r4_rm3_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hrm : modrm.extractLsb' 0 3 = 3#3) :
    Select_Legacy_0_Opcode_DB context true a b c d e f modrm = .ok 9 := by
  simp [Select_Legacy_0_Opcode_DB, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DB decoder on a ModRM byte selecting `FNINIT` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDB_run_of_r4_rm3_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hrm : modrm.extractLsb' 0 3 = 3#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DB ip context 0xDB).run s =
      some ((X86.Instructions.FNINIT (BitVec.add ip 2#64) context).run t) := by
  unfold Decode_Legacy_0_Opcode_DB
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDB_run_of_r4_rm3_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 0` in 64-bit mode, opcode DB's form selection picks form
10, `FCMOVNB_ST0_X87`. -/
theorem selectLegacy0OpcodeDB_run_of_r0_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_DB context true a b c d e f modrm = .ok 10 := by
  simp [Select_Legacy_0_Opcode_DB, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DB decoder on a ModRM byte selecting `FCMOVNB_ST0_X87` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDB_run_of_r0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DB ip context 0xDB).run s =
      some ((X86.Instructions.FCMOVNB_ST0_X87 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDB).run t) := by
  unfold Decode_Legacy_0_Opcode_DB
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDB_run_of_r0_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 1` in 64-bit mode, opcode DB's form selection picks form
11, `FCMOVNE_ST0_X87`. -/
theorem selectLegacy0OpcodeDB_run_of_r1_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_DB context true a b c d e f modrm = .ok 11 := by
  simp [Select_Legacy_0_Opcode_DB, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DB decoder on a ModRM byte selecting `FCMOVNE_ST0_X87` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDB_run_of_r1_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DB ip context 0xDB).run s =
      some ((X86.Instructions.FCMOVNE_ST0_X87 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDB).run t) := by
  unfold Decode_Legacy_0_Opcode_DB
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDB_run_of_r1_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 2` in 64-bit mode, opcode DB's form selection picks form
12, `FCMOVNBE_ST0_X87`. -/
theorem selectLegacy0OpcodeDB_run_of_r2_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_0_Opcode_DB context true a b c d e f modrm = .ok 12 := by
  simp [Select_Legacy_0_Opcode_DB, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DB decoder on a ModRM byte selecting `FCMOVNBE_ST0_X87` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDB_run_of_r2_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DB ip context 0xDB).run s =
      some ((X86.Instructions.FCMOVNBE_ST0_X87 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDB).run t) := by
  unfold Decode_Legacy_0_Opcode_DB
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDB_run_of_r2_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 3` in 64-bit mode, opcode DB's form selection picks form
13, `FCMOVNU_ST0_X87`. -/
theorem selectLegacy0OpcodeDB_run_of_r3_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_0_Opcode_DB context true a b c d e f modrm = .ok 13 := by
  simp [Select_Legacy_0_Opcode_DB, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DB decoder on a ModRM byte selecting `FCMOVNU_ST0_X87` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDB_run_of_r3_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DB ip context 0xDB).run s =
      some ((X86.Instructions.FCMOVNU_ST0_X87 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDB).run t) := by
  unfold Decode_Legacy_0_Opcode_DB
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDB_run_of_r3_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 4`, `rm = 0` in 64-bit mode, opcode DB's form selection picks form
14, `FENI8087_NOP`. -/
theorem selectLegacy0OpcodeDB_run_of_r4_rm0_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hrm : modrm.extractLsb' 0 3 = 0#3) :
    Select_Legacy_0_Opcode_DB context true a b c d e f modrm = .ok 14 := by
  simp [Select_Legacy_0_Opcode_DB, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DB decoder on a ModRM byte selecting `FENI8087_NOP` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDB_run_of_r4_rm0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hrm : modrm.extractLsb' 0 3 = 0#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DB ip context 0xDB).run s =
      some ((X86.Instructions.FENI8087_NOP (BitVec.add ip 2#64) context).run t) := by
  unfold Decode_Legacy_0_Opcode_DB
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDB_run_of_r4_rm0_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 4`, `rm = 1` in 64-bit mode, opcode DB's form selection picks form
15, `FDISI8087_NOP`. -/
theorem selectLegacy0OpcodeDB_run_of_r4_rm1_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hrm : modrm.extractLsb' 0 3 = 1#3) :
    Select_Legacy_0_Opcode_DB context true a b c d e f modrm = .ok 15 := by
  simp [Select_Legacy_0_Opcode_DB, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DB decoder on a ModRM byte selecting `FDISI8087_NOP` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDB_run_of_r4_rm1_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hrm : modrm.extractLsb' 0 3 = 1#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DB ip context 0xDB).run s =
      some ((X86.Instructions.FDISI8087_NOP (BitVec.add ip 2#64) context).run t) := by
  unfold Decode_Legacy_0_Opcode_DB
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDB_run_of_r4_rm1_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 4`, `rm = 4` in 64-bit mode, opcode DB's form selection picks form
16, `FSETPM287_NOP`. -/
theorem selectLegacy0OpcodeDB_run_of_r4_rm4_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hrm : modrm.extractLsb' 0 3 = 4#3) :
    Select_Legacy_0_Opcode_DB context true a b c d e f modrm = .ok 16 := by
  simp [Select_Legacy_0_Opcode_DB, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DB decoder on a ModRM byte selecting `FSETPM287_NOP` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDB_run_of_r4_rm4_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hrm : modrm.extractLsb' 0 3 = 4#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DB ip context 0xDB).run s =
      some ((X86.Instructions.FSETPM287_NOP (BitVec.add ip 2#64) context).run t) := by
  unfold Decode_Legacy_0_Opcode_DB
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDB_run_of_r4_rm4_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod ≠ 3`, `reg = 0` in 64-bit mode, opcode DB's form selection picks form
6, `FILD_ST0_MEMmem32int`. -/
theorem selectLegacy0OpcodeDB_run_of_r0_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_DB context true a b c d e f modrm = .ok 6 := by
  simp [Select_Legacy_0_Opcode_DB, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DB decoder on a memory ModRM byte selecting `FILD_ST0_MEMmem32int` runs that form
from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDB_run_of_r0_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DB ip context 0xDB).run s =
      (X86.Instructions.FILD_ST0_MEMmem32int (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
          (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDB).run t := by
  unfold Decode_Legacy_0_Opcode_DB
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDB_run_of_r0_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 2` in 64-bit mode, opcode DB's form selection picks form
3, `FIST_MEMmem32int_ST0`. -/
theorem selectLegacy0OpcodeDB_run_of_r2_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_0_Opcode_DB context true a b c d e f modrm = .ok 3 := by
  simp [Select_Legacy_0_Opcode_DB, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DB decoder on a memory ModRM byte selecting `FIST_MEMmem32int_ST0` runs that form
from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDB_run_of_r2_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DB ip context 0xDB).run s =
      some
          ((X86.Instructions.FIST_MEMmem32int_ST0 (BitVec.add ip 2#64) context
          (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDB).run t) := by
  unfold Decode_Legacy_0_Opcode_DB
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDB_run_of_r2_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 3` in 64-bit mode, opcode DB's form selection picks form
4, `FISTP_MEMmem32int_ST0`. -/
theorem selectLegacy0OpcodeDB_run_of_r3_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_0_Opcode_DB context true a b c d e f modrm = .ok 4 := by
  simp [Select_Legacy_0_Opcode_DB, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DB decoder on a memory ModRM byte selecting `FISTP_MEMmem32int_ST0` runs that form
from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDB_run_of_r3_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DB ip context 0xDB).run s =
      some
          ((X86.Instructions.FISTP_MEMmem32int_ST0 (BitVec.add ip 2#64) context
          (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDB).run t) := by
  unfold Decode_Legacy_0_Opcode_DB
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDB_run_of_r3_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 5` in 64-bit mode, opcode DB's form selection picks form
7, `FLD_ST0_MEMmem80real`. -/
theorem selectLegacy0OpcodeDB_run_of_r5_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_0_Opcode_DB context true a b c d e f modrm = .ok 7 := by
  simp [Select_Legacy_0_Opcode_DB, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DB decoder on a memory ModRM byte selecting `FLD_ST0_MEMmem80real` runs that form
from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDB_run_of_r5_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DB ip context 0xDB).run s =
      some
          ((X86.Instructions.FLD_ST0_MEMmem80real (BitVec.add ip 2#64) context
          (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDB).run t) := by
  unfold Decode_Legacy_0_Opcode_DB
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDB_run_of_r5_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 7` in 64-bit mode, opcode DB's form selection picks form
5, `FSTP_MEMmem80real_ST0`. -/
theorem selectLegacy0OpcodeDB_run_of_r7_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_0_Opcode_DB context true a b c d e f modrm = .ok 5 := by
  simp [Select_Legacy_0_Opcode_DB, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DB decoder on a memory ModRM byte selecting `FSTP_MEMmem80real_ST0` runs that form
from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDB_run_of_r7_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DB ip context 0xDB).run s =
      some
          ((X86.Instructions.FSTP_MEMmem80real_ST0 (BitVec.add ip 2#64) context
          (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDB).run t) := by
  unfold Decode_Legacy_0_Opcode_DB
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDB_run_of_r7_memory context a b c d e f modrm hmod
        hreg)

end X86Proofs
