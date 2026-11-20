import X86Proofs.Step.Decode

/-!
# Opcode `DC`: x87 arithmetic with `m64real` or ST(i), ST(0) operands

The one place that looks inside lean-x86's opcode-`DC` decoder (`Decode_Legacy_0_Opcode_DC`) and
its form selection (`Select_Legacy_0_Opcode_DC`), architecture rule 5. The decoder may diverge
(`PartialSpecM`) and passes the opcode byte to the x87 forms (for FOP). For each register form
(`mod = 3`) the library uses, a `selectLegacy0OpcodeDC_run_of_r<reg>[_rm<rm>]_register` lemma gives
the form the selection picks, and a `decodeLegacy0OpcodeDC_run_of_…` lemma runs the decoder (from
the ModRM fetch at `ip + 1`) to the call of that form at `ip + 2` (`decode_modrm_form_partial`).
Register forms with an ST(i) operand are chosen by `mod` and `reg`; the others also by `rm`.
Memory forms (`mod ≠ 3`) are chosen by `reg` alone: `selectLegacy0OpcodeDC_run_of_r<reg>_memory`
and `decodeLegacy0OpcodeDC_run_of_r<reg>_memory`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3`, `reg = 0` in 64-bit mode, opcode DC's form selection picks form
2, `FADD_X87_ST0`. -/
theorem selectLegacy0OpcodeDC_run_of_r0_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_DC context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_DC, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DC decoder on a ModRM byte selecting `FADD_X87_ST0` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDC_run_of_r0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DC ip context 0xDC).run s =
      some ((X86.Instructions.FADD_X87_ST0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDC).run t) := by
  unfold Decode_Legacy_0_Opcode_DC
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDC_run_of_r0_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 5` in 64-bit mode, opcode DC's form selection picks form
4, `FSUB_X87_ST0`. -/
theorem selectLegacy0OpcodeDC_run_of_r5_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_0_Opcode_DC context true a b c d e f modrm = .ok 4 := by
  simp [Select_Legacy_0_Opcode_DC, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DC decoder on a ModRM byte selecting `FSUB_X87_ST0` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDC_run_of_r5_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DC ip context 0xDC).run s =
      some ((X86.Instructions.FSUB_X87_ST0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDC).run t) := by
  unfold Decode_Legacy_0_Opcode_DC
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDC_run_of_r5_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 1` in 64-bit mode, opcode DC's form selection picks form
6, `FMUL_X87_ST0`. -/
theorem selectLegacy0OpcodeDC_run_of_r1_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_DC context true a b c d e f modrm = .ok 6 := by
  simp [Select_Legacy_0_Opcode_DC, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DC decoder on a ModRM byte selecting `FMUL_X87_ST0` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDC_run_of_r1_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DC ip context 0xDC).run s =
      some ((X86.Instructions.FMUL_X87_ST0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDC).run t) := by
  unfold Decode_Legacy_0_Opcode_DC
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDC_run_of_r1_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 2` in 64-bit mode, opcode DC's form selection picks form
9, `FCOM_ST0_X87_DCD0`. -/
theorem selectLegacy0OpcodeDC_run_of_r2_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_0_Opcode_DC context true a b c d e f modrm = .ok 9 := by
  simp [Select_Legacy_0_Opcode_DC, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DC decoder on a ModRM byte selecting `FCOM_ST0_X87_DCD0` runs that form from the
state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDC_run_of_r2_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DC ip context 0xDC).run s =
      some ((X86.Instructions.FCOM_ST0_X87_DCD0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDC).run t) := by
  unfold Decode_Legacy_0_Opcode_DC
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDC_run_of_r2_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 3` in 64-bit mode, opcode DC's form selection picks form
10, `FCOMP_ST0_X87_DCD1`. -/
theorem selectLegacy0OpcodeDC_run_of_r3_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_0_Opcode_DC context true a b c d e f modrm = .ok 10 := by
  simp [Select_Legacy_0_Opcode_DC, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DC decoder on a ModRM byte selecting `FCOMP_ST0_X87_DCD1` runs that form from the
state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDC_run_of_r3_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DC ip context 0xDC).run s =
      some
          ((X86.Instructions.FCOMP_ST0_X87_DCD1 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDC).run t) := by
  unfold Decode_Legacy_0_Opcode_DC
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDC_run_of_r3_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 4` in 64-bit mode, opcode DC's form selection picks form
12, `FSUBR_X87_ST0`. -/
theorem selectLegacy0OpcodeDC_run_of_r4_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_0_Opcode_DC context true a b c d e f modrm = .ok 12 := by
  simp [Select_Legacy_0_Opcode_DC, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DC decoder on a ModRM byte selecting `FSUBR_X87_ST0` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDC_run_of_r4_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DC ip context 0xDC).run s =
      some ((X86.Instructions.FSUBR_X87_ST0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDC).run t) := by
  unfold Decode_Legacy_0_Opcode_DC
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDC_run_of_r4_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 7` in 64-bit mode, opcode DC's form selection picks form
14, `FDIV_X87_ST0`. -/
theorem selectLegacy0OpcodeDC_run_of_r7_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_0_Opcode_DC context true a b c d e f modrm = .ok 14 := by
  simp [Select_Legacy_0_Opcode_DC, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DC decoder on a ModRM byte selecting `FDIV_X87_ST0` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDC_run_of_r7_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DC ip context 0xDC).run s =
      some ((X86.Instructions.FDIV_X87_ST0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDC).run t) := by
  unfold Decode_Legacy_0_Opcode_DC
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDC_run_of_r7_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 6` in 64-bit mode, opcode DC's form selection picks form
16, `FDIVR_X87_ST0`. -/
theorem selectLegacy0OpcodeDC_run_of_r6_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_0_Opcode_DC context true a b c d e f modrm = .ok 16 := by
  simp [Select_Legacy_0_Opcode_DC, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DC decoder on a ModRM byte selecting `FDIVR_X87_ST0` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDC_run_of_r6_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DC ip context 0xDC).run s =
      some ((X86.Instructions.FDIVR_X87_ST0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDC).run t) := by
  unfold Decode_Legacy_0_Opcode_DC
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDC_run_of_r6_register context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 0` in 64-bit mode, opcode DC's form selection picks form
1, `FADD_MEMm64real`. -/
theorem selectLegacy0OpcodeDC_run_of_r0_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_DC context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_DC, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DC decoder on a memory ModRM byte selecting `FADD_MEMm64real` runs that form from the
state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDC_run_of_r0_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DC ip context 0xDC).run s =
      (X86.Instructions.FADD_MEMm64real (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
          (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDC).run t := by
  unfold Decode_Legacy_0_Opcode_DC
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDC_run_of_r0_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 1` in 64-bit mode, opcode DC's form selection picks form
5, `FMUL_ST0_MEMm64real`. -/
theorem selectLegacy0OpcodeDC_run_of_r1_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_DC context true a b c d e f modrm = .ok 5 := by
  simp [Select_Legacy_0_Opcode_DC, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DC decoder on a memory ModRM byte selecting `FMUL_ST0_MEMm64real` runs that form from
the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDC_run_of_r1_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DC ip context 0xDC).run s =
      (X86.Instructions.FMUL_ST0_MEMm64real (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
          (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDC).run t := by
  unfold Decode_Legacy_0_Opcode_DC
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDC_run_of_r1_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 2` in 64-bit mode, opcode DC's form selection picks form
7, `FCOM_ST0_MEMm64real`. -/
theorem selectLegacy0OpcodeDC_run_of_r2_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_0_Opcode_DC context true a b c d e f modrm = .ok 7 := by
  simp [Select_Legacy_0_Opcode_DC, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DC decoder on a memory ModRM byte selecting `FCOM_ST0_MEMm64real` runs that form from
the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDC_run_of_r2_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DC ip context 0xDC).run s =
      (X86.Instructions.FCOM_ST0_MEMm64real (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
          (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDC).run t := by
  unfold Decode_Legacy_0_Opcode_DC
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDC_run_of_r2_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 3` in 64-bit mode, opcode DC's form selection picks form
8, `FCOMP_ST0_MEMm64real`. -/
theorem selectLegacy0OpcodeDC_run_of_r3_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_0_Opcode_DC context true a b c d e f modrm = .ok 8 := by
  simp [Select_Legacy_0_Opcode_DC, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DC decoder on a memory ModRM byte selecting `FCOMP_ST0_MEMm64real` runs that form
from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDC_run_of_r3_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DC ip context 0xDC).run s =
      (X86.Instructions.FCOMP_ST0_MEMm64real (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
          (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDC).run t := by
  unfold Decode_Legacy_0_Opcode_DC
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDC_run_of_r3_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 4` in 64-bit mode, opcode DC's form selection picks form
3, `FSUB_ST0_MEMm64real`. -/
theorem selectLegacy0OpcodeDC_run_of_r4_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_0_Opcode_DC context true a b c d e f modrm = .ok 3 := by
  simp [Select_Legacy_0_Opcode_DC, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DC decoder on a memory ModRM byte selecting `FSUB_ST0_MEMm64real` runs that form from
the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDC_run_of_r4_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DC ip context 0xDC).run s =
      (X86.Instructions.FSUB_ST0_MEMm64real (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
          (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDC).run t := by
  unfold Decode_Legacy_0_Opcode_DC
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDC_run_of_r4_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 5` in 64-bit mode, opcode DC's form selection picks form
11, `FSUBR_ST0_MEMm64real`. -/
theorem selectLegacy0OpcodeDC_run_of_r5_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_0_Opcode_DC context true a b c d e f modrm = .ok 11 := by
  simp [Select_Legacy_0_Opcode_DC, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DC decoder on a memory ModRM byte selecting `FSUBR_ST0_MEMm64real` runs that form
from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDC_run_of_r5_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DC ip context 0xDC).run s =
      (X86.Instructions.FSUBR_ST0_MEMm64real (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
          (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDC).run t := by
  unfold Decode_Legacy_0_Opcode_DC
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDC_run_of_r5_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 6` in 64-bit mode, opcode DC's form selection picks form
13, `FDIV_ST0_MEMm64real`. -/
theorem selectLegacy0OpcodeDC_run_of_r6_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_0_Opcode_DC context true a b c d e f modrm = .ok 13 := by
  simp [Select_Legacy_0_Opcode_DC, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DC decoder on a memory ModRM byte selecting `FDIV_ST0_MEMm64real` runs that form from
the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDC_run_of_r6_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DC ip context 0xDC).run s =
      (X86.Instructions.FDIV_ST0_MEMm64real (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
          (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDC).run t := by
  unfold Decode_Legacy_0_Opcode_DC
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDC_run_of_r6_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 7` in 64-bit mode, opcode DC's form selection picks form
15, `FDIVR_ST0_MEMm64real`. -/
theorem selectLegacy0OpcodeDC_run_of_r7_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_0_Opcode_DC context true a b c d e f modrm = .ok 15 := by
  simp [Select_Legacy_0_Opcode_DC, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DC decoder on a memory ModRM byte selecting `FDIVR_ST0_MEMm64real` runs that form
from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDC_run_of_r7_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DC ip context 0xDC).run s =
      (X86.Instructions.FDIVR_ST0_MEMm64real (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
          (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDC).run t := by
  unfold Decode_Legacy_0_Opcode_DC
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDC_run_of_r7_memory context a b c d e f modrm hmod
        hreg)

end X86Proofs
