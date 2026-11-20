import X86Proofs.Step.Decode

/-!
# Opcode `DF`: x87 `m16int`/`m64int` loads and stores, FFREEP, FNSTSW AX, FUCOMIP, FCOMIP

The one place that looks inside lean-x86's opcode-`DF` decoder (`Decode_Legacy_0_Opcode_DF`) and
its form selection (`Select_Legacy_0_Opcode_DF`), architecture rule 5. The decoder may diverge
(`PartialSpecM`) and passes the opcode byte to the x87 forms (for FOP). For each register form
(`mod = 3`) the library uses, a `selectLegacy0OpcodeDF_run_of_r<reg>[_rm<rm>]_register` lemma gives
the form the selection picks, and a `decodeLegacy0OpcodeDF_run_of_…` lemma runs the decoder (from
the ModRM fetch at `ip + 1`) to the call of that form at `ip + 2` (`decode_modrm_form_partial`).
Register forms with an ST(i) operand are chosen by `mod` and `reg`; the others also by `rm`.
Memory forms (`mod ≠ 3`) are chosen by `reg` alone: `selectLegacy0OpcodeDF_run_of_r<reg>_memory`
and `decodeLegacy0OpcodeDF_run_of_r<reg>_memory`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3`, `reg = 5` in 64-bit mode, opcode DF's form selection picks form
3, `FUCOMIP_ST0_X87`. -/
theorem selectLegacy0OpcodeDF_run_of_r5_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_0_Opcode_DF context true a b c d e f modrm = .ok 3 := by
  simp [Select_Legacy_0_Opcode_DF, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DF decoder on a ModRM byte selecting `FUCOMIP_ST0_X87` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDF_run_of_r5_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DF ip context 0xDF).run s =
      some ((X86.Instructions.FUCOMIP_ST0_X87 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDF).run t) := by
  unfold Decode_Legacy_0_Opcode_DF
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDF_run_of_r5_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 6` in 64-bit mode, opcode DF's form selection picks form
4, `FCOMIP_ST0_X87`. -/
theorem selectLegacy0OpcodeDF_run_of_r6_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_0_Opcode_DF context true a b c d e f modrm = .ok 4 := by
  simp [Select_Legacy_0_Opcode_DF, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DF decoder on a ModRM byte selecting `FCOMIP_ST0_X87` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDF_run_of_r6_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DF ip context 0xDF).run s =
      some ((X86.Instructions.FCOMIP_ST0_X87 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDF).run t) := by
  unfold Decode_Legacy_0_Opcode_DF
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDF_run_of_r6_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 2` in 64-bit mode, opcode DF's form selection picks form
8, `FSTP_X87_ST0_DFD0`. -/
theorem selectLegacy0OpcodeDF_run_of_r2_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_0_Opcode_DF context true a b c d e f modrm = .ok 8 := by
  simp [Select_Legacy_0_Opcode_DF, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DF decoder on a ModRM byte selecting `FSTP_X87_ST0_DFD0` runs that form from the
state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDF_run_of_r2_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DF ip context 0xDF).run s =
      some ((X86.Instructions.FSTP_X87_ST0_DFD0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDF).run t) := by
  unfold Decode_Legacy_0_Opcode_DF
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDF_run_of_r2_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 3` in 64-bit mode, opcode DF's form selection picks form
9, `FSTP_X87_ST0_DFD1`. -/
theorem selectLegacy0OpcodeDF_run_of_r3_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_0_Opcode_DF context true a b c d e f modrm = .ok 9 := by
  simp [Select_Legacy_0_Opcode_DF, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DF decoder on a ModRM byte selecting `FSTP_X87_ST0_DFD1` runs that form from the
state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDF_run_of_r3_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DF ip context 0xDF).run s =
      some ((X86.Instructions.FSTP_X87_ST0_DFD1 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDF).run t) := by
  unfold Decode_Legacy_0_Opcode_DF
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDF_run_of_r3_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 1` in 64-bit mode, opcode DF's form selection picks form
12, `FXCH_ST0_X87_DFC1`. -/
theorem selectLegacy0OpcodeDF_run_of_r1_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_DF context true a b c d e f modrm = .ok 12 := by
  simp [Select_Legacy_0_Opcode_DF, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DF decoder on a ModRM byte selecting `FXCH_ST0_X87_DFC1` runs that form from the
state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDF_run_of_r1_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DF ip context 0xDF).run s =
      some ((X86.Instructions.FXCH_ST0_X87_DFC1 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDF).run t) := by
  unfold Decode_Legacy_0_Opcode_DF
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDF_run_of_r1_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 0` in 64-bit mode, opcode DF's form selection picks form
13, `FFREEP_X87`. -/
theorem selectLegacy0OpcodeDF_run_of_r0_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_DF context true a b c d e f modrm = .ok 13 := by
  simp [Select_Legacy_0_Opcode_DF, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DF decoder on a ModRM byte selecting `FFREEP_X87` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDF_run_of_r0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DF ip context 0xDF).run s =
      some ((X86.Instructions.FFREEP_X87 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDF).run t) := by
  unfold Decode_Legacy_0_Opcode_DF
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDF_run_of_r0_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 4`, `rm = 0` in 64-bit mode, opcode DF's form selection picks form
14, `FNSTSW_AX`. -/
theorem selectLegacy0OpcodeDF_run_of_r4_rm0_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hrm : modrm.extractLsb' 0 3 = 0#3) :
    Select_Legacy_0_Opcode_DF context true a b c d e f modrm = .ok 14 := by
  simp [Select_Legacy_0_Opcode_DF, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DF decoder on a ModRM byte selecting `FNSTSW_AX` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDF_run_of_r4_rm0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hrm : modrm.extractLsb' 0 3 = 0#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DF ip context 0xDF).run s =
      some ((X86.Instructions.FNSTSW_AX (BitVec.add ip 2#64) context).run t) := by
  unfold Decode_Legacy_0_Opcode_DF
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDF_run_of_r4_rm0_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod ≠ 3`, `reg = 0` in 64-bit mode, opcode DF's form selection picks form
10, `FILD_ST0_MEMmem16int`. -/
theorem selectLegacy0OpcodeDF_run_of_r0_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_DF context true a b c d e f modrm = .ok 10 := by
  simp [Select_Legacy_0_Opcode_DF, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DF decoder on a memory ModRM byte selecting `FILD_ST0_MEMmem16int` runs that form
from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDF_run_of_r0_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DF ip context 0xDF).run s =
      (X86.Instructions.FILD_ST0_MEMmem16int (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
          (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDF).run t := by
  unfold Decode_Legacy_0_Opcode_DF
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDF_run_of_r0_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 2` in 64-bit mode, opcode DF's form selection picks form
5, `FIST_MEMmem16int_ST0`. -/
theorem selectLegacy0OpcodeDF_run_of_r2_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_0_Opcode_DF context true a b c d e f modrm = .ok 5 := by
  simp [Select_Legacy_0_Opcode_DF, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DF decoder on a memory ModRM byte selecting `FIST_MEMmem16int_ST0` runs that form
from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDF_run_of_r2_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DF ip context 0xDF).run s =
      some
          ((X86.Instructions.FIST_MEMmem16int_ST0 (BitVec.add ip 2#64) context
          (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDF).run t) := by
  unfold Decode_Legacy_0_Opcode_DF
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDF_run_of_r2_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 3` in 64-bit mode, opcode DF's form selection picks form
6, `FISTP_MEMmem16int_ST0`. -/
theorem selectLegacy0OpcodeDF_run_of_r3_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_0_Opcode_DF context true a b c d e f modrm = .ok 6 := by
  simp [Select_Legacy_0_Opcode_DF, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DF decoder on a memory ModRM byte selecting `FISTP_MEMmem16int_ST0` runs that form
from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDF_run_of_r3_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DF ip context 0xDF).run s =
      some
          ((X86.Instructions.FISTP_MEMmem16int_ST0 (BitVec.add ip 2#64) context
          (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDF).run t) := by
  unfold Decode_Legacy_0_Opcode_DF
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDF_run_of_r3_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 5` in 64-bit mode, opcode DF's form selection picks form
11, `FILD_ST0_MEMm64int`. -/
theorem selectLegacy0OpcodeDF_run_of_r5_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_0_Opcode_DF context true a b c d e f modrm = .ok 11 := by
  simp [Select_Legacy_0_Opcode_DF, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DF decoder on a memory ModRM byte selecting `FILD_ST0_MEMm64int` runs that form from
the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDF_run_of_r5_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DF ip context 0xDF).run s =
      (X86.Instructions.FILD_ST0_MEMm64int (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
          (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDF).run t := by
  unfold Decode_Legacy_0_Opcode_DF
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDF_run_of_r5_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 7` in 64-bit mode, opcode DF's form selection picks form
7, `FISTP_MEMm64int_ST0`. -/
theorem selectLegacy0OpcodeDF_run_of_r7_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_0_Opcode_DF context true a b c d e f modrm = .ok 7 := by
  simp [Select_Legacy_0_Opcode_DF, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DF decoder on a memory ModRM byte selecting `FISTP_MEMm64int_ST0` runs that form from
the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDF_run_of_r7_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DF ip context 0xDF).run s =
      some
          ((X86.Instructions.FISTP_MEMm64int_ST0 (BitVec.add ip 2#64) context
          (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDF).run t) := by
  unfold Decode_Legacy_0_Opcode_DF
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDF_run_of_r7_memory context a b c d e f modrm hmod
        hreg)

end X86Proofs
