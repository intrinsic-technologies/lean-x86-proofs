import X86Proofs.Step.Decode

/-!
# Opcode `DE`: x87 `m16int` arithmetic and the popping register arithmetic (FADDP, …), FCOMPP

The one place that looks inside lean-x86's opcode-`DE` decoder (`Decode_Legacy_0_Opcode_DE`) and
its form selection (`Select_Legacy_0_Opcode_DE`), architecture rule 5. The decoder may diverge
(`PartialSpecM`) and passes the opcode byte to the x87 forms (for FOP). For each register form
(`mod = 3`) the library uses, a `selectLegacy0OpcodeDE_run_of_r<reg>[_rm<rm>]_register` lemma gives
the form the selection picks, and a `decodeLegacy0OpcodeDE_run_of_…` lemma runs the decoder (from
the ModRM fetch at `ip + 1`) to the call of that form at `ip + 2` (`decode_modrm_form_partial`).
Register forms with an ST(i) operand are chosen by `mod` and `reg`; the others also by `rm`.
Memory forms (`mod ≠ 3`) are chosen by `reg` alone: `selectLegacy0OpcodeDE_run_of_r<reg>_memory`
and `decodeLegacy0OpcodeDE_run_of_r<reg>_memory`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3`, `reg = 0` in 64-bit mode, opcode DE's form selection picks form
2, `FADDP_X87_ST0`. -/
theorem selectLegacy0OpcodeDE_run_of_r0_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_DE context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_DE, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DE decoder on a ModRM byte selecting `FADDP_X87_ST0` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDE_run_of_r0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DE ip context 0xDE).run s =
      some ((X86.Instructions.FADDP_X87_ST0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDE).run t) := by
  unfold Decode_Legacy_0_Opcode_DE
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDE_run_of_r0_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 5` in 64-bit mode, opcode DE's form selection picks form
4, `FSUBP_X87_ST0`. -/
theorem selectLegacy0OpcodeDE_run_of_r5_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_0_Opcode_DE context true a b c d e f modrm = .ok 4 := by
  simp [Select_Legacy_0_Opcode_DE, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DE decoder on a ModRM byte selecting `FSUBP_X87_ST0` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDE_run_of_r5_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DE ip context 0xDE).run s =
      some ((X86.Instructions.FSUBP_X87_ST0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDE).run t) := by
  unfold Decode_Legacy_0_Opcode_DE
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDE_run_of_r5_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 1` in 64-bit mode, opcode DE's form selection picks form
6, `FMULP_X87_ST0`. -/
theorem selectLegacy0OpcodeDE_run_of_r1_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_DE context true a b c d e f modrm = .ok 6 := by
  simp [Select_Legacy_0_Opcode_DE, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DE decoder on a ModRM byte selecting `FMULP_X87_ST0` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDE_run_of_r1_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DE ip context 0xDE).run s =
      some ((X86.Instructions.FMULP_X87_ST0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDE).run t) := by
  unfold Decode_Legacy_0_Opcode_DE
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDE_run_of_r1_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 3`, `rm = 1` in 64-bit mode, opcode DE's form selection picks form
7, `FCOMPP`. -/
theorem selectLegacy0OpcodeDE_run_of_r3_rm1_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3) (hrm : modrm.extractLsb' 0 3 = 1#3) :
    Select_Legacy_0_Opcode_DE context true a b c d e f modrm = .ok 7 := by
  simp [Select_Legacy_0_Opcode_DE, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DE decoder on a ModRM byte selecting `FCOMPP` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDE_run_of_r3_rm1_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3) (hrm : modrm.extractLsb' 0 3 = 1#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DE ip context 0xDE).run s =
      some ((X86.Instructions.FCOMPP (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDE).run t) := by
  unfold Decode_Legacy_0_Opcode_DE
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDE_run_of_r3_rm1_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 2` in 64-bit mode, opcode DE's form selection picks form
8, `FCOMP_ST0_X87_DED0`. -/
theorem selectLegacy0OpcodeDE_run_of_r2_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_0_Opcode_DE context true a b c d e f modrm = .ok 8 := by
  simp [Select_Legacy_0_Opcode_DE, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DE decoder on a ModRM byte selecting `FCOMP_ST0_X87_DED0` runs that form from the
state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDE_run_of_r2_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DE ip context 0xDE).run s =
      some
          ((X86.Instructions.FCOMP_ST0_X87_DED0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDE).run t) := by
  unfold Decode_Legacy_0_Opcode_DE
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDE_run_of_r2_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 4` in 64-bit mode, opcode DE's form selection picks form
12, `FSUBRP_X87_ST0`. -/
theorem selectLegacy0OpcodeDE_run_of_r4_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_0_Opcode_DE context true a b c d e f modrm = .ok 12 := by
  simp [Select_Legacy_0_Opcode_DE, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DE decoder on a ModRM byte selecting `FSUBRP_X87_ST0` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDE_run_of_r4_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DE ip context 0xDE).run s =
      some ((X86.Instructions.FSUBRP_X87_ST0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDE).run t) := by
  unfold Decode_Legacy_0_Opcode_DE
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDE_run_of_r4_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 7` in 64-bit mode, opcode DE's form selection picks form
14, `FDIVP_X87_ST0`. -/
theorem selectLegacy0OpcodeDE_run_of_r7_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_0_Opcode_DE context true a b c d e f modrm = .ok 14 := by
  simp [Select_Legacy_0_Opcode_DE, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DE decoder on a ModRM byte selecting `FDIVP_X87_ST0` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDE_run_of_r7_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DE ip context 0xDE).run s =
      some ((X86.Instructions.FDIVP_X87_ST0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDE).run t) := by
  unfold Decode_Legacy_0_Opcode_DE
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDE_run_of_r7_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 6` in 64-bit mode, opcode DE's form selection picks form
16, `FDIVRP_X87_ST0`. -/
theorem selectLegacy0OpcodeDE_run_of_r6_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_0_Opcode_DE context true a b c d e f modrm = .ok 16 := by
  simp [Select_Legacy_0_Opcode_DE, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DE decoder on a ModRM byte selecting `FDIVRP_X87_ST0` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDE_run_of_r6_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DE ip context 0xDE).run s =
      some ((X86.Instructions.FDIVRP_X87_ST0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDE).run t) := by
  unfold Decode_Legacy_0_Opcode_DE
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDE_run_of_r6_register context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 0` in 64-bit mode, opcode DE's form selection picks form
1, `FIADD_ST0_MEMmem16int`. -/
theorem selectLegacy0OpcodeDE_run_of_r0_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_DE context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_DE, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DE decoder on a memory ModRM byte selecting `FIADD_ST0_MEMmem16int` runs that form
from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDE_run_of_r0_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DE ip context 0xDE).run s =
      (X86.Instructions.FIADD_ST0_MEMmem16int (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
          (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDE).run t := by
  unfold Decode_Legacy_0_Opcode_DE
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDE_run_of_r0_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 1` in 64-bit mode, opcode DE's form selection picks form
5, `FIMUL_ST0_MEMmem16int`. -/
theorem selectLegacy0OpcodeDE_run_of_r1_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_DE context true a b c d e f modrm = .ok 5 := by
  simp [Select_Legacy_0_Opcode_DE, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DE decoder on a memory ModRM byte selecting `FIMUL_ST0_MEMmem16int` runs that form
from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDE_run_of_r1_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DE ip context 0xDE).run s =
      (X86.Instructions.FIMUL_ST0_MEMmem16int (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
          (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDE).run t := by
  unfold Decode_Legacy_0_Opcode_DE
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDE_run_of_r1_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 2` in 64-bit mode, opcode DE's form selection picks form
9, `FICOM_ST0_MEMmem16int`. -/
theorem selectLegacy0OpcodeDE_run_of_r2_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_0_Opcode_DE context true a b c d e f modrm = .ok 9 := by
  simp [Select_Legacy_0_Opcode_DE, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DE decoder on a memory ModRM byte selecting `FICOM_ST0_MEMmem16int` runs that form
from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDE_run_of_r2_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DE ip context 0xDE).run s =
      (X86.Instructions.FICOM_ST0_MEMmem16int (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
          (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDE).run t := by
  unfold Decode_Legacy_0_Opcode_DE
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDE_run_of_r2_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 3` in 64-bit mode, opcode DE's form selection picks form
10, `FICOMP_ST0_MEMmem16int`. -/
theorem selectLegacy0OpcodeDE_run_of_r3_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_0_Opcode_DE context true a b c d e f modrm = .ok 10 := by
  simp [Select_Legacy_0_Opcode_DE, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DE decoder on a memory ModRM byte selecting `FICOMP_ST0_MEMmem16int` runs that form
from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDE_run_of_r3_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DE ip context 0xDE).run s =
      (X86.Instructions.FICOMP_ST0_MEMmem16int (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
          (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDE).run t := by
  unfold Decode_Legacy_0_Opcode_DE
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDE_run_of_r3_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 4` in 64-bit mode, opcode DE's form selection picks form
3, `FISUB_ST0_MEMmem16int`. -/
theorem selectLegacy0OpcodeDE_run_of_r4_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_0_Opcode_DE context true a b c d e f modrm = .ok 3 := by
  simp [Select_Legacy_0_Opcode_DE, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DE decoder on a memory ModRM byte selecting `FISUB_ST0_MEMmem16int` runs that form
from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDE_run_of_r4_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DE ip context 0xDE).run s =
      (X86.Instructions.FISUB_ST0_MEMmem16int (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
          (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDE).run t := by
  unfold Decode_Legacy_0_Opcode_DE
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDE_run_of_r4_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 5` in 64-bit mode, opcode DE's form selection picks form
11, `FISUBR_ST0_MEMmem16int`. -/
theorem selectLegacy0OpcodeDE_run_of_r5_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_0_Opcode_DE context true a b c d e f modrm = .ok 11 := by
  simp [Select_Legacy_0_Opcode_DE, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DE decoder on a memory ModRM byte selecting `FISUBR_ST0_MEMmem16int` runs that form
from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDE_run_of_r5_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DE ip context 0xDE).run s =
      (X86.Instructions.FISUBR_ST0_MEMmem16int (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
          (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDE).run t := by
  unfold Decode_Legacy_0_Opcode_DE
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDE_run_of_r5_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 6` in 64-bit mode, opcode DE's form selection picks form
13, `FIDIV_ST0_MEMmem16int`. -/
theorem selectLegacy0OpcodeDE_run_of_r6_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_0_Opcode_DE context true a b c d e f modrm = .ok 13 := by
  simp [Select_Legacy_0_Opcode_DE, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DE decoder on a memory ModRM byte selecting `FIDIV_ST0_MEMmem16int` runs that form
from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDE_run_of_r6_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DE ip context 0xDE).run s =
      (X86.Instructions.FIDIV_ST0_MEMmem16int (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
          (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDE).run t := by
  unfold Decode_Legacy_0_Opcode_DE
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDE_run_of_r6_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 7` in 64-bit mode, opcode DE's form selection picks form
15, `FIDIVR_ST0_MEMmem16int`. -/
theorem selectLegacy0OpcodeDE_run_of_r7_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_0_Opcode_DE context true a b c d e f modrm = .ok 15 := by
  simp [Select_Legacy_0_Opcode_DE, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-DE decoder on a memory ModRM byte selecting `FIDIVR_ST0_MEMmem16int` runs that form
from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeDE_run_of_r7_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_DE ip context 0xDE).run s =
      (X86.Instructions.FIDIVR_ST0_MEMmem16int (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
          (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xDE).run t := by
  unfold Decode_Legacy_0_Opcode_DE
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeDE_run_of_r7_memory context a b c d e f modrm hmod
        hreg)

end X86Proofs
