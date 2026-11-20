import X86Proofs.Step.Decode

/-!
# Opcode `D9`: x87 loads, constants, control and the one-operand operations

The one place that looks inside lean-x86's opcode-`D9` decoder (`Decode_Legacy_0_Opcode_D9`) and
its form selection (`Select_Legacy_0_Opcode_D9`), architecture rule 5. The decoder may diverge
(`PartialSpecM`) and passes the opcode byte to the x87 forms (for FOP). For each register form
(`mod = 3`) the library uses, a `selectLegacy0OpcodeD9_run_of_r<reg>[_rm<rm>]_register` lemma gives
the form the selection picks, and a `decodeLegacy0OpcodeD9_run_of_…` lemma runs the decoder (from
the ModRM fetch at `ip + 1`) to the call of that form at `ip + 2` (`decode_modrm_form_partial`).
Register forms with an ST(i) operand are chosen by `mod` and `reg`; the others also by `rm`.
Memory forms (`mod ≠ 3`) are chosen by `reg` alone: `selectLegacy0OpcodeD9_run_of_r<reg>_memory`
and `decodeLegacy0OpcodeD9_run_of_r<reg>_memory`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3`, `reg = 6`, `rm = 0` in 64-bit mode, opcode D9's form selection picks form
1, `F2XM1`. -/
theorem selectLegacy0OpcodeD9_run_of_r6_rm0_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hrm : modrm.extractLsb' 0 3 = 0#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `F2XM1` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r6_rm0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hrm : modrm.extractLsb' 0 3 = 0#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      (X86.Instructions.F2XM1 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r6_rm0_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 7`, `rm = 6` in 64-bit mode, opcode D9's form selection picks form
2, `FSIN`. -/
theorem selectLegacy0OpcodeD9_run_of_r7_rm6_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hrm : modrm.extractLsb' 0 3 = 6#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FSIN` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r7_rm6_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hrm : modrm.extractLsb' 0 3 = 6#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      (X86.Instructions.FSIN (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r7_rm6_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 7`, `rm = 7` in 64-bit mode, opcode D9's form selection picks form
3, `FCOS`. -/
theorem selectLegacy0OpcodeD9_run_of_r7_rm7_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hrm : modrm.extractLsb' 0 3 = 7#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 3 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FCOS` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r7_rm7_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hrm : modrm.extractLsb' 0 3 = 7#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      (X86.Instructions.FCOS (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r7_rm7_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 6`, `rm = 2` in 64-bit mode, opcode D9's form selection picks form
4, `FPTAN`. -/
theorem selectLegacy0OpcodeD9_run_of_r6_rm2_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hrm : modrm.extractLsb' 0 3 = 2#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 4 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FPTAN` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r6_rm2_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hrm : modrm.extractLsb' 0 3 = 2#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      (X86.Instructions.FPTAN (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r6_rm2_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 7`, `rm = 3` in 64-bit mode, opcode D9's form selection picks form
5, `FSINCOS`. -/
theorem selectLegacy0OpcodeD9_run_of_r7_rm3_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hrm : modrm.extractLsb' 0 3 = 3#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 5 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FSINCOS` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r7_rm3_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hrm : modrm.extractLsb' 0 3 = 3#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      (X86.Instructions.FSINCOS (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r7_rm3_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 6`, `rm = 3` in 64-bit mode, opcode D9's form selection picks form
6, `FPATAN`. -/
theorem selectLegacy0OpcodeD9_run_of_r6_rm3_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hrm : modrm.extractLsb' 0 3 = 3#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 6 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FPATAN` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r6_rm3_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hrm : modrm.extractLsb' 0 3 = 3#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      (X86.Instructions.FPATAN (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r6_rm3_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 6`, `rm = 1` in 64-bit mode, opcode D9's form selection picks form
7, `FYL2X`. -/
theorem selectLegacy0OpcodeD9_run_of_r6_rm1_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hrm : modrm.extractLsb' 0 3 = 1#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 7 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FYL2X` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r6_rm1_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hrm : modrm.extractLsb' 0 3 = 1#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      (X86.Instructions.FYL2X (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r6_rm1_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 7`, `rm = 1` in 64-bit mode, opcode D9's form selection picks form
8, `FYL2XP1`. -/
theorem selectLegacy0OpcodeD9_run_of_r7_rm1_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hrm : modrm.extractLsb' 0 3 = 1#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 8 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FYL2XP1` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r7_rm1_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hrm : modrm.extractLsb' 0 3 = 1#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      (X86.Instructions.FYL2XP1 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r7_rm1_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 3` in 64-bit mode, opcode D9's form selection picks form
14, `FSTPNCE_X87_ST0`. -/
theorem selectLegacy0OpcodeD9_run_of_r3_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 14 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FSTPNCE_X87_ST0` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r3_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some ((X86.Instructions.FSTPNCE_X87_ST0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r3_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 0` in 64-bit mode, opcode D9's form selection picks form
16, `FLD_ST0_X87`. -/
theorem selectLegacy0OpcodeD9_run_of_r0_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 16 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FLD_ST0_X87` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some ((X86.Instructions.FLD_ST0_X87 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r0_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 4`, `rm = 0` in 64-bit mode, opcode D9's form selection picks form
26, `FCHS`. -/
theorem selectLegacy0OpcodeD9_run_of_r4_rm0_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hrm : modrm.extractLsb' 0 3 = 0#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 26 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FCHS` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r4_rm0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hrm : modrm.extractLsb' 0 3 = 0#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some ((X86.Instructions.FCHS (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r4_rm0_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 1` in 64-bit mode, opcode D9's form selection picks form
27, `FXCH_ST0_X87`. -/
theorem selectLegacy0OpcodeD9_run_of_r1_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 27 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FXCH_ST0_X87` runs that form from the state
after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r1_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some ((X86.Instructions.FXCH_ST0_X87 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r1_register context a b c d e f modrm hmod
        hreg)

/-- With `mod = 3`, `reg = 4`, `rm = 1` in 64-bit mode, opcode D9's form selection picks form
28, `FABS`. -/
theorem selectLegacy0OpcodeD9_run_of_r4_rm1_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hrm : modrm.extractLsb' 0 3 = 1#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 28 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FABS` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r4_rm1_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hrm : modrm.extractLsb' 0 3 = 1#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some ((X86.Instructions.FABS (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r4_rm1_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 6`, `rm = 6` in 64-bit mode, opcode D9's form selection picks form
29, `FDECSTP`. -/
theorem selectLegacy0OpcodeD9_run_of_r6_rm6_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hrm : modrm.extractLsb' 0 3 = 6#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 29 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FDECSTP` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r6_rm6_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hrm : modrm.extractLsb' 0 3 = 6#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some ((X86.Instructions.FDECSTP (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r6_rm6_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 6`, `rm = 7` in 64-bit mode, opcode D9's form selection picks form
30, `FINCSTP`. -/
theorem selectLegacy0OpcodeD9_run_of_r6_rm7_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hrm : modrm.extractLsb' 0 3 = 7#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 30 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FINCSTP` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r6_rm7_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hrm : modrm.extractLsb' 0 3 = 7#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some ((X86.Instructions.FINCSTP (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r6_rm7_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 2`, `rm = 0` in 64-bit mode, opcode D9's form selection picks form
31, `FNOP`. -/
theorem selectLegacy0OpcodeD9_run_of_r2_rm0_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) (hrm : modrm.extractLsb' 0 3 = 0#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 31 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FNOP` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r2_rm0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) (hrm : modrm.extractLsb' 0 3 = 0#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some ((X86.Instructions.FNOP (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r2_rm0_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 4`, `rm = 4` in 64-bit mode, opcode D9's form selection picks form
32, `FTST`. -/
theorem selectLegacy0OpcodeD9_run_of_r4_rm4_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hrm : modrm.extractLsb' 0 3 = 4#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 32 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FTST` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r4_rm4_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hrm : modrm.extractLsb' 0 3 = 4#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some ((X86.Instructions.FTST (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r4_rm4_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 4`, `rm = 5` in 64-bit mode, opcode D9's form selection picks form
33, `FXAM`. -/
theorem selectLegacy0OpcodeD9_run_of_r4_rm5_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hrm : modrm.extractLsb' 0 3 = 5#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 33 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FXAM` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r4_rm5_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hrm : modrm.extractLsb' 0 3 = 5#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some ((X86.Instructions.FXAM (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r4_rm5_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 7`, `rm = 4` in 64-bit mode, opcode D9's form selection picks form
34, `FRNDINT`. -/
theorem selectLegacy0OpcodeD9_run_of_r7_rm4_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hrm : modrm.extractLsb' 0 3 = 4#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 34 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FRNDINT` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r7_rm4_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hrm : modrm.extractLsb' 0 3 = 4#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some ((X86.Instructions.FRNDINT (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r7_rm4_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 7`, `rm = 5` in 64-bit mode, opcode D9's form selection picks form
35, `FSCALE`. -/
theorem selectLegacy0OpcodeD9_run_of_r7_rm5_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hrm : modrm.extractLsb' 0 3 = 5#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 35 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FSCALE` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r7_rm5_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hrm : modrm.extractLsb' 0 3 = 5#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some ((X86.Instructions.FSCALE (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r7_rm5_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 6`, `rm = 4` in 64-bit mode, opcode D9's form selection picks form
36, `FXTRACT`. -/
theorem selectLegacy0OpcodeD9_run_of_r6_rm4_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hrm : modrm.extractLsb' 0 3 = 4#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 36 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FXTRACT` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r6_rm4_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hrm : modrm.extractLsb' 0 3 = 4#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      (X86.Instructions.FXTRACT (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r6_rm4_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 7`, `rm = 2` in 64-bit mode, opcode D9's form selection picks form
40, `FSQRT`. -/
theorem selectLegacy0OpcodeD9_run_of_r7_rm2_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hrm : modrm.extractLsb' 0 3 = 2#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 40 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FSQRT` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r7_rm2_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hrm : modrm.extractLsb' 0 3 = 2#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some ((X86.Instructions.FSQRT (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r7_rm2_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 7`, `rm = 0` in 64-bit mode, opcode D9's form selection picks form
41, `FPREM`. -/
theorem selectLegacy0OpcodeD9_run_of_r7_rm0_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hrm : modrm.extractLsb' 0 3 = 0#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 41 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FPREM` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r7_rm0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hrm : modrm.extractLsb' 0 3 = 0#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some ((X86.Instructions.FPREM (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r7_rm0_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 6`, `rm = 5` in 64-bit mode, opcode D9's form selection picks form
42, `FPREM1`. -/
theorem selectLegacy0OpcodeD9_run_of_r6_rm5_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hrm : modrm.extractLsb' 0 3 = 5#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 42 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FPREM1` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r6_rm5_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3) (hrm : modrm.extractLsb' 0 3 = 5#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some ((X86.Instructions.FPREM1 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r6_rm5_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 5`, `rm = 1` in 64-bit mode, opcode D9's form selection picks form
18, `FLDL2T`. -/
theorem selectLegacy0OpcodeD9_run_of_r5_rm1_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hrm : modrm.extractLsb' 0 3 = 1#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 18 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FLDL2T` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r5_rm1_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hrm : modrm.extractLsb' 0 3 = 1#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some ((X86.Instructions.FLDL2T (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r5_rm1_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 5`, `rm = 2` in 64-bit mode, opcode D9's form selection picks form
19, `FLDL2E`. -/
theorem selectLegacy0OpcodeD9_run_of_r5_rm2_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hrm : modrm.extractLsb' 0 3 = 2#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 19 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FLDL2E` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r5_rm2_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hrm : modrm.extractLsb' 0 3 = 2#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some ((X86.Instructions.FLDL2E (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r5_rm2_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 5`, `rm = 3` in 64-bit mode, opcode D9's form selection picks form
20, `FLDPI`. -/
theorem selectLegacy0OpcodeD9_run_of_r5_rm3_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hrm : modrm.extractLsb' 0 3 = 3#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 20 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FLDPI` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r5_rm3_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hrm : modrm.extractLsb' 0 3 = 3#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some ((X86.Instructions.FLDPI (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r5_rm3_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 5`, `rm = 4` in 64-bit mode, opcode D9's form selection picks form
21, `FLDLG2`. -/
theorem selectLegacy0OpcodeD9_run_of_r5_rm4_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hrm : modrm.extractLsb' 0 3 = 4#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 21 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FLDLG2` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r5_rm4_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hrm : modrm.extractLsb' 0 3 = 4#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some ((X86.Instructions.FLDLG2 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r5_rm4_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 5`, `rm = 5` in 64-bit mode, opcode D9's form selection picks form
22, `FLDLN2`. -/
theorem selectLegacy0OpcodeD9_run_of_r5_rm5_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hrm : modrm.extractLsb' 0 3 = 5#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 22 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FLDLN2` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r5_rm5_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hrm : modrm.extractLsb' 0 3 = 5#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some ((X86.Instructions.FLDLN2 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r5_rm5_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 5`, `rm = 0` in 64-bit mode, opcode D9's form selection picks form
17, `FLD1`. -/
theorem selectLegacy0OpcodeD9_run_of_r5_rm0_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hrm : modrm.extractLsb' 0 3 = 0#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 17 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FLD1` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r5_rm0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hrm : modrm.extractLsb' 0 3 = 0#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some ((X86.Instructions.FLD1 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r5_rm0_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod = 3`, `reg = 5`, `rm = 6` in 64-bit mode, opcode D9's form selection picks form
23, `FLDZ`. -/
theorem selectLegacy0OpcodeD9_run_of_r5_rm6_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hrm : modrm.extractLsb' 0 3 = 6#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 23 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, hrm, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a ModRM byte selecting `FLDZ` runs that form from the state after
the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r5_rm6_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) (hrm : modrm.extractLsb' 0 3 = 6#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some ((X86.Instructions.FLDZ (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r5_rm6_register context a b c d e f modrm hmod
        hreg hrm)

/-- With `mod ≠ 3`, `reg = 0` in 64-bit mode, opcode D9's form selection picks form
15, `FLD_ST0_MEMmem32real`. -/
theorem selectLegacy0OpcodeD9_run_of_r0_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 15 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a memory ModRM byte selecting `FLD_ST0_MEMmem32real` runs that form
from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r0_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      (X86.Instructions.FLD_ST0_MEMmem32real (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
          (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r0_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 2` in 64-bit mode, opcode D9's form selection picks form
12, `FST_MEMmem32real_ST0`. -/
theorem selectLegacy0OpcodeD9_run_of_r2_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 12 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a memory ModRM byte selecting `FST_MEMmem32real_ST0` runs that form
from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r2_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some
          ((X86.Instructions.FST_MEMmem32real_ST0 (BitVec.add ip 2#64) context
          (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r2_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 3` in 64-bit mode, opcode D9's form selection picks form
13, `FSTP_MEMmem32real_ST0`. -/
theorem selectLegacy0OpcodeD9_run_of_r3_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 13 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a memory ModRM byte selecting `FSTP_MEMmem32real_ST0` runs that form
from the state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r3_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some
          ((X86.Instructions.FSTP_MEMmem32real_ST0 (BitVec.add ip 2#64) context
          (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0xD9).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r3_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 5` in 64-bit mode, opcode D9's form selection picks form
24, `FLDCW_MEMmem16`. -/
theorem selectLegacy0OpcodeD9_run_of_r5_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 24 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a memory ModRM byte selecting `FLDCW_MEMmem16` runs that form from the
state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r5_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some
          ((X86.Instructions.FLDCW_MEMmem16 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
          (modrm.extractLsb' 0 3)).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r5_memory context a b c d e f modrm hmod
        hreg)

/-- With `mod ≠ 3`, `reg = 7` in 64-bit mode, opcode D9's form selection picks form
25, `FNSTCW_MEMmem16`. -/
theorem selectLegacy0OpcodeD9_run_of_r7_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_0_Opcode_D9 context true a b c d e f modrm = .ok 25 := by
  simp [Select_Legacy_0_Opcode_D9, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-D9 decoder on a memory ModRM byte selecting `FNSTCW_MEMmem16` runs that form from the
state after the ModRM fetch, at `ip + 2`. -/
theorem decodeLegacy0OpcodeD9_run_of_r7_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run s =
      some
          ((X86.Instructions.FNSTCW_MEMmem16 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
          (modrm.extractLsb' 0 3)).run t) := by
  unfold Decode_Legacy_0_Opcode_D9
  decode_modrm_form_partial s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeD9_run_of_r7_memory context a b c d e f modrm hmod
        hreg)

end X86Proofs
