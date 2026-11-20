import X86Proofs.Step.Decode

/-!
# Opcode `0F 18`: group 16 (prefetches and reserved hint NOPs)

The one place that looks inside lean-x86's opcode-`0F 18` decoder (`Decode_Legacy_1_Opcode_18`) and
its form selection (`Select_Legacy_1_Opcode_18`), architecture rule 5. For each ModRM case the
library uses (`mod = 3` with `reg = 0`–`7`, the reserved NOPs `NOP_GPRv_0F18r<k>`, and a memory
operand with `reg = 4`–`7`, `NOP_MEMv_0F18r<k>`; `Instructions/Nop/Generated`), a
`selectLegacy1Opcode18_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy1Opcode18_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`, `ip` the
second opcode byte's address) to the call of that form at `ip + 2`. The memory forms with
`reg = 0`–`3` are the prefetches (`PREFETCHNTA`, `PREFETCHT0`–`T2`), which call the caller's cache
binding and are not covered.

`Decode_Legacy_1`'s dispatch to this decoder is `decodeLegacy1_run_of_opcode18`
(`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` and `reg = 0` in 64-bit mode, opcode `0F 18`'s form selection picks form 5,
`NOP_GPRv_0F18r0`. -/
theorem selectLegacy1Opcode18_run_of_r0_register (context : Instruction_Context)
    (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_1_Opcode_18 context true a b c d e f modrm = .ok 5 := by
  simp [Select_Legacy_1_Opcode_18, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`0F 18` decoder with `mod = 3` and `reg = 0` runs `NOP_GPRv_0F18r0` from the state
`t` after the ModRM fetch (in 64-bit mode, decoder features answered), with `Next_IP` `ip + 2`. -/
theorem decodeLegacy1Opcode18_run_of_r0_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_18 ip context).run s =
      (X86.Instructions.NOP_GPRv_0F18r0 (BitVec.add ip 2#64) context).run t := by
  unfold Decode_Legacy_1_Opcode_18
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1Opcode18_run_of_r0_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 1` in 64-bit mode, opcode `0F 18`'s form selection picks form 6,
`NOP_GPRv_0F18r1`. -/
theorem selectLegacy1Opcode18_run_of_r1_register (context : Instruction_Context)
    (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 1#3) :
    Select_Legacy_1_Opcode_18 context true a b c d e f modrm = .ok 6 := by
  simp [Select_Legacy_1_Opcode_18, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`0F 18` decoder with `mod = 3` and `reg = 1` runs `NOP_GPRv_0F18r1` from the state
`t` after the ModRM fetch (in 64-bit mode, decoder features answered), with `Next_IP` `ip + 2`. -/
theorem decodeLegacy1Opcode18_run_of_r1_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_18 ip context).run s =
      (X86.Instructions.NOP_GPRv_0F18r1 (BitVec.add ip 2#64) context).run t := by
  unfold Decode_Legacy_1_Opcode_18
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1Opcode18_run_of_r1_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 2` in 64-bit mode, opcode `0F 18`'s form selection picks form 7,
`NOP_GPRv_0F18r2`. -/
theorem selectLegacy1Opcode18_run_of_r2_register (context : Instruction_Context)
    (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 2#3) :
    Select_Legacy_1_Opcode_18 context true a b c d e f modrm = .ok 7 := by
  simp [Select_Legacy_1_Opcode_18, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`0F 18` decoder with `mod = 3` and `reg = 2` runs `NOP_GPRv_0F18r2` from the state
`t` after the ModRM fetch (in 64-bit mode, decoder features answered), with `Next_IP` `ip + 2`. -/
theorem decodeLegacy1Opcode18_run_of_r2_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 2#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_18 ip context).run s =
      (X86.Instructions.NOP_GPRv_0F18r2 (BitVec.add ip 2#64) context).run t := by
  unfold Decode_Legacy_1_Opcode_18
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1Opcode18_run_of_r2_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 3` in 64-bit mode, opcode `0F 18`'s form selection picks form 8,
`NOP_GPRv_0F18r3`. -/
theorem selectLegacy1Opcode18_run_of_r3_register (context : Instruction_Context)
    (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_1_Opcode_18 context true a b c d e f modrm = .ok 8 := by
  simp [Select_Legacy_1_Opcode_18, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`0F 18` decoder with `mod = 3` and `reg = 3` runs `NOP_GPRv_0F18r3` from the state
`t` after the ModRM fetch (in 64-bit mode, decoder features answered), with `Next_IP` `ip + 2`. -/
theorem decodeLegacy1Opcode18_run_of_r3_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_18 ip context).run s =
      (X86.Instructions.NOP_GPRv_0F18r3 (BitVec.add ip 2#64) context).run t := by
  unfold Decode_Legacy_1_Opcode_18
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1Opcode18_run_of_r3_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 4` in 64-bit mode, opcode `0F 18`'s form selection picks form 9,
`NOP_GPRv_0F18r4`. -/
theorem selectLegacy1Opcode18_run_of_r4_register (context : Instruction_Context)
    (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_1_Opcode_18 context true a b c d e f modrm = .ok 9 := by
  simp [Select_Legacy_1_Opcode_18, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`0F 18` decoder with `mod = 3` and `reg = 4` runs `NOP_GPRv_0F18r4` from the state
`t` after the ModRM fetch (in 64-bit mode, decoder features answered), with `Next_IP` `ip + 2`. -/
theorem decodeLegacy1Opcode18_run_of_r4_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_18 ip context).run s =
      (X86.Instructions.NOP_GPRv_0F18r4 (BitVec.add ip 2#64) context).run t := by
  unfold Decode_Legacy_1_Opcode_18
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1Opcode18_run_of_r4_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 5` in 64-bit mode, opcode `0F 18`'s form selection picks form 10,
`NOP_GPRv_0F18r5`. -/
theorem selectLegacy1Opcode18_run_of_r5_register (context : Instruction_Context)
    (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_1_Opcode_18 context true a b c d e f modrm = .ok 10 := by
  simp [Select_Legacy_1_Opcode_18, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`0F 18` decoder with `mod = 3` and `reg = 5` runs `NOP_GPRv_0F18r5` from the state
`t` after the ModRM fetch (in 64-bit mode, decoder features answered), with `Next_IP` `ip + 2`. -/
theorem decodeLegacy1Opcode18_run_of_r5_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_18 ip context).run s =
      (X86.Instructions.NOP_GPRv_0F18r5 (BitVec.add ip 2#64) context).run t := by
  unfold Decode_Legacy_1_Opcode_18
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1Opcode18_run_of_r5_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 6` in 64-bit mode, opcode `0F 18`'s form selection picks form 11,
`NOP_GPRv_0F18r6`. -/
theorem selectLegacy1Opcode18_run_of_r6_register (context : Instruction_Context)
    (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_1_Opcode_18 context true a b c d e f modrm = .ok 11 := by
  simp [Select_Legacy_1_Opcode_18, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`0F 18` decoder with `mod = 3` and `reg = 6` runs `NOP_GPRv_0F18r6` from the state
`t` after the ModRM fetch (in 64-bit mode, decoder features answered), with `Next_IP` `ip + 2`. -/
theorem decodeLegacy1Opcode18_run_of_r6_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_18 ip context).run s =
      (X86.Instructions.NOP_GPRv_0F18r6 (BitVec.add ip 2#64) context).run t := by
  unfold Decode_Legacy_1_Opcode_18
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1Opcode18_run_of_r6_register context a b c d e f modrm hmod hreg)

/-- With `mod = 3` and `reg = 7` in 64-bit mode, opcode `0F 18`'s form selection picks form 12,
`NOP_GPRv_0F18r7`. -/
theorem selectLegacy1Opcode18_run_of_r7_register (context : Instruction_Context)
    (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_1_Opcode_18 context true a b c d e f modrm = .ok 12 := by
  simp [Select_Legacy_1_Opcode_18, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`0F 18` decoder with `mod = 3` and `reg = 7` runs `NOP_GPRv_0F18r7` from the state
`t` after the ModRM fetch (in 64-bit mode, decoder features answered), with `Next_IP` `ip + 2`. -/
theorem decodeLegacy1Opcode18_run_of_r7_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_18 ip context).run s =
      (X86.Instructions.NOP_GPRv_0F18r7 (BitVec.add ip 2#64) context).run t := by
  unfold Decode_Legacy_1_Opcode_18
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1Opcode18_run_of_r7_register context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3` and `reg = 4` in 64-bit mode, opcode `0F 18`'s form selection picks form 13,
`NOP_MEMv_0F18r4`. -/
theorem selectLegacy1Opcode18_run_of_r4_memory (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_1_Opcode_18 context true a b c d e f modrm = .ok 13 := by
  simp [Select_Legacy_1_Opcode_18, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`0F 18` decoder with `mod ≠ 3` and `reg = 4` runs `NOP_MEMv_0F18r4` from the state
`t` after the ModRM fetch (in 64-bit mode, decoder features answered), at `ip + 2` (the address
after the ModRM byte) with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy1Opcode18_run_of_r4_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_18 ip context).run s =
      (X86.Instructions.NOP_MEMv_0F18r4 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_18
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1Opcode18_run_of_r4_memory context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3` and `reg = 5` in 64-bit mode, opcode `0F 18`'s form selection picks form 14,
`NOP_MEMv_0F18r5`. -/
theorem selectLegacy1Opcode18_run_of_r5_memory (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 5#3) :
    Select_Legacy_1_Opcode_18 context true a b c d e f modrm = .ok 14 := by
  simp [Select_Legacy_1_Opcode_18, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`0F 18` decoder with `mod ≠ 3` and `reg = 5` runs `NOP_MEMv_0F18r5` from the state
`t` after the ModRM fetch (in 64-bit mode, decoder features answered), at `ip + 2` (the address
after the ModRM byte) with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy1Opcode18_run_of_r5_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 5#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_18 ip context).run s =
      (X86.Instructions.NOP_MEMv_0F18r5 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_18
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1Opcode18_run_of_r5_memory context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3` and `reg = 6` in 64-bit mode, opcode `0F 18`'s form selection picks form 15,
`NOP_MEMv_0F18r6`. -/
theorem selectLegacy1Opcode18_run_of_r6_memory (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 6#3) :
    Select_Legacy_1_Opcode_18 context true a b c d e f modrm = .ok 15 := by
  simp [Select_Legacy_1_Opcode_18, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`0F 18` decoder with `mod ≠ 3` and `reg = 6` runs `NOP_MEMv_0F18r6` from the state
`t` after the ModRM fetch (in 64-bit mode, decoder features answered), at `ip + 2` (the address
after the ModRM byte) with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy1Opcode18_run_of_r6_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 6#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_18 ip context).run s =
      (X86.Instructions.NOP_MEMv_0F18r6 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_18
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1Opcode18_run_of_r6_memory context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3` and `reg = 7` in 64-bit mode, opcode `0F 18`'s form selection picks form 16,
`NOP_MEMv_0F18r7`. -/
theorem selectLegacy1Opcode18_run_of_r7_memory (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_1_Opcode_18 context true a b c d e f modrm = .ok 16 := by
  simp [Select_Legacy_1_Opcode_18, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-`0F 18` decoder with `mod ≠ 3` and `reg = 7` runs `NOP_MEMv_0F18r7` from the state
`t` after the ModRM fetch (in 64-bit mode, decoder features answered), at `ip + 2` (the address
after the ModRM byte) with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy1Opcode18_run_of_r7_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_18 ip context).run s =
      (X86.Instructions.NOP_MEMv_0F18r7 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_18
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1Opcode18_run_of_r7_memory context a b c d e f modrm hmod hreg)

end X86Proofs
