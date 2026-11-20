import X86Proofs.Step.Decode

/-!
# Opcode `0F C7`: group 9, `CMPXCHG8B m64`, `CMPXCHG16B m128`

The one place that looks inside lean-x86's opcode-`C7` decoder (`Decode_Legacy_1_Opcode_C7`) and its
form selection (`Select_Legacy_1_Opcode_C7`), architecture rule 5. In 64-bit mode the selection
depends on `mod`, the ModRM `reg` digit, REX.W and the LOCK prefix: with `mod ≠ 3` and `reg = 1`,
REX.W clear and no LOCK it picks `CMPXCHG8B_MEMq_1` (`Instructions/Cmpxchg8b/Generated/M64`); with
REX.W set and the CPUID CMPXCHG16B feature reported it picks `CMPXCHG16B_MEMdq`
(`Instructions/Cmpxchg16b/Generated/M128`; the `…_w` pairs, which take the feature's answer,
`decode_modrm_form_cmpxchg16b`), and with LOCK the locked forms (`CMPXCHG8B_LOCK_MEMq_1`,
`CMPXCHG16B_LOCK_MEMdq`, `Instructions/Cmpxchg8b/Generated/M64Lock`,
`Instructions/Cmpxchg16b/Generated/M128Lock`). The
`selectLegacy1OpcodeC7_run_of_r1_memory` lemma gives the form the selection picks, and
`decodeLegacy1OpcodeC7_run_of_r1_memory` runs the decoder (from the ModRM fetch at `ip + 1`, `ip`
the second opcode byte's address) to the call of that form at `ip + 2`.

The `…_lock` pairs are the same cases with a LOCK prefix (`lock_prefix_present = true`),
selecting the `<OP>_LOCK_…` form (the generated `…Lock` rows).

The dispatch to this decoder is `decodeLegacy1_run_of_opcodeC7` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod ≠ 3`, `reg = 1`, REX.W clear and no LOCK prefix in 64-bit mode, opcode C7's form
selection picks form 2, `CMPXCHG8B_MEMq_1`. -/
theorem selectLegacy1OpcodeC7_run_of_r1_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hw : context.rex_w = 0)
    (hlock : context.lock_prefix_present = false) :
    Select_Legacy_1_Opcode_C7 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_C7, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hw, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-C7 decoder with a memory ModRM (`mod ≠ 3`, `reg = 1`), REX.W clear and no LOCK
prefix runs `CMPXCHG8B_MEMq_1` from the state after the ModRM fetch, at `ip + 2`, with the ModRM
`mod` and `rm` fields. -/
theorem decodeLegacy1OpcodeC7_run_of_r1_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hw : context.rex_w = 0)
    (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_C7 ip context).run s =
      (X86.Instructions.CMPXCHG8B_MEMq_1 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_C7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1OpcodeC7_run_of_r1_memory context a b c d e f modrm hmod hreg hw hlock)

/-- With `mod ≠ 3`, `reg = 1`, REX.W clear and a LOCK prefix in 64-bit mode, opcode C7's form
selection picks form 4, `CMPXCHG8B_LOCK_MEMq_1`. -/
theorem selectLegacy1OpcodeC7_run_of_r1_memory_lock (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hw : context.rex_w = 0)
    (hlock : context.lock_prefix_present = true) :
    Select_Legacy_1_Opcode_C7 context true a b c d e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_C7, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hw, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-C7 decoder with a memory ModRM (`mod ≠ 3`, `reg = 1`), REX.W clear and a LOCK
prefix runs `CMPXCHG8B_LOCK_MEMq_1` from the state after the ModRM fetch, at `ip + 2`, with the
ModRM
`mod` and `rm` fields. -/
theorem decodeLegacy1OpcodeC7_run_of_r1_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hw : context.rex_w = 0)
    (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_C7 ip context).run s =
      (X86.Instructions.CMPXCHG8B_LOCK_MEMq_1 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_C7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1OpcodeC7_run_of_r1_memory_lock context a b c d e f modrm hmod hreg hw hlock)

/-- With `mod ≠ 3`, `reg = 1`, REX.W set, no LOCK prefix and CMPXCHG16B reported in 64-bit mode,
opcode C7's form selection picks form 1, `CMPXCHG16B_MEMdq`. -/
theorem selectLegacy1OpcodeC7_run_of_r1_memory_w (context : Instruction_Context)
    (a b c d e : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hw : context.rex_w = 1)
    (hlock : context.lock_prefix_present = false) :
    Select_Legacy_1_Opcode_C7 context true a b c d e true modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_C7, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hw, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-C7 decoder with a memory ModRM (`mod ≠ 3`, `reg = 1`), REX.W set, no LOCK prefix
and CMPXCHG16B reported runs `CMPXCHG16B_MEMdq` from the state after the ModRM fetch, at `ip + 2`,
with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy1OpcodeC7_run_of_r1_memory_w [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hw : context.rex_w = 1)
    (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hc : Prelude.ReportsCPUFeature Bindings.processor t CPUID_CMPXCHG16B_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_C7 ip context).run s =
      (X86.Instructions.CMPXCHG16B_MEMdq (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_C7
  decode_modrm_form_cmpxchg16b s t ip hfetch hmode hf hc
    (fun a b c d e =>
      selectLegacy1OpcodeC7_run_of_r1_memory_w context a b c d e modrm hmod hreg hw hlock)

/-- With `mod ≠ 3`, `reg = 1`, REX.W set, a LOCK prefix and CMPXCHG16B reported in 64-bit mode,
opcode C7's form selection picks form 3, `CMPXCHG16B_LOCK_MEMdq`. -/
theorem selectLegacy1OpcodeC7_run_of_r1_memory_w_lock (context : Instruction_Context)
    (a b c d e : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hw : context.rex_w = 1)
    (hlock : context.lock_prefix_present = true) :
    Select_Legacy_1_Opcode_C7 context true a b c d e true modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_C7, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, hw, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-C7 decoder with a memory ModRM (`mod ≠ 3`, `reg = 1`), REX.W set, a LOCK prefix
and CMPXCHG16B reported runs `CMPXCHG16B_LOCK_MEMdq` from the state after the ModRM fetch, at
`ip + 2`, with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy1OpcodeC7_run_of_r1_memory_w_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 1#3) (hw : context.rex_w = 1)
    (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hc : Prelude.ReportsCPUFeature Bindings.processor t CPUID_CMPXCHG16B_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_C7 ip context).run s =
      (X86.Instructions.CMPXCHG16B_LOCK_MEMdq (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_C7
  decode_modrm_form_cmpxchg16b s t ip hfetch hmode hf hc
    (fun a b c d e =>
      selectLegacy1OpcodeC7_run_of_r1_memory_w_lock context a b c d e modrm hmod hreg hw hlock)

end X86Proofs
