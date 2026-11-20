import X86Proofs.Step.Decode

/-!
# Opcode `0F BB`: `BTC r/m, r`

The one place that looks inside lean-x86's opcode-`BB` decoder (`Decode_Legacy_1_Opcode_BB`) and its
form selection (`Select_Legacy_1_Opcode_BB`), architecture rule 5. The library uses the register
form (`mod = 3`, `BTC_GPRv_GPRv`, `Instructions/Btc/Generated/RR`) and the memory form (`mod ≠ 3`,
`BTC_MEMv_GPRv`, `Instructions/Btc/Generated/MR`) and its LOCK form (`BTC_LOCK_MEMv_GPRv`,
`MRLock`), whose register bit offset also moves the address (`bitStringOffset`). For each, a
`selectLegacy1OpcodeBB_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy1OpcodeBB_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`, `ip` the
second opcode byte's address) to the call of that form at `ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcodeBB` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` in 64-bit mode, opcode BB's form selection picks form 1, `BTC_GPRv_GPRv`. -/
theorem selectLegacy1OpcodeBB_run_of_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_BB context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_BB, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-BB decoder with a register ModRM (`mod = 3`) runs `BTC_GPRv_GPRv` from the state
after the ModRM fetch, at `ip + 2`, with the ModRM `reg` and `rm` fields. -/
theorem decodeLegacy1OpcodeBB_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BB ip context).run s =
      (X86.Instructions.BTC_GPRv_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BB
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeBB_run_of_register context a b c d e f modrm hmod)

/-- With `mod ≠ 3`, `lock_prefix_present = false` in 64-bit mode, opcode BB's form selection picks
form 2, `BTC_MEMv_GPRv`. -/
theorem selectLegacy1OpcodeBB_run_of_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hlock : context.lock_prefix_present = false) :
    Select_Legacy_1_Opcode_BB context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_BB, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-BB decoder with a memory ModRM (`mod ≠ 3`) and no LOCK prefix runs `BTC_MEMv_GPRv`
from the state after the ModRM fetch, at `ip + 2`, with the ModRM `mod`, `reg` and `rm` fields. -/
theorem decodeLegacy1OpcodeBB_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BB ip context).run s =
      (X86.Instructions.BTC_MEMv_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BB
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1OpcodeBB_run_of_memory context a b c d e f modrm hmod hlock)

/-- With `mod ≠ 3`, `lock_prefix_present = true` in 64-bit mode, opcode BB's form selection picks
form 3, `BTC_LOCK_MEMv_GPRv`. -/
theorem selectLegacy1OpcodeBB_run_of_memory_lock (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hlock : context.lock_prefix_present = true) :
    Select_Legacy_1_Opcode_BB context true a b c d e f modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_BB, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-BB decoder with a memory ModRM (`mod ≠ 3`) and a LOCK prefix runs
`BTC_LOCK_MEMv_GPRv` from the state after the ModRM fetch, at `ip + 2`, with the ModRM `mod`, `reg`
and `rm` fields. -/
theorem decodeLegacy1OpcodeBB_run_of_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BB ip context).run s =
      (X86.Instructions.BTC_LOCK_MEMv_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BB
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy1OpcodeBB_run_of_memory_lock context a b c d e f modrm hmod hlock)

end X86Proofs
