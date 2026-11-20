import X86Proofs.Step.Decode

/-!
# Opcode `87`: `XCHG r/m, r`

The one place that looks inside lean-x86's opcode-`87` decoder (`Decode_Legacy_0_Opcode_87`) and its
form selection (`Select_Legacy_0_Opcode_87`), architecture rule 5. With a register operand (`mod =
3`) the selection picks `XCHG_GPRv_GPRv` (`Instructions/Xchg/Generated/RR`). The memory forms
(`XCHG_MEMv_GPRv_0` with LOCK, `XCHG_MEMv_GPRv_1` without, `Instructions/Xchg/Generated/MRLock`
and `MR`) both access memory as a locked read-modify-write (`Logical_Mem_Read` with
`acquire_lock`, `logicalMemRead_run_seg_lock`). For each form, a
`selectLegacy0Opcode87_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy0Opcode87_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`, `ip`
the opcode byte's address) to the call of that form at `ip + 2`.

The dispatch to this decoder is `decodeLegacy0_run_of_opcode87` (`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` in 64-bit mode, opcode 87's form selection picks form 2, `XCHG_GPRv_GPRv`. -/
theorem selectLegacy0Opcode87_run_of_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_0_Opcode_87 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_87, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-87 decoder with a register ModRM (`mod = 3`) runs `XCHG_GPRv_GPRv` from the state
after the ModRM fetch, at `ip + 2`, with the ModRM `reg` and `rm` fields. -/
theorem decodeLegacy0Opcode87_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_87 ip context).run s =
      (X86.Instructions.XCHG_GPRv_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_87
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy0Opcode87_run_of_register context a b c d e f modrm hmod)

/-- With `mod ≠ 3` and no LOCK prefix in 64-bit mode, opcode 87's form selection picks form
3, `XCHG_MEMv_GPRv_1`. -/
theorem selectLegacy0Opcode87_run_of_memory (context : Instruction_Context)
    (hlock : context.lock_prefix_present = false) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_0_Opcode_87 context true a b c d e f modrm = .ok 3 := by
  simp [Select_Legacy_0_Opcode_87, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-87 decoder with a memory ModRM (`mod ≠ 3`) and no LOCK prefix runs `XCHG_MEMv_GPRv_1`
from the state after the ModRM fetch, at `ip + 2`, with the ModRM `mod`, `reg` and `rm` fields. -/
theorem decodeLegacy0Opcode87_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hlock : context.lock_prefix_present = false)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_87 ip context).run s =
      (X86.Instructions.XCHG_MEMv_GPRv_1 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_87
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode87_run_of_memory context hlock a b c d e f modrm hmod)

/-- With `mod ≠ 3` and a LOCK prefix in 64-bit mode, opcode 87's form selection picks form
1, `XCHG_MEMv_GPRv_0`. -/
theorem selectLegacy0Opcode87_run_of_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_0_Opcode_87 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_87, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-87 decoder with a memory ModRM (`mod ≠ 3`) and a LOCK prefix runs `XCHG_MEMv_GPRv_0`
from the state after the ModRM fetch, at `ip + 2`, with the ModRM `mod`, `reg` and `rm` fields. -/
theorem decodeLegacy0Opcode87_run_of_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hlock : context.lock_prefix_present = true)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_87 ip context).run s =
      (X86.Instructions.XCHG_MEMv_GPRv_0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_87
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy0Opcode87_run_of_memory_lock context hlock a b c d e f modrm hmod)

end X86Proofs
