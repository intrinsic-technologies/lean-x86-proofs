import X86Proofs.Step.Decode

/-!
# Opcode `C6`: group 11 (`MOV r/m8, imm8`)

The one place that looks inside lean-x86's opcode-`C6` decoder (`Decode_Legacy_0_Opcode_C6`) and its
form selection (`Select_Legacy_0_Opcode_C6`), architecture rule 5. Several instruction folders use
the opcode, each through the lemmas here. For each ModRM case the library uses — `reg = 0` with
`mod = 3` (`Instructions/Mov/Generated/R8Imm8C6`) and with a memory operand
(`Instructions/MovStore`) — a `selectLegacy0OpcodeC6_run_of_…` lemma gives the form the
selection picks, and a `decodeLegacy0OpcodeC6_run_of_…` lemma runs the decoder (from the ModRM
fetch at `ip + 1`) to the call of that form at `ip + 2` (the form fetches the immediate itself).
For a new case, add the pair here (the decoder lemma is `decode_modrm_form`).

`Decode_Legacy_0`'s dispatch to this decoder is `decodeLegacy0_run_of_opcodeC6`
(`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` and `reg = 0` in 64-bit mode, opcode C6's form selection picks form 1,
`MOV_GPR8_IMMb_C6r0`. -/
theorem selectLegacy0OpcodeC6_run_of_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_C6 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_C6, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/--
The opcode-C6 decoder with a register ModRM and `reg = 0`. If fetching the byte after the opcode
at `ip` returns a ModRM byte with `mod = 3` and `reg = 0` and leaves state `t` (in 64-bit mode,
decoder features answered), the decoder runs `MOV_GPR8_IMMb_C6r0` from `t` with `Next_IP` `ip + 2`
(the immediate's address) and the ModRM `rm` field.
-/
theorem decodeLegacy0OpcodeC6_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_C6 ip context).run s =
      (X86.Instructions.MOV_GPR8_IMMb_C6r0 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_C6
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeC6_run_of_register context a b c d e f modrm hmod hreg)

/-- With `mod ≠ 3` and `reg = 0` in 64-bit mode, opcode C6's form selection picks form 2,
`MOV_MEMb_IMMb_1`. -/
theorem selectLegacy0OpcodeC6_run_of_memory (context : Instruction_Context) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_C6 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_C6, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-C6 decoder with a memory ModRM and `reg = 0`: it runs `MOV_MEMb_IMMb_1` from the
state after the ModRM fetch, at `ip + 2`, with the ModRM `mod` and `rm` fields. -/
theorem decodeLegacy0OpcodeC6_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_C6 ip context).run s =
      (X86.Instructions.MOV_MEMb_IMMb_1 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_C6
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f =>
    Select_Legacy_0_Opcode_C6 context mode a b c d e f modrm) _ 2 hmode hf
    (fun a b c d e f => selectLegacy0OpcodeC6_run_of_memory context a b c d e f modrm hmod hreg)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

end X86Proofs
