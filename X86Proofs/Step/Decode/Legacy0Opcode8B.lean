import X86Proofs.Step.Decode

/-!
# Opcode `8B`: `MOV r, r/m`

The one place that looks inside lean-x86's opcode-`8B` decoder (`Decode_Legacy_0_Opcode_8B`) and its
form selection (`Select_Legacy_0_Opcode_8B`), architecture rule 5. Several instruction folders use
the opcode, each through the lemmas here. For each ModRM case the library uses — `mod = 3`
(`Instructions/Mov/Generated/RRRev`) and a memory operand (`Instructions/MovLoad`,
`Instructions/Mov/Generated/RM`) — a `selectLegacy0Opcode8B_run_of_…` lemma gives the form the
selection picks, and a `decodeLegacy0Opcode8B_run_of_…` lemma runs the decoder (from the ModRM fetch
at `ip + 1`) to the call of that form at `ip + 2`. For a new case, add the pair here (the decoder
lemma is `decode_modrm_form`).

`Decode_Legacy_0`'s dispatch to this decoder is `decodeLegacy0_run_of_opcode8B`
(`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` in 64-bit mode, opcode 8B's form selection picks form 1, `MOV_GPRv_GPRv_8B`. -/
theorem selectLegacy0Opcode8B_run_of_register (context : Instruction_Context) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_0_Opcode_8B context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_8B, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-8B decoder with a register ModRM: it runs `MOV_GPRv_GPRv_8B` from the state after
the ModRM fetch, at `ip + 2`, with the ModRM `reg` and `rm` fields. -/
theorem decodeLegacy0Opcode8B_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_8B ip context).run s =
      (X86.Instructions.MOV_GPRv_GPRv_8B (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_8B
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode8B_run_of_register context a b c d e f modrm hmod)

/-- With `mod ≠ 3` in 64-bit mode, opcode 8B's form selection picks form 2, `MOV_GPRv_MEMv_1`. -/
theorem selectLegacy0Opcode8B_run_of_memory (context : Instruction_Context) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_0_Opcode_8B context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_8B, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/--
The opcode-8B decoder with a memory ModRM. If fetching the byte after the opcode at `ip` returns a
ModRM byte with `mod ≠ 3` and leaves state `t` (in 64-bit mode, decoder features answered), the
decoder runs `MOV_GPRv_MEMv_1` from `t` with `ip + 2` (the address after the ModRM byte) and the
ModRM fields.
-/
theorem decodeLegacy0Opcode8B_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_8B ip context).run s =
      (X86.Instructions.MOV_GPRv_MEMv_1 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_8B
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 5 3) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f =>
    Select_Legacy_0_Opcode_8B context mode a b c d e f modrm) _ 2 hmode hf
    (fun a b c d e f => selectLegacy0Opcode8B_run_of_memory context a b c d e f modrm hmod)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

end X86Proofs
