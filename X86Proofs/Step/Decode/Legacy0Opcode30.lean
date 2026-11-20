import X86Proofs.Step.Decode

/-!
# Opcode `30`: `XOR r/m8, r8`

The one place that looks inside lean-x86's opcode-`30` decoder (`Decode_Legacy_0_Opcode_30`) and its
form selection (`Select_Legacy_0_Opcode_30`), architecture rule 5. Several instruction folders use
the opcode, each through the lemmas here. For each ModRM case the library uses — `mod = 3`
(`Instructions/Xor/Generated/R8`) and a memory operand without LOCK
(`Instructions/Xor/Generated/M8R8`) — a
`selectLegacy0Opcode30_run_of_…` lemma gives the form the selection picks, and a
`decodeLegacy0Opcode30_run_of_…` lemma runs the decoder (from the ModRM fetch at `ip + 1`) to the
call of that form at `ip + 2`. For a new case, add the pair here (the decoder lemma is
`decode_modrm_form`).

The `…_lock` pairs are the same cases with a LOCK prefix (`lock_prefix_present = true`),
selecting the `<OP>_LOCK_…` form (the generated `…Lock` rows).

`Decode_Legacy_0`'s dispatch to this decoder is `decodeLegacy0_run_of_opcode30`
(`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3` in 64-bit mode, opcode 30's form selection picks form 1, `XOR_GPR8_GPR8_30`. -/
theorem selectLegacy0Opcode30_run_of_register (context : Instruction_Context) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_0_Opcode_30 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_30, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/--
The opcode-30 decoder with a register ModRM. If fetching the byte after the opcode at `ip`
returns a ModRM byte with `mod = 3` and leaves state `t` (in 64-bit mode, decoder features
answered), the decoder runs `XOR_GPR8_GPR8_30` from `t` with `Next_IP` `ip + 2` and the ModRM
`reg` and `rm` fields.
-/
theorem decodeLegacy0Opcode30_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_30 ip context).run s =
      (X86.Instructions.XOR_GPR8_GPR8_30 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_30
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode30_run_of_register context a b c d e f modrm hmod)

/-- With `mod ≠ 3`, no LOCK prefix and 64-bit mode, opcode 30's form selection picks form 2,
`XOR_MEMb_GPR8`. -/
theorem selectLegacy0Opcode30_run_of_memory (context : Instruction_Context) (hlock : context.lock_prefix_present = false)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_0_Opcode_30 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_30, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-30 decoder with a memory ModRM and no LOCK prefix runs `XOR_MEMb_GPR8`. -/
theorem decodeLegacy0Opcode30_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hlock : context.lock_prefix_present = false) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_30 ip context).run s =
      (X86.Instructions.XOR_MEMb_GPR8 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_30
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 5 3) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f =>
    Select_Legacy_0_Opcode_30 context mode a b c d e f modrm) _ 2 hmode hf
    (fun a b c d e f => selectLegacy0Opcode30_run_of_memory context hlock a b c d e f modrm hmod)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

/-- With `mod ≠ 3`, a LOCK prefix and 64-bit mode, opcode 30's form selection picks form 3,
`XOR_LOCK_MEMb_GPR8`. -/
theorem selectLegacy0Opcode30_run_of_memory_lock (context : Instruction_Context)
    (hlock : context.lock_prefix_present = true)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_0_Opcode_30 context true a b c d e f modrm = .ok 3 := by
  simp [Select_Legacy_0_Opcode_30, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hlock, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-30 decoder with a memory ModRM and a LOCK prefix runs `XOR_LOCK_MEMb_GPR8`. -/
theorem decodeLegacy0Opcode30_run_of_memory_lock [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hlock : context.lock_prefix_present = true) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_30 ip context).run s =
      (X86.Instructions.XOR_LOCK_MEMb_GPR8 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_30
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 5 3) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f =>
    Select_Legacy_0_Opcode_30 context mode a b c d e f modrm) _ 3 hmode hf
    (fun a b c d e f => selectLegacy0Opcode30_run_of_memory_lock context hlock a b c d e f modrm
      hmod)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

end X86Proofs
