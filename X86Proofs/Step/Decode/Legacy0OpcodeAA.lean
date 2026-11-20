import X86Proofs.Step.Decode

/-!
# Opcode `AA`: `STOSB`, `REP STOSB` (`F3` and `F2`)

The one place that looks inside lean-x86's opcode-`AA` decoder (`Decode_Legacy_0_Opcode_AA`) and its
form selection (`Select_Legacy_0_Opcode_AA`), architecture rule 5. In 64-bit mode the selection
picks `STOSB` without a REP prefix (`Instructions/Stos/Generated/Str`) and `REP_STOSB_0` after `F3`
(`Instructions/Stos/Generated/Rep`), and `REP_STOSB_1` after `F2` (the same operation;
`Instructions/Stos/Generated/RepF2`). For each form, a `selectLegacy0OpcodeAA_run_of_…` lemma gives
the index the selection picks and a `decodeLegacy0OpcodeAA_run_of_…` lemma runs the decoder to the
call of that form at `ip + 1` (no ModRM byte). The dispatch to this decoder is
`decodeLegacy0_run_of_opcodeAA` (`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- Without a REP prefix, in 64-bit mode: form 3, `STOSB`. -/
theorem selectLegacy0OpcodeAA_run_of_stosb (context : Instruction_Context)
    (hrep : context.rep_prefix = 0)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AA context true a b c d e f 0 = .ok 3 := by
  simp [Select_Legacy_0_Opcode_AA, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AA` decoder without a REP prefix runs `STOSB` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAA_run_of_stosb [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AA ip context).run s =
      (X86.Instructions.STOSB (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AA
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AA context mode a b c d e f z) _ 3 hmode hf
    (selectLegacy0OpcodeAA_run_of_stosb context hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `F3`, in 64-bit mode: form 2, `REP_STOSB_0`. -/
theorem selectLegacy0OpcodeAA_run_of_rep_stosb (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AA context true a b c d e f 0 = .ok 2 := by
  simp [Select_Legacy_0_Opcode_AA, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AA` decoder with `F3` runs `REP_STOSB_0` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAA_run_of_rep_stosb [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AA ip context).run s =
      (X86.Instructions.REP_STOSB_0 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AA
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AA context mode a b c d e f z) _ 2 hmode hf
    (selectLegacy0OpcodeAA_run_of_rep_stosb context hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `F2`, in 64-bit mode: form 1, `REP_STOSB_1`. -/
theorem selectLegacy0OpcodeAA_run_of_rep_stosb_f2 (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AA context true a b c d e f 0 = .ok 1 := by
  simp [Select_Legacy_0_Opcode_AA, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AA` decoder in that context runs `REP_STOSB_1` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAA_run_of_rep_stosb_f2 [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AA ip context).run s =
      (X86.Instructions.REP_STOSB_1 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AA
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AA context mode a b c d e f z) _ 1 hmode hf
    (selectLegacy0OpcodeAA_run_of_rep_stosb_f2 context hrep)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

end X86Proofs
