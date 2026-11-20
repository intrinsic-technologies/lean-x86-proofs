import X86Proofs.Step.Decode

/-!
# Opcode `AC`: `LODSB`, `REP LODSB` (`F3` and `F2`)

The one place that looks inside lean-x86's opcode-`AC` decoder (`Decode_Legacy_0_Opcode_AC`) and its
form selection (`Select_Legacy_0_Opcode_AC`), architecture rule 5. In 64-bit mode the selection
picks `LODSB` without a REP prefix (`Instructions/Lods/Generated/Str`) and `REP_LODSB_0` after `F3`
(`Instructions/Lods/Generated/Rep`), and `REP_LODSB_1` after `F2` (the same operation;
`Instructions/Lods/Generated/RepF2`). For each form, a `selectLegacy0OpcodeAC_run_of_…` lemma gives
the index the selection picks and a `decodeLegacy0OpcodeAC_run_of_…` lemma runs the decoder to the
call of that form at `ip + 1` (no ModRM byte). The dispatch to this decoder is
`decodeLegacy0_run_of_opcodeAC` (`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- Without a REP prefix, in 64-bit mode: form 3, `LODSB`. -/
theorem selectLegacy0OpcodeAC_run_of_lodsb (context : Instruction_Context)
    (hrep : context.rep_prefix = 0)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AC context true a b c d e f 0 = .ok 3 := by
  simp [Select_Legacy_0_Opcode_AC, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AC` decoder in that context runs `LODSB` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAC_run_of_lodsb [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AC ip context).run s =
      (X86.Instructions.LODSB (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AC
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AC context mode a b c d e f z) _ 3 hmode hf
    (selectLegacy0OpcodeAC_run_of_lodsb context hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `F3`, in 64-bit mode: form 2, `REP_LODSB_0`. -/
theorem selectLegacy0OpcodeAC_run_of_rep_lodsb (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AC context true a b c d e f 0 = .ok 2 := by
  simp [Select_Legacy_0_Opcode_AC, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AC` decoder in that context runs `REP_LODSB_0` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAC_run_of_rep_lodsb [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AC ip context).run s =
      (X86.Instructions.REP_LODSB_0 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AC
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AC context mode a b c d e f z) _ 2 hmode hf
    (selectLegacy0OpcodeAC_run_of_rep_lodsb context hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `F2`, in 64-bit mode: form 1, `REP_LODSB_1`. -/
theorem selectLegacy0OpcodeAC_run_of_rep_lodsb_f2 (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AC context true a b c d e f 0 = .ok 1 := by
  simp [Select_Legacy_0_Opcode_AC, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AC` decoder in that context runs `REP_LODSB_1` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAC_run_of_rep_lodsb_f2 [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AC ip context).run s =
      (X86.Instructions.REP_LODSB_1 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AC
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AC context mode a b c d e f z) _ 1 hmode hf
    (selectLegacy0OpcodeAC_run_of_rep_lodsb_f2 context hrep)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

end X86Proofs
