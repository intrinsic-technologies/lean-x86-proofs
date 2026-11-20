import X86Proofs.Step.Decode

/-!
# Opcode `A4`: `MOVSB`, `REP MOVSB` (`F3` and `F2`)

The one place that looks inside lean-x86's opcode-`A4` decoder (`Decode_Legacy_0_Opcode_A4`) and its
form selection (`Select_Legacy_0_Opcode_A4`), architecture rule 5. In 64-bit mode the selection
picks `MOVSB` without a REP prefix (`Instructions/Movs`) and `REP_MOVSB_0` after `F3`
(`Instructions/Movs/Generated/Rep`), and `REP_MOVSB_1` after `F2` (the same operation;
`Instructions/Movs/Generated/RepF2`). For each form, a `selectLegacy0OpcodeA4_run_of_…` lemma gives
the index the selection picks and a `decodeLegacy0OpcodeA4_run_of_…` lemma runs the decoder to the
call of that form at `ip + 1` (no ModRM byte). The dispatch to this decoder is
`decodeLegacy0_run_of_opcodeA4` (`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem selectLegacy0OpcodeA4_run_of_noRep (context : Instruction_Context) (hrep : context.rep_prefix = 0)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A4 context true a b c d e f 0 = .ok 3 := by
  simp [Select_Legacy_0_Opcode_A4, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

theorem selectLegacy0OpcodeA4_run_of_rep (context : Instruction_Context) (hrep : context.rep_prefix = 243)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A4 context true a b c d e f 0 = .ok 2 := by
  simp [Select_Legacy_0_Opcode_A4, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A4` decoder without a REP prefix runs `MOVSB` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA4_run_of_noRep [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A4 ip context).run s =
      (X86.Instructions.MOVSB (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A4
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A4 context mode a b c d e f z) _ 3 hmode hf
    (selectLegacy0OpcodeA4_run_of_noRep context hrep)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- The opcode-`A4` decoder with `F3` runs `REP_MOVSB_0` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA4_run_of_rep_movsb [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A4 ip context).run s =
      (X86.Instructions.REP_MOVSB_0 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A4
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A4 context mode a b c d e f z) _ 2 hmode hf
    (selectLegacy0OpcodeA4_run_of_rep context hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `F2`, in 64-bit mode: form 1, `REP_MOVSB_1`. -/
theorem selectLegacy0OpcodeA4_run_of_rep_movsb_f2 (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A4 context true a b c d e f 0 = .ok 1 := by
  simp [Select_Legacy_0_Opcode_A4, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A4` decoder in that context runs `REP_MOVSB_1` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA4_run_of_rep_movsb_f2 [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A4 ip context).run s =
      (X86.Instructions.REP_MOVSB_1 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A4
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A4 context mode a b c d e f z) _ 1 hmode hf
    (selectLegacy0OpcodeA4_run_of_rep_movsb_f2 context hrep)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- `selectLegacy0OpcodeA4_run_of_noRep` under the name the `string` family uses for MOVSB. -/
theorem selectLegacy0OpcodeA4_run_of_movsb (context : Instruction_Context)
    (hrep : context.rep_prefix = 0) (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A4 context true a b c d e f 0 = .ok 3 :=
  selectLegacy0OpcodeA4_run_of_noRep context hrep a b c d e f

/-- `decodeLegacy0OpcodeA4_run_of_noRep` under the name the `string` family uses for MOVSB. -/
theorem decodeLegacy0OpcodeA4_run_of_movsb [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A4 ip context).run s =
      (X86.Instructions.MOVSB (BitVec.add ip 1#64) context).run s :=
  decodeLegacy0OpcodeA4_run_of_noRep s ip context hrep hmode hf

end X86Proofs
