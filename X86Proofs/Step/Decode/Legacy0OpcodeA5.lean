import X86Proofs.Step.Decode

/-!
# Opcode `A5`: `MOVSW`, `MOVSD`, `MOVSQ` and their REP forms

The one place that looks inside lean-x86's opcode-`A5` decoder (`Decode_Legacy_0_Opcode_A5`) and its
form selection (`Select_Legacy_0_Opcode_A5`), architecture rule 5. In 64-bit mode the selection
picks the form by the operand size (REX.W, else `66`) and the REP prefix: `MOVSQ`, `MOVSW_2`,
`MOVSD_2` without one (`Instructions/Movs/Generated/Str`), `REP_MOVSQ_0` (`Instructions/Movs`;
its `_seg` chain `Instructions/Movs/Generated/Rep`, through the aliases `…_run_of_rep_movsq`),
`REP_MOVSW_2`, `REP_MOVSD_2` after `F3` (`Instructions/Movs/Generated/Rep`), `REP_MOVSQ_1`,
`REP_MOVSW_5`, `REP_MOVSD_5` after `F2` (the same operations; `Instructions/Movs/Generated/RepF2`).
For each form, a
`selectLegacy0OpcodeA5_run_of_…` lemma gives the index the selection picks and a
`decodeLegacy0OpcodeA5_run_of_…` lemma runs the decoder to the call of that form at `ip + 1` (no
ModRM byte). The dispatch to this decoder is `decodeLegacy0_run_of_opcodeA5`
(`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem selectLegacy0OpcodeA5_run_of_rep_rexW (context : Instruction_Context) (hrep : context.rep_prefix = 243)
    (hw : context.rex_w = 1) (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A5 context true a b c d e f 0 = .ok 6 := by
  simp [Select_Legacy_0_Opcode_A5, hrep, hw, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A5` decoder with `F3` and REX.W runs `REP_MOVSQ_0` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA5_run_of_rep_rexW [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrep : context.rep_prefix = 243) (hw : context.rex_w = 1)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A5 ip context).run s =
      (X86.Instructions.REP_MOVSQ_0 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A5
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A5 context mode a b c d e f z) _ 6 hmode hf
    (selectLegacy0OpcodeA5_run_of_rep_rexW context hrep hw)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- `selectLegacy0OpcodeA5_run_of_rep_rexW` with the hypotheses in the `rep_string` family's
order (`hw`, then `hrep`). -/
theorem selectLegacy0OpcodeA5_run_of_rep_movsq (context : Instruction_Context)
    (hw : context.rex_w = 1) (hrep : context.rep_prefix = 243) (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A5 context true a b c d e f 0 = .ok 6 :=
  selectLegacy0OpcodeA5_run_of_rep_rexW context hrep hw a b c d e f

/-- `decodeLegacy0OpcodeA5_run_of_rep_rexW` with the hypotheses in the `rep_string` family's order
(`hw`, then `hrep`). -/
theorem decodeLegacy0OpcodeA5_run_of_rep_movsq [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hw : context.rex_w = 1) (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A5 ip context).run s =
      (X86.Instructions.REP_MOVSQ_0 (BitVec.add ip 1#64) context).run s :=
  decodeLegacy0OpcodeA5_run_of_rep_rexW s ip context hrep hw hmode hf

/-- With REX.W and no REP prefix: form 8, `MOVSQ`. -/
theorem selectLegacy0OpcodeA5_run_of_movsq (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 0)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A5 context true a b c d e f 0 = .ok 8 := by
  simp [Select_Legacy_0_Opcode_A5, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A5` decoder in that context runs `MOVSQ` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA5_run_of_movsq [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A5 ip context).run s =
      (X86.Instructions.MOVSQ (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A5
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A5 context mode a b c d e f z) _ 8 hmode hf
    (selectLegacy0OpcodeA5_run_of_movsq context hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `66`, REX.W clear and no REP prefix: form 9, `MOVSW_2`. -/
theorem selectLegacy0OpcodeA5_run_of_movsw (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A5 context true a b c d e f 0 = .ok 9 := by
  simp [Select_Legacy_0_Opcode_A5, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A5` decoder in that context runs `MOVSW_2` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA5_run_of_movsw [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A5 ip context).run s =
      (X86.Instructions.MOVSW_2 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A5
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A5 context mode a b c d e f z) _ 9 hmode hf
    (selectLegacy0OpcodeA5_run_of_movsw context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- Without `66`, REX.W or a REP prefix: form 1, `MOVSD_2`. -/
theorem selectLegacy0OpcodeA5_run_of_movsd (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A5 context true a b c d e f 0 = .ok 1 := by
  simp [Select_Legacy_0_Opcode_A5, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A5` decoder in that context runs `MOVSD_2` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA5_run_of_movsd [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A5 ip context).run s =
      (X86.Instructions.MOVSD_2 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A5
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A5 context mode a b c d e f z) _ 1 hmode hf
    (selectLegacy0OpcodeA5_run_of_movsd context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `66`, REX.W clear and `F3`: form 7, `REP_MOVSW_2`. -/
theorem selectLegacy0OpcodeA5_run_of_rep_movsw (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 243)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A5 context true a b c d e f 0 = .ok 7 := by
  simp [Select_Legacy_0_Opcode_A5, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A5` decoder in that context runs `REP_MOVSW_2` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA5_run_of_rep_movsw [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A5 ip context).run s =
      (X86.Instructions.REP_MOVSW_2 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A5
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A5 context mode a b c d e f z) _ 7 hmode hf
    (selectLegacy0OpcodeA5_run_of_rep_movsw context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `F3`, without `66` or REX.W: form 5, `REP_MOVSD_2`. -/
theorem selectLegacy0OpcodeA5_run_of_rep_movsd (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 243)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A5 context true a b c d e f 0 = .ok 5 := by
  simp [Select_Legacy_0_Opcode_A5, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A5` decoder in that context runs `REP_MOVSD_2` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA5_run_of_rep_movsd [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A5 ip context).run s =
      (X86.Instructions.REP_MOVSD_2 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A5
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A5 context mode a b c d e f z) _ 5 hmode hf
    (selectLegacy0OpcodeA5_run_of_rep_movsd context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `F2`, without `66` or REX.W, in 64-bit mode: form 2, `REP_MOVSD_5`. -/
theorem selectLegacy0OpcodeA5_run_of_rep_movsd_f2 (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 242)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A5 context true a b c d e f 0 = .ok 2 := by
  simp [Select_Legacy_0_Opcode_A5, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A5` decoder in that context runs `REP_MOVSD_5` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA5_run_of_rep_movsd_f2 [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 242)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A5 ip context).run s =
      (X86.Instructions.REP_MOVSD_5 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A5
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A5 context mode a b c d e f z) _ 2 hmode hf
    (selectLegacy0OpcodeA5_run_of_rep_movsd_f2 context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With REX.W and `F2`, in 64-bit mode: form 3, `REP_MOVSQ_1`. -/
theorem selectLegacy0OpcodeA5_run_of_rep_movsq_f2 (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 242)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A5 context true a b c d e f 0 = .ok 3 := by
  simp [Select_Legacy_0_Opcode_A5, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A5` decoder in that context runs `REP_MOVSQ_1` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA5_run_of_rep_movsq_f2 [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 242)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A5 ip context).run s =
      (X86.Instructions.REP_MOVSQ_1 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A5
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A5 context mode a b c d e f z) _ 3 hmode hf
    (selectLegacy0OpcodeA5_run_of_rep_movsq_f2 context hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `66`, REX.W clear and `F2`, in 64-bit mode: form 4, `REP_MOVSW_5`. -/
theorem selectLegacy0OpcodeA5_run_of_rep_movsw_f2 (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 242)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A5 context true a b c d e f 0 = .ok 4 := by
  simp [Select_Legacy_0_Opcode_A5, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A5` decoder in that context runs `REP_MOVSW_5` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA5_run_of_rep_movsw_f2 [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 242)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A5 ip context).run s =
      (X86.Instructions.REP_MOVSW_5 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A5
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A5 context mode a b c d e f z) _ 4 hmode hf
    (selectLegacy0OpcodeA5_run_of_rep_movsw_f2 context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

end X86Proofs
