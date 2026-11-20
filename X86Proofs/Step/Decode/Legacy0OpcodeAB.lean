import X86Proofs.Step.Decode

/-!
# Opcode `AB`: `STOSW`, `STOSD`, `STOSQ` and their REP forms

The one place that looks inside lean-x86's opcode-`AB` decoder (`Decode_Legacy_0_Opcode_AB`) and its
form selection (`Select_Legacy_0_Opcode_AB`), architecture rule 5. In 64-bit mode the selection
picks the form by the operand size (REX.W, else `66`) and the REP prefix: `STOSQ`, `STOSW_2`,
`STOSD_2` without one (`Instructions/Stos/Generated/Str`), `REP_STOSQ_0`, `REP_STOSW_2`,
`REP_STOSD_2` after `F3` (`Instructions/Stos/Generated/Rep`), `REP_STOSQ_1`, `REP_STOSW_5`,
`REP_STOSD_5` after `F2` (the same operations; `Instructions/Stos/Generated/RepF2`). For each form,
a `selectLegacy0OpcodeAB_run_of_…` lemma gives the index the selection picks and a
`decodeLegacy0OpcodeAB_run_of_…` lemma runs the decoder to the call of that form at `ip + 1` (no
ModRM byte). The dispatch to this decoder is `decodeLegacy0_run_of_opcodeAB`
(`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With REX.W and no REP prefix: form 7, `STOSQ`. -/
theorem selectLegacy0OpcodeAB_run_of_stosq (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 0)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AB context true a b c d e f 0 = .ok 7 := by
  simp [Select_Legacy_0_Opcode_AB, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AB` decoder in that context runs `STOSQ` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAB_run_of_stosq [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AB ip context).run s =
      (X86.Instructions.STOSQ (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AB
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AB context mode a b c d e f z) _ 7 hmode hf
    (selectLegacy0OpcodeAB_run_of_stosq context hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `66`, REX.W clear and no REP prefix: form 8, `STOSW_2`. -/
theorem selectLegacy0OpcodeAB_run_of_stosw (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AB context true a b c d e f 0 = .ok 8 := by
  simp [Select_Legacy_0_Opcode_AB, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AB` decoder in that context runs `STOSW_2` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAB_run_of_stosw [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AB ip context).run s =
      (X86.Instructions.STOSW_2 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AB
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AB context mode a b c d e f z) _ 8 hmode hf
    (selectLegacy0OpcodeAB_run_of_stosw context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- Without `66`, REX.W or a REP prefix: form 9, `STOSD_2`. -/
theorem selectLegacy0OpcodeAB_run_of_stosd (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AB context true a b c d e f 0 = .ok 9 := by
  simp [Select_Legacy_0_Opcode_AB, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AB` decoder in that context runs `STOSD_2` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAB_run_of_stosd [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AB ip context).run s =
      (X86.Instructions.STOSD_2 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AB
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AB context mode a b c d e f z) _ 9 hmode hf
    (selectLegacy0OpcodeAB_run_of_stosd context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With REX.W and `F3`: form 5, `REP_STOSQ_0`. -/
theorem selectLegacy0OpcodeAB_run_of_rep_stosq (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 243)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AB context true a b c d e f 0 = .ok 5 := by
  simp [Select_Legacy_0_Opcode_AB, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AB` decoder in that context runs `REP_STOSQ_0` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAB_run_of_rep_stosq [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AB ip context).run s =
      (X86.Instructions.REP_STOSQ_0 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AB
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AB context mode a b c d e f z) _ 5 hmode hf
    (selectLegacy0OpcodeAB_run_of_rep_stosq context hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `66`, REX.W clear and `F3`: form 6, `REP_STOSW_2`. -/
theorem selectLegacy0OpcodeAB_run_of_rep_stosw (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 243)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AB context true a b c d e f 0 = .ok 6 := by
  simp [Select_Legacy_0_Opcode_AB, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AB` decoder in that context runs `REP_STOSW_2` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAB_run_of_rep_stosw [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AB ip context).run s =
      (X86.Instructions.REP_STOSW_2 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AB
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AB context mode a b c d e f z) _ 6 hmode hf
    (selectLegacy0OpcodeAB_run_of_rep_stosw context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `F3`, without `66` or REX.W: form 4, `REP_STOSD_2`. -/
theorem selectLegacy0OpcodeAB_run_of_rep_stosd (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 243)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AB context true a b c d e f 0 = .ok 4 := by
  simp [Select_Legacy_0_Opcode_AB, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AB` decoder in that context runs `REP_STOSD_2` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAB_run_of_rep_stosd [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AB ip context).run s =
      (X86.Instructions.REP_STOSD_2 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AB
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AB context mode a b c d e f z) _ 4 hmode hf
    (selectLegacy0OpcodeAB_run_of_rep_stosd context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `F2`, without `66` or REX.W, in 64-bit mode: form 1, `REP_STOSD_5`. -/
theorem selectLegacy0OpcodeAB_run_of_rep_stosd_f2 (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 242)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AB context true a b c d e f 0 = .ok 1 := by
  simp [Select_Legacy_0_Opcode_AB, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AB` decoder in that context runs `REP_STOSD_5` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAB_run_of_rep_stosd_f2 [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 242)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AB ip context).run s =
      (X86.Instructions.REP_STOSD_5 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AB
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AB context mode a b c d e f z) _ 1 hmode hf
    (selectLegacy0OpcodeAB_run_of_rep_stosd_f2 context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With REX.W and `F2`, in 64-bit mode: form 2, `REP_STOSQ_1`. -/
theorem selectLegacy0OpcodeAB_run_of_rep_stosq_f2 (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 242)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AB context true a b c d e f 0 = .ok 2 := by
  simp [Select_Legacy_0_Opcode_AB, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AB` decoder in that context runs `REP_STOSQ_1` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAB_run_of_rep_stosq_f2 [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 242)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AB ip context).run s =
      (X86.Instructions.REP_STOSQ_1 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AB
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AB context mode a b c d e f z) _ 2 hmode hf
    (selectLegacy0OpcodeAB_run_of_rep_stosq_f2 context hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `66`, REX.W clear and `F2`, in 64-bit mode: form 3, `REP_STOSW_5`. -/
theorem selectLegacy0OpcodeAB_run_of_rep_stosw_f2 (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 242)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AB context true a b c d e f 0 = .ok 3 := by
  simp [Select_Legacy_0_Opcode_AB, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AB` decoder in that context runs `REP_STOSW_5` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAB_run_of_rep_stosw_f2 [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 242)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AB ip context).run s =
      (X86.Instructions.REP_STOSW_5 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AB
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AB context mode a b c d e f z) _ 3 hmode hf
    (selectLegacy0OpcodeAB_run_of_rep_stosw_f2 context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

end X86Proofs
