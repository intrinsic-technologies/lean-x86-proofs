import X86Proofs.Step.Decode

/-!
# Opcode `AD`: `LODSW`, `LODSD`, `LODSQ` and their REP forms

The one place that looks inside lean-x86's opcode-`AD` decoder (`Decode_Legacy_0_Opcode_AD`) and its
form selection (`Select_Legacy_0_Opcode_AD`), architecture rule 5. In 64-bit mode the selection
picks the form by the operand size (REX.W, else `66`) and the REP prefix: `LODSQ`, `LODSW_2`,
`LODSD_2` without one (`Instructions/Lods/Generated/Str`), `REP_LODSQ_0`, `REP_LODSW_2`,
`REP_LODSD_2` after `F3` (`Instructions/Lods/Generated/Rep`), `REP_LODSQ_1`, `REP_LODSW_5`,
`REP_LODSD_5` after `F2` (the same operations; `Instructions/Lods/Generated/RepF2`). For each form,
a `selectLegacy0OpcodeAD_run_of_…` lemma gives the index the selection picks and a
`decodeLegacy0OpcodeAD_run_of_…` lemma runs the decoder to the call of that form at `ip + 1` (no
ModRM byte). The dispatch to this decoder is `decodeLegacy0_run_of_opcodeAD`
(`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With REX.W and no REP prefix: form 7, `LODSQ`. -/
theorem selectLegacy0OpcodeAD_run_of_lodsq (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 0)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AD context true a b c d e f 0 = .ok 7 := by
  simp [Select_Legacy_0_Opcode_AD, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AD` decoder in that context runs `LODSQ` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAD_run_of_lodsq [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AD ip context).run s =
      (X86.Instructions.LODSQ (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AD
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AD context mode a b c d e f z) _ 7 hmode hf
    (selectLegacy0OpcodeAD_run_of_lodsq context hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- Without `66`, REX.W or a REP prefix: form 9, `LODSD_2`. -/
theorem selectLegacy0OpcodeAD_run_of_lodsd (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AD context true a b c d e f 0 = .ok 9 := by
  simp [Select_Legacy_0_Opcode_AD, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AD` decoder in that context runs `LODSD_2` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAD_run_of_lodsd [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AD ip context).run s =
      (X86.Instructions.LODSD_2 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AD
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AD context mode a b c d e f z) _ 9 hmode hf
    (selectLegacy0OpcodeAD_run_of_lodsd context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `66`, REX.W clear and no REP prefix: form 8, `LODSW_2`. -/
theorem selectLegacy0OpcodeAD_run_of_lodsw (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AD context true a b c d e f 0 = .ok 8 := by
  simp [Select_Legacy_0_Opcode_AD, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AD` decoder in that context runs `LODSW_2` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAD_run_of_lodsw [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AD ip context).run s =
      (X86.Instructions.LODSW_2 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AD
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AD context mode a b c d e f z) _ 8 hmode hf
    (selectLegacy0OpcodeAD_run_of_lodsw context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With REX.W and `F3`: form 5, `REP_LODSQ_0`. -/
theorem selectLegacy0OpcodeAD_run_of_rep_lodsq (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 243)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AD context true a b c d e f 0 = .ok 5 := by
  simp [Select_Legacy_0_Opcode_AD, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AD` decoder in that context runs `REP_LODSQ_0` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAD_run_of_rep_lodsq [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AD ip context).run s =
      (X86.Instructions.REP_LODSQ_0 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AD
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AD context mode a b c d e f z) _ 5 hmode hf
    (selectLegacy0OpcodeAD_run_of_rep_lodsq context hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- Without `66` or REX.W, with `F3`: form 4, `REP_LODSD_2`. -/
theorem selectLegacy0OpcodeAD_run_of_rep_lodsd (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 243)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AD context true a b c d e f 0 = .ok 4 := by
  simp [Select_Legacy_0_Opcode_AD, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AD` decoder in that context runs `REP_LODSD_2` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAD_run_of_rep_lodsd [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AD ip context).run s =
      (X86.Instructions.REP_LODSD_2 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AD
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AD context mode a b c d e f z) _ 4 hmode hf
    (selectLegacy0OpcodeAD_run_of_rep_lodsd context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `66`, REX.W clear and `F3`: form 6, `REP_LODSW_2`. -/
theorem selectLegacy0OpcodeAD_run_of_rep_lodsw (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 243)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AD context true a b c d e f 0 = .ok 6 := by
  simp [Select_Legacy_0_Opcode_AD, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AD` decoder in that context runs `REP_LODSW_2` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAD_run_of_rep_lodsw [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AD ip context).run s =
      (X86.Instructions.REP_LODSW_2 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AD
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AD context mode a b c d e f z) _ 6 hmode hf
    (selectLegacy0OpcodeAD_run_of_rep_lodsw context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `F2`, without `66` or REX.W, in 64-bit mode: form 1, `REP_LODSD_5`. -/
theorem selectLegacy0OpcodeAD_run_of_rep_lodsd_f2 (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 242)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AD context true a b c d e f 0 = .ok 1 := by
  simp [Select_Legacy_0_Opcode_AD, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AD` decoder in that context runs `REP_LODSD_5` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAD_run_of_rep_lodsd_f2 [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 242)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AD ip context).run s =
      (X86.Instructions.REP_LODSD_5 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AD
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AD context mode a b c d e f z) _ 1 hmode hf
    (selectLegacy0OpcodeAD_run_of_rep_lodsd_f2 context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With REX.W and `F2`, in 64-bit mode: form 2, `REP_LODSQ_1`. -/
theorem selectLegacy0OpcodeAD_run_of_rep_lodsq_f2 (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 242)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AD context true a b c d e f 0 = .ok 2 := by
  simp [Select_Legacy_0_Opcode_AD, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AD` decoder in that context runs `REP_LODSQ_1` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAD_run_of_rep_lodsq_f2 [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 242)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AD ip context).run s =
      (X86.Instructions.REP_LODSQ_1 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AD
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AD context mode a b c d e f z) _ 2 hmode hf
    (selectLegacy0OpcodeAD_run_of_rep_lodsq_f2 context hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `66`, REX.W clear and `F2`, in 64-bit mode: form 3, `REP_LODSW_5`. -/
theorem selectLegacy0OpcodeAD_run_of_rep_lodsw_f2 (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 242)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AD context true a b c d e f 0 = .ok 3 := by
  simp [Select_Legacy_0_Opcode_AD, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AD` decoder in that context runs `REP_LODSW_5` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAD_run_of_rep_lodsw_f2 [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 242)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AD ip context).run s =
      (X86.Instructions.REP_LODSW_5 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AD
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AD context mode a b c d e f z) _ 3 hmode hf
    (selectLegacy0OpcodeAD_run_of_rep_lodsw_f2 context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

end X86Proofs
