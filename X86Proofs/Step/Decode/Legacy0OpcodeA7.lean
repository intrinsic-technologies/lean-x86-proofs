import X86Proofs.Step.Decode

/-!
# Opcode `A7`: `CMPSW`, `CMPSD`, `CMPSQ` and their REPE and REPNE forms

The one place that looks inside lean-x86's opcode-`A7` decoder (`Decode_Legacy_0_Opcode_A7`) and its
form selection (`Select_Legacy_0_Opcode_A7`), architecture rule 5. In 64-bit mode the selection
picks the form by the operand size (REX.W, else `66`) and the REP prefix: `CMPSW`, `CMPSD`, `CMPSQ`
without one (`Instructions/Cmps/Generated/Str`), `REPE_CMPSW`, `REPE_CMPSD`, `REPE_CMPSQ` after `F3`
(`Instructions/Cmps/Generated/Repe`), `REPNE_CMPSW`, `REPNE_CMPSD`, `REPNE_CMPSQ` after `F2`
(`Instructions/Cmps/Generated/Repne`). For each form, a `selectLegacy0OpcodeA7_run_of_…` lemma gives
the index the selection picks and a `decodeLegacy0OpcodeA7_run_of_…` lemma runs the decoder to the
call of that form at `ip + 1` (no ModRM byte). The dispatch to this decoder is
`decodeLegacy0_run_of_opcodeA7` (`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `66`, REX.W clear and no REP prefix: form 1, `CMPSW`. -/
theorem selectLegacy0OpcodeA7_run_of_cmpsw (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A7 context true a b c d e f 0 = .ok 1 := by
  simp [Select_Legacy_0_Opcode_A7, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A7` decoder in that context runs `CMPSW` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA7_run_of_cmpsw [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A7 ip context).run s =
      (X86.Instructions.CMPSW (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A7
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A7 context mode a b c d e f z) _ 1 hmode hf
    (selectLegacy0OpcodeA7_run_of_cmpsw context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- Without `66`, REX.W or a REP prefix: form 2, `CMPSD`. -/
theorem selectLegacy0OpcodeA7_run_of_cmpsd (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A7 context true a b c d e f 0 = .ok 2 := by
  simp [Select_Legacy_0_Opcode_A7, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A7` decoder in that context runs `CMPSD` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA7_run_of_cmpsd [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A7 ip context).run s =
      (X86.Instructions.CMPSD (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A7
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A7 context mode a b c d e f z) _ 2 hmode hf
    (selectLegacy0OpcodeA7_run_of_cmpsd context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With REX.W and no REP prefix: form 3, `CMPSQ`. -/
theorem selectLegacy0OpcodeA7_run_of_cmpsq (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 0)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A7 context true a b c d e f 0 = .ok 3 := by
  simp [Select_Legacy_0_Opcode_A7, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A7` decoder in that context runs `CMPSQ` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA7_run_of_cmpsq [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A7 ip context).run s =
      (X86.Instructions.CMPSQ (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A7
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A7 context mode a b c d e f z) _ 3 hmode hf
    (selectLegacy0OpcodeA7_run_of_cmpsq context hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `66`, REX.W clear and `F3`: form 4, `REPE_CMPSW`. -/
theorem selectLegacy0OpcodeA7_run_of_repe_cmpsw (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 243)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A7 context true a b c d e f 0 = .ok 4 := by
  simp [Select_Legacy_0_Opcode_A7, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A7` decoder in that context runs `REPE_CMPSW` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA7_run_of_repe_cmpsw [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A7 ip context).run s =
      (X86.Instructions.REPE_CMPSW (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A7
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A7 context mode a b c d e f z) _ 4 hmode hf
    (selectLegacy0OpcodeA7_run_of_repe_cmpsw context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `F3`, without `66` or REX.W: form 5, `REPE_CMPSD`. -/
theorem selectLegacy0OpcodeA7_run_of_repe_cmpsd (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 243)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A7 context true a b c d e f 0 = .ok 5 := by
  simp [Select_Legacy_0_Opcode_A7, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A7` decoder in that context runs `REPE_CMPSD` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA7_run_of_repe_cmpsd [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A7 ip context).run s =
      (X86.Instructions.REPE_CMPSD (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A7
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A7 context mode a b c d e f z) _ 5 hmode hf
    (selectLegacy0OpcodeA7_run_of_repe_cmpsd context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With REX.W and `F3`: form 6, `REPE_CMPSQ`. -/
theorem selectLegacy0OpcodeA7_run_of_repe_cmpsq (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 243)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A7 context true a b c d e f 0 = .ok 6 := by
  simp [Select_Legacy_0_Opcode_A7, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A7` decoder in that context runs `REPE_CMPSQ` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA7_run_of_repe_cmpsq [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A7 ip context).run s =
      (X86.Instructions.REPE_CMPSQ (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A7
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A7 context mode a b c d e f z) _ 6 hmode hf
    (selectLegacy0OpcodeA7_run_of_repe_cmpsq context hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `66`, REX.W clear and `F2`, in 64-bit mode: form 7, `REPNE_CMPSW`. -/
theorem selectLegacy0OpcodeA7_run_of_repne_cmpsw (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 242)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A7 context true a b c d e f 0 = .ok 7 := by
  simp [Select_Legacy_0_Opcode_A7, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A7` decoder in that context runs `REPNE_CMPSW` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA7_run_of_repne_cmpsw [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 242)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A7 ip context).run s =
      (X86.Instructions.REPNE_CMPSW (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A7
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A7 context mode a b c d e f z) _ 7 hmode hf
    (selectLegacy0OpcodeA7_run_of_repne_cmpsw context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `F2`, without `66` or REX.W, in 64-bit mode: form 8, `REPNE_CMPSD`. -/
theorem selectLegacy0OpcodeA7_run_of_repne_cmpsd (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 242)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A7 context true a b c d e f 0 = .ok 8 := by
  simp [Select_Legacy_0_Opcode_A7, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A7` decoder in that context runs `REPNE_CMPSD` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA7_run_of_repne_cmpsd [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 242)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A7 ip context).run s =
      (X86.Instructions.REPNE_CMPSD (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A7
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A7 context mode a b c d e f z) _ 8 hmode hf
    (selectLegacy0OpcodeA7_run_of_repne_cmpsd context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With REX.W and `F2`, in 64-bit mode: form 9, `REPNE_CMPSQ`. -/
theorem selectLegacy0OpcodeA7_run_of_repne_cmpsq (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 242)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A7 context true a b c d e f 0 = .ok 9 := by
  simp [Select_Legacy_0_Opcode_A7, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A7` decoder in that context runs `REPNE_CMPSQ` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA7_run_of_repne_cmpsq [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 242)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A7 ip context).run s =
      (X86.Instructions.REPNE_CMPSQ (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A7
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A7 context mode a b c d e f z) _ 9 hmode hf
    (selectLegacy0OpcodeA7_run_of_repne_cmpsq context hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

end X86Proofs
