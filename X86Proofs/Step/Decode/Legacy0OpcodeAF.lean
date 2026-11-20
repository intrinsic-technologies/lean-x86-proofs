import X86Proofs.Step.Decode

/-!
# Opcode `AF`: `SCASW`, `SCASD`, `SCASQ` and their REPE and REPNE forms

The one place that looks inside lean-x86's opcode-`AF` decoder (`Decode_Legacy_0_Opcode_AF`) and its
form selection (`Select_Legacy_0_Opcode_AF`), architecture rule 5. The decoder may diverge
(`PartialSpecM`: the `REPE`/`REPNE` forms loop), so the selection runs through
`decoderSelect_run_noModRM_partial`; the one-iteration forms are total and run through `liftTotal`.
In 64-bit mode the selection picks the form by the operand size (REX.W, else `66`) and the REP
prefix: `SCASQ`, `SCASW_2`, `SCASD_2` without one (`Instructions/Scas/Generated/Str`), `REPE_SCASQ`,
`REPE_SCASW_2`, `REPE_SCASD_2` after `F3` (`Instructions/Scas/Generated/Repe`), `REPNE_SCASQ`,
`REPNE_SCASW_2`, `REPNE_SCASD_2` after `F2` (`Instructions/Scas/Generated/Repne`). For each form, a
`selectLegacy0OpcodeAF_run_of_…` lemma gives the index the selection picks and a
`decodeLegacy0OpcodeAF_run_of_…` lemma runs the decoder to the call of that form at `ip + 1` (no
ModRM byte). The dispatch to this decoder is `decodeLegacy0_run_of_opcodeAF`
(`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With REX.W and no REP prefix: form 7, `SCASQ`. -/
theorem selectLegacy0OpcodeAF_run_of_scasq (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 0)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AF context true a b c d e f 0 = .ok 7 := by
  simp [Select_Legacy_0_Opcode_AF, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AF` decoder in that context runs `SCASQ` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAF_run_of_scasq [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AF ip context).run s =
      some ((X86.Instructions.SCASQ (BitVec.add ip 1#64) context).run s) := by
  unfold Decode_Legacy_0_Opcode_AF
  refine (decoderSelect_run_noModRM_partial s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AF context mode a b c d e f z) _ 7 hmode hf
    (selectLegacy0OpcodeAF_run_of_scasq context hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact partialSpecM_liftTotal_bind_pure_unit_run _ s

/-- With `66`, REX.W clear and no REP prefix: form 8, `SCASW_2`. -/
theorem selectLegacy0OpcodeAF_run_of_scasw (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AF context true a b c d e f 0 = .ok 8 := by
  simp [Select_Legacy_0_Opcode_AF, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AF` decoder in that context runs `SCASW_2` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAF_run_of_scasw [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AF ip context).run s =
      some ((X86.Instructions.SCASW_2 (BitVec.add ip 1#64) context).run s) := by
  unfold Decode_Legacy_0_Opcode_AF
  refine (decoderSelect_run_noModRM_partial s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AF context mode a b c d e f z) _ 8 hmode hf
    (selectLegacy0OpcodeAF_run_of_scasw context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact partialSpecM_liftTotal_bind_pure_unit_run _ s

/-- Without `66`, REX.W or a REP prefix: form 9, `SCASD_2`. -/
theorem selectLegacy0OpcodeAF_run_of_scasd (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AF context true a b c d e f 0 = .ok 9 := by
  simp [Select_Legacy_0_Opcode_AF, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AF` decoder in that context runs `SCASD_2` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAF_run_of_scasd [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AF ip context).run s =
      some ((X86.Instructions.SCASD_2 (BitVec.add ip 1#64) context).run s) := by
  unfold Decode_Legacy_0_Opcode_AF
  refine (decoderSelect_run_noModRM_partial s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AF context mode a b c d e f z) _ 9 hmode hf
    (selectLegacy0OpcodeAF_run_of_scasd context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact partialSpecM_liftTotal_bind_pure_unit_run _ s

/-- With REX.W and `F3`: form 5, `REPE_SCASQ`. -/
theorem selectLegacy0OpcodeAF_run_of_repe_scasq (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 243)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AF context true a b c d e f 0 = .ok 5 := by
  simp [Select_Legacy_0_Opcode_AF, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AF` decoder in that context runs `REPE_SCASQ` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAF_run_of_repe_scasq [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AF ip context).run s =
      (X86.Instructions.REPE_SCASQ (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AF
  refine (decoderSelect_run_noModRM_partial s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AF context mode a b c d e f z) _ 5 hmode hf
    (selectLegacy0OpcodeAF_run_of_repe_scasq context hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact partialSpecM_bind_pure_unit_run _ s

/-- With `66`, REX.W clear and `F3`: form 6, `REPE_SCASW_2`. -/
theorem selectLegacy0OpcodeAF_run_of_repe_scasw (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 243)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AF context true a b c d e f 0 = .ok 6 := by
  simp [Select_Legacy_0_Opcode_AF, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AF` decoder in that context runs `REPE_SCASW_2` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAF_run_of_repe_scasw [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AF ip context).run s =
      (X86.Instructions.REPE_SCASW_2 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AF
  refine (decoderSelect_run_noModRM_partial s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AF context mode a b c d e f z) _ 6 hmode hf
    (selectLegacy0OpcodeAF_run_of_repe_scasw context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact partialSpecM_bind_pure_unit_run _ s

/-- With `F3`, without `66` or REX.W: form 4, `REPE_SCASD_2`. -/
theorem selectLegacy0OpcodeAF_run_of_repe_scasd (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 243)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AF context true a b c d e f 0 = .ok 4 := by
  simp [Select_Legacy_0_Opcode_AF, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AF` decoder in that context runs `REPE_SCASD_2` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAF_run_of_repe_scasd [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AF ip context).run s =
      (X86.Instructions.REPE_SCASD_2 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AF
  refine (decoderSelect_run_noModRM_partial s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AF context mode a b c d e f z) _ 4 hmode hf
    (selectLegacy0OpcodeAF_run_of_repe_scasd context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact partialSpecM_bind_pure_unit_run _ s

/-- With `F2`, without `66` or REX.W, in 64-bit mode: form 1, `REPNE_SCASD_2`. -/
theorem selectLegacy0OpcodeAF_run_of_repne_scasd (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 242)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AF context true a b c d e f 0 = .ok 1 := by
  simp [Select_Legacy_0_Opcode_AF, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AF` decoder in that context runs `REPNE_SCASD_2` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAF_run_of_repne_scasd [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 242)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AF ip context).run s =
      (X86.Instructions.REPNE_SCASD_2 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AF
  refine (decoderSelect_run_noModRM_partial s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AF context mode a b c d e f z) _ 1 hmode hf
    (selectLegacy0OpcodeAF_run_of_repne_scasd context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact partialSpecM_bind_pure_unit_run _ s

/-- With REX.W and `F2`, in 64-bit mode: form 2, `REPNE_SCASQ`. -/
theorem selectLegacy0OpcodeAF_run_of_repne_scasq (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 242)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AF context true a b c d e f 0 = .ok 2 := by
  simp [Select_Legacy_0_Opcode_AF, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AF` decoder in that context runs `REPNE_SCASQ` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAF_run_of_repne_scasq [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hrep : context.rep_prefix = 242)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AF ip context).run s =
      (X86.Instructions.REPNE_SCASQ (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AF
  refine (decoderSelect_run_noModRM_partial s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AF context mode a b c d e f z) _ 2 hmode hf
    (selectLegacy0OpcodeAF_run_of_repne_scasq context hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact partialSpecM_bind_pure_unit_run _ s

/-- With `66`, REX.W clear and `F2`, in 64-bit mode: form 3, `REPNE_SCASW_2`. -/
theorem selectLegacy0OpcodeAF_run_of_repne_scasw (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 242)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AF context true a b c d e f 0 = .ok 3 := by
  simp [Select_Legacy_0_Opcode_AF, hosz, hw, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AF` decoder in that context runs `REPNE_SCASW_2` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAF_run_of_repne_scasw [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true)
    (hw : context.rex_w = 0)
    (hrep : context.rep_prefix = 242)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AF ip context).run s =
      (X86.Instructions.REPNE_SCASW_2 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AF
  refine (decoderSelect_run_noModRM_partial s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AF context mode a b c d e f z) _ 3 hmode hf
    (selectLegacy0OpcodeAF_run_of_repne_scasw context hosz hw hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact partialSpecM_bind_pure_unit_run _ s

end X86Proofs
