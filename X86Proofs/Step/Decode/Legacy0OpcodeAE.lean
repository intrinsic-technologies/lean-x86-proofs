import X86Proofs.Step.Decode

/-!
# Opcode `AE`: `SCASB`, `REPE SCASB`, `REPNE SCASB`

The one place that looks inside lean-x86's opcode-`AE` decoder (`Decode_Legacy_0_Opcode_AE`) and its
form selection (`Select_Legacy_0_Opcode_AE`), architecture rule 5. The decoder may diverge
(`PartialSpecM`: the `REPE`/`REPNE` forms loop), so the selection runs through
`decoderSelect_run_noModRM_partial`; the one-iteration forms are total and run through `liftTotal`.
In 64-bit mode the selection picks `SCASB` without a REP prefix (`Instructions/Scas/Generated/Str`),
`REPE_SCASB` after `F3` (`Instructions/Scas/Generated/Repe`) and `REPNE_SCASB` after `F2`
(`Instructions/Scas/Generated/Repne`). For each form, a `selectLegacy0OpcodeAE_run_of_…` lemma gives
the index the selection picks and a `decodeLegacy0OpcodeAE_run_of_…` lemma runs the decoder to the
call of that form at `ip + 1` (no ModRM byte). The dispatch to this decoder is
`decodeLegacy0_run_of_opcodeAE` (`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- Without a REP prefix, in 64-bit mode: form 3, `SCASB`. -/
theorem selectLegacy0OpcodeAE_run_of_scasb (context : Instruction_Context)
    (hrep : context.rep_prefix = 0)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AE context true a b c d e f 0 = .ok 3 := by
  simp [Select_Legacy_0_Opcode_AE, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AE` decoder without a REP prefix runs `SCASB` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAE_run_of_scasb [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AE ip context).run s =
      some ((X86.Instructions.SCASB (BitVec.add ip 1#64) context).run s) := by
  unfold Decode_Legacy_0_Opcode_AE
  refine (decoderSelect_run_noModRM_partial s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AE context mode a b c d e f z) _ 3 hmode hf
    (selectLegacy0OpcodeAE_run_of_scasb context hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact partialSpecM_liftTotal_bind_pure_unit_run _ s

/-- With `F3`, in 64-bit mode: form 2, `REPE_SCASB`. -/
theorem selectLegacy0OpcodeAE_run_of_repe_scasb (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AE context true a b c d e f 0 = .ok 2 := by
  simp [Select_Legacy_0_Opcode_AE, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AE` decoder with `F3` runs `REPE_SCASB` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAE_run_of_repe_scasb [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AE ip context).run s =
      (X86.Instructions.REPE_SCASB (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AE
  refine (decoderSelect_run_noModRM_partial s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AE context mode a b c d e f z) _ 2 hmode hf
    (selectLegacy0OpcodeAE_run_of_repe_scasb context hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact partialSpecM_bind_pure_unit_run _ s

/-- With `F2`, in 64-bit mode: form 1, `REPNE_SCASB`. -/
theorem selectLegacy0OpcodeAE_run_of_repne_scasb (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AE context true a b c d e f 0 = .ok 1 := by
  simp [Select_Legacy_0_Opcode_AE, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`AE` decoder in that context runs `REPNE_SCASB` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeAE_run_of_repne_scasb [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AE ip context).run s =
      (X86.Instructions.REPNE_SCASB (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AE
  refine (decoderSelect_run_noModRM_partial s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AE context mode a b c d e f z) _ 1 hmode hf
    (selectLegacy0OpcodeAE_run_of_repne_scasb context hrep)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact partialSpecM_bind_pure_unit_run _ s

end X86Proofs
