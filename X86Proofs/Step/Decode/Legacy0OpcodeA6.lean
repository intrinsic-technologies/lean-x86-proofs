import X86Proofs.Step.Decode

/-!
# Opcode `A6`: `CMPSB`, `REPE CMPSB`, `REPNE CMPSB`

The one place that looks inside lean-x86's opcode-`A6` decoder (`Decode_Legacy_0_Opcode_A6`) and its
form selection (`Select_Legacy_0_Opcode_A6`), architecture rule 5. In 64-bit mode the selection
picks `CMPSB` without a REP prefix (`Instructions/Cmps/Generated/Str`) and `REPE_CMPSB` after `F3`
(`Instructions/Cmps/Generated/Repe`) and `REPNE_CMPSB` after `F2`
(`Instructions/Cmps/Generated/Repne`). For each form, a `selectLegacy0OpcodeA6_run_of_…` lemma gives
the index the selection picks and a `decodeLegacy0OpcodeA6_run_of_…` lemma runs the decoder to the
call of that form at `ip + 1` (no ModRM byte). The dispatch to this decoder is
`decodeLegacy0_run_of_opcodeA6` (`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- Without a REP prefix, in 64-bit mode: form 1, `CMPSB`. -/
theorem selectLegacy0OpcodeA6_run_of_cmpsb (context : Instruction_Context)
    (hrep : context.rep_prefix = 0)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A6 context true a b c d e f 0 = .ok 1 := by
  simp [Select_Legacy_0_Opcode_A6, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A6` decoder without a REP prefix runs `CMPSB` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA6_run_of_cmpsb [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A6 ip context).run s =
      (X86.Instructions.CMPSB (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A6
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A6 context mode a b c d e f z) _ 1 hmode hf
    (selectLegacy0OpcodeA6_run_of_cmpsb context hrep)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `F3`, in 64-bit mode: form 2, `REPE_CMPSB`. -/
theorem selectLegacy0OpcodeA6_run_of_repe_cmpsb (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A6 context true a b c d e f 0 = .ok 2 := by
  simp [Select_Legacy_0_Opcode_A6, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A6` decoder with `F3` runs `REPE_CMPSB` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA6_run_of_repe_cmpsb [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A6 ip context).run s =
      (X86.Instructions.REPE_CMPSB (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A6
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A6 context mode a b c d e f z) _ 2 hmode hf
    (selectLegacy0OpcodeA6_run_of_repe_cmpsb context hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `F2`, in 64-bit mode: form 3, `REPNE_CMPSB`. -/
theorem selectLegacy0OpcodeA6_run_of_repne_cmpsb (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_A6 context true a b c d e f 0 = .ok 3 := by
  simp [Select_Legacy_0_Opcode_A6, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`A6` decoder in that context runs `REPNE_CMPSB` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0OpcodeA6_run_of_repne_cmpsb [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 242)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A6 ip context).run s =
      (X86.Instructions.REPNE_CMPSB (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A6
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A6 context mode a b c d e f z) _ 3 hmode hf
    (selectLegacy0OpcodeA6_run_of_repne_cmpsb context hrep)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

end X86Proofs
