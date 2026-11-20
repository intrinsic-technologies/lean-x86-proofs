import X86Proofs.Step.Decode

/-!
# Opcode `90`: `NOP`, `XCHG r8, rAX`, `PAUSE`

The one place that looks inside lean-x86's opcode-`90` decoder (`Decode_Legacy_0_Opcode_90`) and its
form selection (`Select_Legacy_0_Opcode_90`), architecture rule 5. `90` has no ModRM byte; the
selection picks `XCHG_GPRv_OrAX_0` with REX.B (`xchg r8, rAX`, `Instructions/Xchg/Generated/Acc`),
`NOP_90` without REX.B (`Instructions/Nop`), each without a REP prefix, and `PAUSE` after `F3`
(`Instructions/Pause`). The decoder lemmas run it to the call of the form at `ip + 1`.

The dispatch to this decoder is `decodeLegacy0_run_of_opcode90` (`Step/Decode/Legacy0.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- Without REP and REX.B in 64-bit mode, opcode 90's form selection picks form 2, `NOP_90`. -/
theorem selectLegacy0Opcode90_run_of_nop (context : Instruction_Context)
    (hrep : context.rep_prefix = 0) (hb : context.rex_b3 = 0) (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_90 context true a b c d e f 0 = .ok 2 := by
  simp [Select_Legacy_0_Opcode_90, hrep, hb, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`90` decoder without REP and REX.B runs `NOP_90` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0Opcode90_run_of_nop [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (op : BitVec 8) (hrep : context.rep_prefix = 0)
    (hb : context.rex_b3 = 0) (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_90 ip context op).run s =
      (X86.Instructions.NOP_90 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_90
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_90 context mode a b c d e f z) _ 2 hmode hf
    (selectLegacy0Opcode90_run_of_nop context hrep hb)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With REX.B and no REP prefix in 64-bit mode, opcode 90's form selection picks form 1,
`XCHG_GPRv_OrAX_0`. -/
theorem selectLegacy0Opcode90_run_of_xchg (context : Instruction_Context)
    (hrep : context.rep_prefix = 0) (hb : context.rex_b3 = 1) (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_90 context true a b c d e f 0 = .ok 1 := by
  simp [Select_Legacy_0_Opcode_90, hrep, hb, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`90` decoder with REX.B and no REP prefix runs `XCHG_GPRv_OrAX_0` with the opcode
byte and `Next_IP = ip + 1`. -/
theorem decodeLegacy0Opcode90_run_of_xchg [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (op : BitVec 8) (hrep : context.rep_prefix = 0)
    (hb : context.rex_b3 = 1) (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_90 ip context op).run s =
      (X86.Instructions.XCHG_GPRv_OrAX_0 (BitVec.add ip 1#64) context op).run s := by
  unfold Decode_Legacy_0_Opcode_90
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_90 context mode a b c d e f z) _ 1 hmode hf
    (selectLegacy0Opcode90_run_of_xchg context hrep hb)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- With `F3` in 64-bit mode, opcode 90's form selection picks form 3, `PAUSE`. -/
theorem selectLegacy0Opcode90_run_of_pause (context : Instruction_Context)
    (hrep : context.rep_prefix = 243) (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_90 context true a b c d e f 0 = .ok 3 := by
  simp [Select_Legacy_0_Opcode_90, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

/-- The opcode-`90` decoder with `F3` runs `PAUSE` with `Next_IP = ip + 1`. -/
theorem decodeLegacy0Opcode90_run_of_pause [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (op : BitVec 8) (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_90 ip context op).run s =
      (X86.Instructions.PAUSE (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_90
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_90 context mode a b c d e f z) _ 3 hmode hf
    (selectLegacy0Opcode90_run_of_pause context hrep)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

end X86Proofs
