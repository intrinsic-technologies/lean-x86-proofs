import X86Proofs.Step.Decode

/-!
# Opcodes `91`–`97`: `XCHG r, rAX`

The one place that looks inside lean-x86's opcode-`91` decoder (`Decode_Legacy_0_Opcode_91`) and its
form selection (`Select_Legacy_0_Opcode_91`), architecture rule 5. The decoders of `92`–`97` are
copies of it (equal by `rfl`), so the dispatch `decodeLegacy0_run_of_opcode91to97`
(`Step/Decode/Legacy0.lean`) sends all seven to this one, with the opcode byte. In 64-bit mode the
selection always picks `XCHG_GPRv_OrAX_0` (`Instructions/Xchg/Generated/Acc`), which takes the
register from the opcode's low three bits (extended by REX.B); the decoder runs it at `ip + 1`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- In 64-bit mode opcode 91's form selection picks form 1, `XCHG_GPRv_OrAX_0`. -/
theorem selectLegacy0Opcode91_run_of_xchg (context : Instruction_Context) (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_91 context true a b c d e f 0 = .ok 1 := by
  simp [Select_Legacy_0_Opcode_91]
  rfl

/-- The opcode-`91` decoder runs `XCHG_GPRv_OrAX_0` with the opcode byte and `Next_IP = ip + 1`. -/
theorem decodeLegacy0Opcode91_run_of_xchg [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (op : BitVec 8) (hmode : In64BitMode s)
    (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_91 ip context op).run s =
      (X86.Instructions.XCHG_GPRv_OrAX_0 (BitVec.add ip 1#64) context op).run s := by
  unfold Decode_Legacy_0_Opcode_91
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_91 context mode a b c d e f z) _ 1 hmode hf
    (selectLegacy0Opcode91_run_of_xchg context)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

end X86Proofs
