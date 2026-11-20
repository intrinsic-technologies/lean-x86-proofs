import X86Proofs.Step.Decode

/-!
# Opcodes `0F C8`–`0F CF`: `BSWAP r`

The one place that looks inside lean-x86's opcode-`C8` decoder (`Decode_Legacy_1_Opcode_C8`) and
its form selection (`Select_Legacy_1_Opcode_C8`), architecture rule 5. The decoders of `C9`–`CF`
are copies of it (equal by `rfl`), and `Decode_Legacy_1` hands each the opcode byte, so the
dispatch `decodeLegacy1_run_of_bswapOpcode` (`Step/Escape.lean`) sends all eight to this one. In
64-bit mode the selection always picks `BSWAP_GPRv` (`Instructions/Bswap/Generated/R`), which
takes the register from the opcode's low three bits (extended by REX.B); the decoder runs it at
`ip + 1`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- In 64-bit mode opcode C8's form selection picks form 1, `BSWAP_GPRv`. -/
theorem selectLegacy1OpcodeC8_run_of_bswap (context : Instruction_Context) (a b c d e f : Bool) :
    Select_Legacy_1_Opcode_C8 context true a b c d e f 0 = .ok 1 := by
  simp [Select_Legacy_1_Opcode_C8]
  rfl

/-- The opcode-`C8` decoder runs `BSWAP_GPRv` with the opcode byte and `Next_IP = ip + 1`. -/
theorem decodeLegacy1OpcodeC8_run_of_bswap [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (op : BitVec 8) (hmode : In64BitMode s)
    (hf : DecoderFeatures s) :
    (Decode_Legacy_1_Opcode_C8 ip context op).run s =
      (X86.Instructions.BSWAP_GPRv (BitVec.add ip 1#64) context op).run s := by
  unfold Decode_Legacy_1_Opcode_C8
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_1_Opcode_C8 context mode a b c d e f z) _ 1 hmode hf
    (selectLegacy1OpcodeC8_run_of_bswap context)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

end X86Proofs
