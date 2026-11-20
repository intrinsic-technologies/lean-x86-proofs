import X86Proofs.Step.Decode

/-!
# Opcode `0F A2`: `CPUID`

The one place that looks inside lean-x86's opcode-`A2` decoder (`Decode_Legacy_1_Opcode_A2`) and
its form selection (`Select_Legacy_1_Opcode_A2`), architecture rule 5. `A2` has no ModRM byte; in
64-bit mode the selection always picks `CPUID` (`Instructions/Cpuid`), which the decoder runs at
`ip + 1`. The dispatch to this decoder is `decodeLegacy1_run_of_opcodeA2` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- In 64-bit mode opcode A2's form selection picks form 1, `CPUID`. -/
theorem selectLegacy1OpcodeA2_run_of_cpuid (context : Instruction_Context) (a b c d e f : Bool) :
    Select_Legacy_1_Opcode_A2 context true a b c d e f 0 = .ok 1 := by
  simp [Select_Legacy_1_Opcode_A2]
  rfl

/-- The opcode-`A2` decoder runs `CPUID` with `Next_IP = ip + 1`. -/
theorem decodeLegacy1OpcodeA2_run_of_cpuid [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_1_Opcode_A2 ip context).run s =
      (X86.Instructions.CPUID (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_1_Opcode_A2
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_1_Opcode_A2 context mode a b c d e f z) _ 1 hmode hf
    (selectLegacy1OpcodeA2_run_of_cpuid context)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

end X86Proofs
