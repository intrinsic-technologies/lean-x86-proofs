import X86Proofs.Step.Escape
import X86Proofs.Step.FetchImm
import X86Proofs.Instructions.Branch.Form
import X86Proofs.Step.Decode.Legacy0

/-!
# Decoding the relative branches

- `Jcc rel8` (`70+cc`): `Decode_Legacy_0` dispatches each of the 16 opcodes to its decoder
  (`Decode_Legacy_0_Opcode_7x`), which selects `Jcc_RELBRb_0` in 64-bit mode. The 16 decoders and
  forms are copies, equal by `rfl` to the `JO` ones (`Decode_Legacy_0_Opcode_70`, `JO_RELBRb_0`),
  so `decodeLegacy0_run_of_jccOpcode8` (`Step/Decode/Legacy0.lean`) covers the dispatch for all 16
  at once, and `decodeLegacy0Opcode70_run_of_jcc` the decoder.
- `Jcc rel32` (`0F 80+cc`): the same through `Decode_Legacy_1` (`decodeLegacy1_run_of_jccOpcode32`
  in `Step/Escape.lean`, `decodeLegacy1Opcode80_run_of_jcc`; the form `JO_RELBRd_0`).
- `JMP rel8` (`EB`, `JMP_RELBRb_1`) and `JMP rel32` (`E9`, `JMP_RELBRd`): one opcode each
  (dispatch `decodeLegacy0_run_of_opcodeEB`, `decodeLegacy0_run_of_opcodeE9`).

The decoders hand the form the address of the displacement (opcode + 1), which the form fetches.
`decode_jcc_rel8`, `decode_jcc_rel32`, `decode_jmp_rel8`, `decode_jmp_rel32` start from the state
the step wrappers hand to the decoder.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The `Jcc rel8` decoder in 64-bit mode runs `JO_RELBRb_0` at `ip + 1` (the displacement). -/
theorem decodeLegacy0Opcode70_run_of_jcc [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (op : BitVec 8) (hmode : In64BitMode s)
    (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_70 ip context op).run s =
      (X86.Instructions.JO_RELBRb_0 (BitVec.add ip 1#64) context op).run s := by
  unfold Decode_Legacy_0_Opcode_70
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_70 context mode a b c d e f z) _ 1 hmode hf
    (fun _ _ _ _ _ _ => rfl)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- The `Jcc rel32` decoder in 64-bit mode runs `JO_RELBRd_0` at `ip + 1` (the displacement). -/
theorem decodeLegacy1Opcode80_run_of_jcc [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (op : BitVec 8) (hmode : In64BitMode s)
    (hf : DecoderFeatures s) :
    (Decode_Legacy_1_Opcode_80 ip context op).run s =
      (X86.Instructions.JO_RELBRd_0 (BitVec.add ip 1#64) context op).run s := by
  unfold Decode_Legacy_1_Opcode_80
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_1_Opcode_80 context mode a b c d e f z) _ 1 hmode hf
    (fun _ _ _ _ _ _ => rfl)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- The `EB` decoder in 64-bit mode runs `JMP_RELBRb_1` at `ip + 1`. -/
theorem decodeLegacy0OpcodeEB_run_of_jmp [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_EB ip context).run s =
      (X86.Instructions.JMP_RELBRb_1 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_EB
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_EB context mode a b c d e f z) _ 1 hmode hf
    (fun _ _ _ _ _ _ => rfl)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- The `E9` decoder in 64-bit mode runs `JMP_RELBRd` at `ip + 1`. -/
theorem decodeLegacy0OpcodeE9_run_of_jmp [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_E9 ip context).run s =
      (X86.Instructions.JMP_RELBRd (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_E9
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_E9 context mode a b c d e f z) _ 1 hmode hf
    (fun _ _ _ _ _ _ => rfl)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

end X86Proofs
