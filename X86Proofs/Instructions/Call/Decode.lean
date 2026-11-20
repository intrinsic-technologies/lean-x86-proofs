import X86Proofs.Step.MemOperand
import X86Proofs.Instructions.Call.Form
import X86Proofs.Step.Decode.Legacy0
import X86Proofs.Step.Decode.Legacy0OpcodeFF

/-!
# Decoding CALL and RET

- `CALL rel32` (`E8`, `CALL_NEAR_RELBRd`) and `RET` (`C3`, `RET_NEAR`): one opcode each, no ModRM;
  the decoder hands the form the address after the opcode (`decodeLegacy0OpcodeE8_run_of_call`,
  `decodeLegacy0OpcodeC3_run_of_ret`; dispatch `decodeLegacy0_run_of_opcodeE8`,
  `decodeLegacy0_run_of_opcodeC3` in `Step/Decode/Legacy0.lean`).
- `CALL r/m64` (`FF /2`): the group opcode `FF` selects `CALL_NEAR_GPRv` for `mod = 3` and
  `CALL_NEAR_MEMv` otherwise, in any context (`decodeLegacy0OpcodeFF_run_of_call_register`,
  `decodeLegacy0OpcodeFF_run_of_call_memory`, in `Step/Decode/Legacy0OpcodeFF.lean`).
  `decodeLegacy0_run_of_FF_call_register` and `decodeLegacy0_run_of_FF_call_memory` take the
  opcode at offset `j` (after `j` prefix bytes), as `step_scan_legacy0` hands over.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The `E8` decoder in 64-bit mode runs `CALL_NEAR_RELBRd` at `ip + 1` (the displacement). -/
theorem decodeLegacy0OpcodeE8_run_of_call [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_E8 ip context).run s =
      (X86.Instructions.CALL_NEAR_RELBRd (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_E8
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_E8 context mode a b c d e f z) _ 1 hmode hf
    (fun _ _ _ _ _ _ => rfl)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- The `C3` decoder in 64-bit mode runs `RET_NEAR` with `Next_IP` `ip + 1`. -/
theorem decodeLegacy0OpcodeC3_run_of_ret [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_C3 ip context).run s =
      (X86.Instructions.RET_NEAR (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_C3
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_C3 context mode a b c d e f z) _ 1 hmode hf
    (fun _ _ _ _ _ _ => rfl)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

/-- `call r64` (`FF /2`, `mod = 3`) at offset `j` (after `j` prefix bytes). -/
theorem decodeLegacy0_run_of_FF_call_register [Bindings] (s : RamState) (h : ReadyToStep s)
    (bytes : List UInt8) (j : Nat) (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 2) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (hop : bytes[j]? = some 0xFF)
    (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.CALL_NEAR_GPRv (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx
        (modrmRm modrm)).run (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy0_run_of_modrm_at s h bytes j 0xFF modrm hcode hlow hop hm hj ctx _ _
    (fun a u hf hmode => decodeLegacy0_run_of_opcodeFF a u _ ctx hrex2 hf hmode)
    (fun a u hf hmode hfe => decodeLegacy0OpcodeFF_run_of_call_register a u _ ctx _ hmod hreg hmode hfe hf)

/-- `call [mem]` (`FF /2`, `mod ≠ 3`) at offset `j` (after `j` prefix bytes). -/
theorem decodeLegacy0_run_of_FF_call_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (bytes : List UInt8) (j : Nat) (modrm : UInt8) (hmod : modrmMod modrm ≠ 3)
    (hreg : modrmReg modrm = 2) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (hop : bytes[j]? = some 0xFF)
    (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.CALL_NEAR_MEMv (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx
        (modrmMod modrm) (modrmRm modrm)).run (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy0_run_of_modrm_at s h bytes j 0xFF modrm hcode hlow hop hm hj ctx _ _
    (fun a u hf hmode => decodeLegacy0_run_of_opcodeFF a u _ ctx hrex2 hf hmode)
    (fun a u hf hmode hfe => decodeLegacy0OpcodeFF_run_of_call_memory a u _ ctx _ hmod hreg hmode hfe hf)

end X86Proofs
