
import X86Proofs.Step.Fetch
import X86Proofs.Core.Operand
import X86Proofs.Instructions.Bt.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem bt_r_imm8_form [X86.Machine.Bindings] (s t : X86.Machine.RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (imm : BitVec 8) (hmode : In64BitMode s)
    (n : Nat) (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n)
    (hlock : ctx.lock_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) :
    (X86.Instructions.BT_GPRv_IMMb ip ctx rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeFlagsOutputs t
        (btSpec (fun i => oracleBit (oracleSkip t.oracle i))
          (StatusFlags.ofRFLAGS t.RFLAGS) (dst.read s) (imm.signExtend n)) 4
        (BitVec.add ip 1#64)) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.BT_GPRv_IMMb
    simp only [Operand.read_reg64, writeFlagsOutputs]
    spec_run [
      Read_GPR => readGPR64_run _ _ hmode,
      Mem_Fetch => hfetch,
      X86.Instructions.Operations.BT => bt_operation _ 64 (by decide) _ _]
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.BT_GPRv_IMMb
    simp only [Operand.read_reg32, writeFlagsOutputs]
    spec_run [
      Read_GPR => readGPR32_run _ _ hmode,
      Mem_Fetch => hfetch,
      X86.Instructions.Operations.BT => bt_operation _ 32 (by decide) _ _]

theorem bt_r16_imm8_form [X86.Machine.Bindings] (s t : X86.Machine.RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (imm : BitVec 8) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 16)
    (hlock : ctx.lock_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) :
    (X86.Instructions.BT_GPRv_IMMb ip ctx rm).run s =
      let dst : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeFlagsOutputs t
        (btSpec (fun i => oracleBit (oracleSkip t.oracle i))
          (StatusFlags.ofRFLAGS t.RFLAGS) (dst.read s) (imm.signExtend 16)) 4
        (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.BT_GPRv_IMMb
  simp only [Operand.read_reg16, writeFlagsOutputs]
  spec_run [
    Read_GPR => readGPR16_run _ _ hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.BT => bt_operation _ 16 (by decide) _ _]

end X86Proofs
