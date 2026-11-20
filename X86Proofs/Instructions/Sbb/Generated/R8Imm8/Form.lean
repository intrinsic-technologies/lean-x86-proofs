import X86Proofs.Step.Fetch
import X86Proofs.Core.Operand
import X86Proofs.Instructions.Sbb.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem sbb_r8_imm8_form [X86.Machine.Bindings] (s t : X86.Machine.RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (imm : BitVec 8) (hmode : In64BitMode s)
    (hrm : ctx.rex_prefix_present = true ∨ (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hlock : ctx.lock_prefix_present = false) (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) (htmode : In64BitMode t) :
    (X86.Instructions.SBB_GPR8_IMMb_80r3 ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs t dst (sbbSpec (StatusFlags.ofRFLAGS t.RFLAGS).CF (dst.read s) (imm.signExtend 8)) 0
        (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SBB_GPR8_IMMb_80r3
  simp only [Operand.read_reg8, writeOutputs, Operand.write_reg8, oracleSkip_zero]
  spec_run [
    Read_GPR8 => readGPR8_run_of_lowByte _ _ _ (lowByte_of_rex hrm) hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.SBB => sbb_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_of_lowByte _ _ _ (lowByte_of_rex hrm) _
      (htmode.of_cs_lma_eq rfl rfl)]

theorem sbb_r8_imm8_gpr8_form [X86.Machine.Bindings] (s t : X86.Machine.RamState)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3) (imm : BitVec 8)
    (hmode : In64BitMode s)
    (hlock : ctx.lock_prefix_present = false) (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t))
    (htmode : In64BitMode t) :
    (X86.Instructions.SBB_GPR8_IMMb_80r3 ip ctx rm).run s =
      let dst : Operand 8 := .gpr8 (gprNumber ctx.rex_b4 ctx.rex_b3 rm) (byteRex ctx)
      (.ok (), writeOutputs t dst (sbbSpec (StatusFlags.ofRFLAGS t.RFLAGS).CF (dst.read s) (imm.signExtend 8)) 0
        (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SBB_GPR8_IMMb_80r3
  simp only [writeOutputs, oracleSkip_zero]
  spec_run [
    Read_GPR8 => readGPR8_run_gpr8 _ _ _ hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.SBB => sbb_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_gpr8 _ _ _ _ (htmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
