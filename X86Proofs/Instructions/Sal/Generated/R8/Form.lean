import X86Proofs.Core.Operand
import X86Proofs.Instructions.Shl.Operation

namespace X86Proofs

open X86 X86.Helpers

attribute [local irreducible] X86.Instructions.Operations.SHL

theorem sal_r8_imm8_form [X86.Machine.Bindings] (s t : X86.Machine.RamState)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3) (count : BitVec 8)
    (hmode : In64BitMode s) (hfetch : (Mem_Fetch ip 8).run s = (.ok count, t))
    (htmode : In64BitMode t)
    (hrm : ctx.rex_prefix_present = true ∨ (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.SHL_GPR8_IMMb_C0r6 ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let c := shiftCount 8 count
      (.ok (), writeOutputs t dst (shlSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shlOracleAF t.oracle c) c (dst.read s)) (shlOracleBits c)
        (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SHL_GPR8_IMMb_C0r6
  simp only [Operand.read_reg8, writeOutputs, Operand.write_reg8]
  spec_run [
    Read_GPR8 => readGPR8_run_of_lowByte _ _ _ (lowByte_of_rex ‹_›) hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.SHL => shl_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_of_lowByte _ _ _ (lowByte_of_rex ‹_›) _
      (htmode.of_cs_lma_eq rfl rfl)]

theorem sal_r8_imm8_gpr8_form [X86.Machine.Bindings] (s t : X86.Machine.RamState)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3) (count : BitVec 8)
    (hmode : In64BitMode s) (hfetch : (Mem_Fetch ip 8).run s = (.ok count, t))
    (htmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.SHL_GPR8_IMMb_C0r6 ip ctx rm).run s =
      let dst : Operand 8 := .gpr8 (gprNumber ctx.rex_b4 ctx.rex_b3 rm) (byteRex ctx)
      let c := shiftCount 8 count
      (.ok (), writeOutputs t dst (shlSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shlOracleAF t.oracle c) c (dst.read s)) (shlOracleBits c)
        (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SHL_GPR8_IMMb_C0r6
  simp only [writeOutputs]
  spec_run [
    Read_GPR8 => readGPR8_run_gpr8 _ _ _ hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.SHL => shl_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_gpr8 _ _ _ _ (htmode.of_cs_lma_eq rfl rfl)]

theorem sal_r8_one_form [X86.Machine.Bindings] (s : X86.Machine.RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s)
    (hrm : ctx.rex_prefix_present = true ∨ (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.SHL_GPR8_ONE_D0r6 ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs s dst (shlSpec (StatusFlags.ofRFLAGS s.RFLAGS)
        (oracleBit s.oracle) (shlOracleAF s.oracle 1) 1 (dst.read s)) (shlOracleBits 1) ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SHL_GPR8_ONE_D0r6
  simp only [Operand.read_reg8, writeOutputs, Operand.write_reg8]
  spec_run [
    Read_GPR8 => readGPR8_run_of_lowByte _ _ _ (lowByte_of_rex ‹_›) hmode,
    X86.Instructions.Operations.SHL => shl_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_of_lowByte _ _ _ (lowByte_of_rex ‹_›) _
      (hmode.of_cs_lma_eq rfl rfl)]

theorem sal_r8_one_gpr8_form [X86.Machine.Bindings] (s : X86.Machine.RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.SHL_GPR8_ONE_D0r6 ip ctx rm).run s =
      let dst : Operand 8 := .gpr8 (gprNumber ctx.rex_b4 ctx.rex_b3 rm) (byteRex ctx)
      (.ok (), writeOutputs s dst (shlSpec (StatusFlags.ofRFLAGS s.RFLAGS)
        (oracleBit s.oracle) (shlOracleAF s.oracle 1) 1 (dst.read s)) (shlOracleBits 1) ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SHL_GPR8_ONE_D0r6
  simp only [writeOutputs]
  spec_run [
    Read_GPR8 => readGPR8_run_gpr8 _ _ _ hmode,
    X86.Instructions.Operations.SHL => shl_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_gpr8 _ _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
