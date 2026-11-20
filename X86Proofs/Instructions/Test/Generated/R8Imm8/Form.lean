import X86Proofs.Step.Fetch
import X86Proofs.Core.Operand
import X86Proofs.Instructions.Test.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem test_r8_imm8_form [X86.Machine.Bindings] (s t : X86.Machine.RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (imm : BitVec 8) (hmode : In64BitMode s)
    (hrex : ctx.rex_prefix_present = true)
    (hlock : ctx.lock_prefix_present = false) (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) :
    (X86.Instructions.TEST_GPR8_IMMb_F6r0 ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeFlagsOutputs t (testSpec (oracleBit t.oracle) (dst.read s) (imm.signExtend 8)) 1
        (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with rex_prefix_present := true, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.TEST_GPR8_IMMb_F6r0
  simp only [Operand.read, writeFlagsOutputs]
  spec_run [
    Read_GPR8 => readGPR8_run_of_rex _ _ hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.TEST => test_operation _ 8 (by decide) _ _]

theorem test_r8_imm8_low_form [X86.Machine.Bindings] (s t : X86.Machine.RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (imm : BitVec 8) (hmode : In64BitMode s)
    (hrm : (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hlock : ctx.lock_prefix_present = false) (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) :
    (X86.Instructions.TEST_GPR8_IMMb_F6r0 ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeFlagsOutputs t (testSpec (oracleBit t.oracle) (dst.read s) (imm.signExtend 8)) 1
        (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.TEST_GPR8_IMMb_F6r0
  simp only [Operand.read_reg8, writeFlagsOutputs]
  spec_run [
    Read_GPR8 => readGPR8_run_of_low _ _ hrm _ hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.TEST => test_operation _ 8 (by decide) _ _]

theorem test_r8_imm8_gpr8_form [X86.Machine.Bindings] (s t : X86.Machine.RamState)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3) (imm : BitVec 8)
    (hmode : In64BitMode s)
    (hlock : ctx.lock_prefix_present = false) (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) :
    (X86.Instructions.TEST_GPR8_IMMb_F6r0 ip ctx rm).run s =
      let dst : Operand 8 := .gpr8 (gprNumber ctx.rex_b4 ctx.rex_b3 rm) (byteRex ctx)
      (.ok (), writeFlagsOutputs t (testSpec (oracleBit t.oracle) (dst.read s) (imm.signExtend 8)) 1
        (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.TEST_GPR8_IMMb_F6r0
  simp only [writeFlagsOutputs]
  spec_run [
    Read_GPR8 => readGPR8_run_gpr8 _ _ _ hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.TEST => test_operation _ 8 (by decide) _ _]

end X86Proofs
