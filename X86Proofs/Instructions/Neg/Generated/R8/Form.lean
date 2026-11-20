import X86Proofs.Core.Operand
import X86Proofs.Instructions.Neg.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem neg_r8_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s)
    (hrm : ctx.rex_prefix_present = true ∨ (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.NEG_GPR8 ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs s dst (negSpec (dst.read s)) 0 ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.NEG_GPR8
  simp only [Operand.read_reg8, writeOutputs, Operand.write_reg8, oracleSkip_zero]
  spec_run [
    Read_GPR8 => readGPR8_run_of_lowByte _ _ _ (lowByte_of_rex ‹_›) hmode,
    X86.Instructions.Operations.NEG => neg_operation _ 8 (by decide) _,
    Write_GPR8 => writeGPR8_run_of_lowByte _ _ _ (lowByte_of_rex ‹_›) _
      (hmode.of_cs_lma_eq rfl rfl)]

theorem neg_r8_gpr8_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.NEG_GPR8 ip ctx rm).run s =
      let dst : Operand 8 := .gpr8 (gprNumber ctx.rex_b4 ctx.rex_b3 rm) (byteRex ctx)
      (.ok (), writeOutputs s dst (negSpec (dst.read s)) 0 ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.NEG_GPR8
  simp only [writeOutputs, oracleSkip_zero]
  spec_run [
    Read_GPR8 => readGPR8_run_gpr8 _ _ _ hmode,
    X86.Instructions.Operations.NEG => neg_operation _ 8 (by decide) _,
    Write_GPR8 => writeGPR8_run_gpr8 _ _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
