import X86Proofs.Core.Operand
import X86Proofs.Instructions.Cmp.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem cmp_r8_r8_rev_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hreg : ctx.rex_prefix_present = true ∨ (gprNumber ctx.rex_r4 ctx.rex_r3 reg).toNat < 4)
    (hrm : ctx.rex_prefix_present = true ∨ (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.CMP_GPR8_GPR8_3A ip ctx reg rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeFlagsOutputs s (cmpSpec (dst.read s) (src.read s)) 0 ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CMP_GPR8_GPR8_3A
  simp only [Operand.read_reg8, writeFlagsOutputs, oracleSkip_zero]
  spec_run [
    Read_GPR8 => readGPR8_run_of_lowByte _ _ _ (lowByte_of_rex ‹_›) hmode,
    X86.Instructions.Operations.CMP => cmp_operation _ 8 (by decide) _ _]

theorem cmp_r8_r8_rev_gpr8_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.CMP_GPR8_GPR8_3A ip ctx reg rm).run s =
      let dst : Operand 8 := .gpr8 (gprNumber ctx.rex_r4 ctx.rex_r3 reg) (byteRex ctx)
      let src : Operand 8 := .gpr8 (gprNumber ctx.rex_b4 ctx.rex_b3 rm) (byteRex ctx)
      (.ok (), writeFlagsOutputs s (cmpSpec (dst.read s) (src.read s)) 0 ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CMP_GPR8_GPR8_3A
  simp only [writeFlagsOutputs, oracleSkip_zero]
  spec_run [
    Read_GPR8 => readGPR8_run_gpr8 _ _ _ hmode,
    X86.Instructions.Operations.CMP => cmp_operation _ 8 (by decide) _ _]

end X86Proofs
