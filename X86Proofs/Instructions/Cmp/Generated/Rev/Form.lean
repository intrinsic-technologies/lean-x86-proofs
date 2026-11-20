import X86Proofs.Core.Operand
import X86Proofs.Instructions.Cmp.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem cmp_r_r_rev_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s) (n : Nat)
    (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.CMP_GPRv_GPRv_3B ip ctx reg rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeFlagsOutputs s (cmpSpec (dst.read s) (src.read s)) 0 ip) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.CMP_GPRv_GPRv_3B
    simp only [Operand.read_reg64, writeFlagsOutputs, oracleSkip_zero]
    spec_run [
      Read_GPR => readGPR64_run _ _ hmode,
      X86.Instructions.Operations.CMP => cmp_operation _ 64 (by decide) _ _]
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.CMP_GPRv_GPRv_3B
    simp only [Operand.read_reg32, writeFlagsOutputs, oracleSkip_zero]
    spec_run [
      Read_GPR => readGPR32_run _ _ hmode,
      X86.Instructions.Operations.CMP => cmp_operation _ 32 (by decide) _ _]

theorem cmp_r16_r16_rev_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 16) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.CMP_GPRv_GPRv_3B ip ctx reg rm).run s =
      let dst : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeFlagsOutputs s (cmpSpec (dst.read s) (src.read s)) 0 ip) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CMP_GPRv_GPRv_3B
  simp only [Operand.read_reg16, writeFlagsOutputs, oracleSkip_zero]
  spec_run [
    Read_GPR => readGPR16_run _ _ hmode,
    X86.Instructions.Operations.CMP => cmp_operation _ 16 (by decide) _ _]

end X86Proofs
