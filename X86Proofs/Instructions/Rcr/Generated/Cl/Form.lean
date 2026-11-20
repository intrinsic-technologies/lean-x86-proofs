import X86Proofs.Core.Operand
import X86Proofs.Instructions.Rcr.Operation

namespace X86Proofs

open X86 X86.Helpers

attribute [local irreducible] X86.Instructions.Operations.RCR

theorem rcr_r_cl_form [X86.Machine.Bindings] (s : X86.Machine.RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s) (n : Nat)
    (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.RCR_GPRv_CL ip ctx rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let c := shiftCount n ((Operand.reg 1 : Operand 8).read s)
      (.ok (), writeOutputs s dst (rcrSpec (StatusFlags.ofRFLAGS s.RFLAGS)
        (oracleBit s.oracle) (StatusFlags.ofRFLAGS s.RFLAGS).CF c (dst.read s)) (rcrOracleBits c) ip) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.RCR_GPRv_CL
    simp only [Operand.read_reg64, Operand.read_reg8, writeOutputs, Operand.write_reg64]
    spec_run [
      Read_GPR => readGPR64_run _ _ hmode,
      CL => cl_run _,
      X86.Instructions.Operations.RCR => rcr_operation _ 64 (by decide) _ _,
      Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.RCR_GPRv_CL
    simp only [Operand.read_reg32, Operand.read_reg8, writeOutputs, Operand.write_reg32]
    spec_run [
      Read_GPR => readGPR32_run _ _ hmode,
      CL => cl_run _,
      X86.Instructions.Operations.RCR => rcr_operation _ 32 (by decide) _ _,
      Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem rcr_r16_cl_form [X86.Machine.Bindings] (s : X86.Machine.RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 16) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.RCR_GPRv_CL ip ctx rm).run s =
      let dst : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let c := shiftCount 16 ((Operand.reg 1 : Operand 8).read s)
      (.ok (), writeOutputs s dst (rcrSpec (StatusFlags.ofRFLAGS s.RFLAGS)
        (oracleBit s.oracle) (StatusFlags.ofRFLAGS s.RFLAGS).CF c (dst.read s)) (rcrOracleBits c) ip) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.RCR_GPRv_CL
  simp only [Operand.read_reg16, Operand.read_reg8, writeOutputs, Operand.write_reg16]
  spec_run [
    Read_GPR => readGPR16_run _ _ hmode,
    CL => cl_run _,
    X86.Instructions.Operations.RCR => rcr_operation _ 16 (by decide) _ _,
    Write_GPR => writeGPR16_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
