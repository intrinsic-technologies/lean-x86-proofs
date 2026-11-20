
import X86Proofs.Step.Fetch
import X86Proofs.Core.Operand
import X86Proofs.Instructions.Shld.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

attribute [local irreducible] X86.Instructions.Operations.SHLD

theorem shld_r_r_cl_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (n : Nat) (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.SHLD_GPRv_GPRv_CL ip ctx reg rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let c := shiftCount n ((Operand.reg 1 : Operand 8).read s)
      (.ok (), writeOutputs s dst
        (shldSpec (fun i => oracleBit (oracleSkip s.oracle i))
          (s.oracle.take n).1 (StatusFlags.ofRFLAGS s.RFLAGS) c
          (dst.read s) (src.read s))
        (shldOracleBits n c) ip) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.SHLD_GPRv_GPRv_CL
    simp only [Operand.read_reg64, Operand.read_reg8, writeOutputs, Operand.write_reg64]
    spec_run [
      Read_GPR => readGPR64_run _ _ hmode,
      CL => cl_run _,
      X86.Instructions.Operations.SHLD => shld_operation _ 64 (by decide) _ _ _,
      Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.SHLD_GPRv_GPRv_CL
    simp only [Operand.read_reg32, Operand.read_reg8, writeOutputs, Operand.write_reg32]
    spec_run [
      Read_GPR => readGPR32_run _ _ hmode,
      CL => cl_run _,
      X86.Instructions.Operations.SHLD => shld_operation _ 32 (by decide) _ _ _,
      Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem shld_r16_r16_cl_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 16)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.SHLD_GPRv_GPRv_CL ip ctx reg rm).run s =
      let dst : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let c := shiftCount 16 ((Operand.reg 1 : Operand 8).read s)
      (.ok (), writeOutputs s dst
        (shldSpec (fun i => oracleBit (oracleSkip s.oracle i))
          (s.oracle.take 16).1 (StatusFlags.ofRFLAGS s.RFLAGS) c
          (dst.read s) (src.read s))
        (shldOracleBits 16 c) ip) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SHLD_GPRv_GPRv_CL
  simp only [Operand.read_reg16, Operand.read_reg8, writeOutputs, Operand.write_reg16]
  spec_run [
    Read_GPR => readGPR16_run _ _ hmode,
    CL => cl_run _,
    X86.Instructions.Operations.SHLD => shld_operation _ 16 (by decide) _ _ _,
    Write_GPR => writeGPR16_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
