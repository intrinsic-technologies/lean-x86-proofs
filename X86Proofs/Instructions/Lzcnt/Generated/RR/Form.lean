
import X86Proofs.Core.Operand
import X86Proofs.Core.ReadOnly
import X86Proofs.Instructions.Lzcnt.Operation

namespace X86Proofs

open X86 X86.Helpers X86.Machine X86.UserProcess

theorem lzcnt_r_r_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (n : Nat) (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n)
    (hlock : ctx.lock_prefix_present = false)
    (hl : Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true) :
    (X86.Instructions.LZCNT_GPRv_GPRv ip ctx reg rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs s dst
        (lzcntSpec (fun i => oracleBit (oracleSkip s.oracle i)) (src.read s)) 4 ip) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.LZCNT_GPRv_GPRv
    simp only [Operand.read_reg64, writeOutputs, Operand.write_reg64]
    spec_run [
      Read_GPR => readGPR64_run _ _ hmode,
      CPUID_LZCNT => readCPUIDFeature_run hl,
      X86.Instructions.Operations.LZCNT => lzcnt_operation _ 64 (by decide) _,
      Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.LZCNT_GPRv_GPRv
    simp only [Operand.read_reg32, writeOutputs, Operand.write_reg32]
    spec_run [
      Read_GPR => readGPR32_run _ _ hmode,
      CPUID_LZCNT => readCPUIDFeature_run hl,
      X86.Instructions.Operations.LZCNT => lzcnt_operation _ 32 (by decide) _,
      Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem lzcnt_r16_r16_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 16)
    (hlock : ctx.lock_prefix_present = false)
    (hl : Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true) :
    (X86.Instructions.LZCNT_GPRv_GPRv ip ctx reg rm).run s =
      let dst : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs s dst
        (lzcntSpec (fun i => oracleBit (oracleSkip s.oracle i)) (src.read s)) 4 ip) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.LZCNT_GPRv_GPRv
  simp only [Operand.read_reg16, writeOutputs, Operand.write_reg16]
  spec_run [
    Read_GPR => readGPR16_run _ _ hmode,
    CPUID_LZCNT => readCPUIDFeature_run hl,
    X86.Instructions.Operations.LZCNT => lzcnt_operation _ 16 (by decide) _,
    Write_GPR => writeGPR16_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
