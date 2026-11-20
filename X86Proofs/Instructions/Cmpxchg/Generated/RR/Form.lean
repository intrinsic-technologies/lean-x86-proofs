import X86Proofs.Core.Operand
import X86Proofs.Instructions.Cmpxchg.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem cmpxchg_r_r_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (n : Nat) (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.CMPXCHG_GPRv_GPRv ip ctx reg rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let acc : Operand n := .reg 0
      (.ok (), if acc.read s = dst.read s then
        writeOutputs s dst (src.read s, cmpSpec (acc.read s) (dst.read s)) 0
          ip
      else
        writeOutputs s acc (dst.read s, cmpSpec (acc.read s) (dst.read s)) 0
          ip) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.CMPXCHG_GPRv_GPRv
    simp only [Operand.read_reg64, writeOutputs, Operand.write_reg64, oracleSkip_zero]
    by_cases hc : (Operand.reg 0 : Operand 64).read s =
        (Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 64).read s
    · simp only [Operand.read_reg64] at hc
      simp only [eq_true hc, ↓reduceIte]
      spec_run [
        Read_GPR => readGPR64_run _ _ hmode,
        X86.Instructions.Operations.CMPXCHG =>
          cmpxchg_operation_eq _ 64 (by decide) s.GPR[gprIndex 0] _ _ _
            (by exact BitVec.setWidth_eq _) (by exact hc),
        Write_GPR => writeGPR64_run _ _ _ (by exact hmode.of_cs_lma_eq rfl rfl)]
    · simp only [Operand.read_reg64] at hc
      simp only [eq_false hc, ↓reduceIte]
      spec_run [
        Read_GPR => readGPR64_run _ _ hmode,
        X86.Instructions.Operations.CMPXCHG =>
          cmpxchg_operation_ne _ 64 (by decide) s.GPR[gprIndex 0] _ _ _
            (by exact BitVec.setWidth_eq _) (by exact hc)]
      simp only [mergeGPR_64]
      rfl
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.CMPXCHG_GPRv_GPRv
    simp only [Operand.read_reg32, writeOutputs, Operand.write_reg32, oracleSkip_zero]
    by_cases hc : (Operand.reg 0 : Operand 32).read s =
        (Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 32).read s
    · simp only [Operand.read_reg32] at hc
      simp only [eq_true hc, ↓reduceIte]
      spec_run [
        Read_GPR => readGPR32_run _ _ hmode,
        X86.Instructions.Operations.CMPXCHG =>
          cmpxchg_operation_eq _ 32 (by decide) (s.GPR[gprIndex 0].setWidth 32) _ _ _
            (by rfl) (by exact hc),
        Write_GPR => writeGPR32_run _ _ _ (by exact hmode.of_cs_lma_eq rfl rfl)]
    · simp only [Operand.read_reg32] at hc
      simp only [eq_false hc, ↓reduceIte]
      spec_run [
        Read_GPR => readGPR32_run _ _ hmode,
        X86.Instructions.Operations.CMPXCHG =>
          cmpxchg_operation_ne _ 32 (by decide) (s.GPR[gprIndex 0].setWidth 32) _ _ _
            (by rfl) (by exact hc)]

theorem cmpxchg_r16_r16_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 16)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.CMPXCHG_GPRv_GPRv ip ctx reg rm).run s =
      let dst : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let acc : Operand 16 := .reg 0
      (.ok (), if acc.read s = dst.read s then
        writeOutputs s dst (src.read s, cmpSpec (acc.read s) (dst.read s)) 0
          ip
      else
        writeOutputs s acc (dst.read s, cmpSpec (acc.read s) (dst.read s)) 0
          ip) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CMPXCHG_GPRv_GPRv
  simp only [Operand.read_reg16, writeOutputs, Operand.write_reg16, oracleSkip_zero]
  by_cases hc : (Operand.reg 0 : Operand 16).read s =
      (Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 16).read s
  · simp only [Operand.read_reg16] at hc
    simp only [eq_true hc, ↓reduceIte]
    spec_run [
      Read_GPR => readGPR16_run _ _ hmode,
      X86.Instructions.Operations.CMPXCHG =>
        cmpxchg_operation_eq _ 16 (by decide) (s.GPR[gprIndex 0].setWidth 16) _ _ _
          (by rfl) (by exact hc),
      Write_GPR => writeGPR16_run _ _ _ (by exact hmode.of_cs_lma_eq rfl rfl)]
  · simp only [Operand.read_reg16] at hc
    simp only [eq_false hc, ↓reduceIte]
    spec_run [
      Read_GPR => readGPR16_run _ _ hmode,
      X86.Instructions.Operations.CMPXCHG =>
        cmpxchg_operation_ne _ 16 (by decide) (s.GPR[gprIndex 0].setWidth 16) _ _ _
          (by rfl) (by exact hc)]

end X86Proofs
