import X86Proofs.Core.Operand
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Cmpxchg.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem cmpxchg_r8_r8_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hreg : ctx.rex_prefix_present = true ∨ (gprNumber ctx.rex_r4 ctx.rex_r3 reg).toNat < 4)
    (hrm : ctx.rex_prefix_present = true ∨ (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.CMPXCHG_GPR8_GPR8 ip ctx reg rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let acc : Operand 8 := .reg 0
      (.ok (), if acc.read s = dst.read s then
        writeOutputs s dst (src.read s, cmpSpec (acc.read s) (dst.read s)) 0
          ip
      else
        writeOutputs s acc (dst.read s, cmpSpec (acc.read s) (dst.read s)) 0
          ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CMPXCHG_GPR8_GPR8
  simp only [Operand.read_reg8, writeOutputs, Operand.write_reg8, oracleSkip_zero]
  by_cases hc : (Operand.reg 0 : Operand 8).read s =
      (Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 8).read s
  · simp only [Operand.read_reg8] at hc
    simp only [eq_true hc, ↓reduceIte]
    spec_run [
      Read_GPR8 => readGPR8_run_of_lowByte _ _ _ (lowByte_of_rex ‹_›) hmode,
      X86.Instructions.Operations.CMPXCHG =>
        cmpxchg_operation_eq _ 8 (by decide) (s.GPR[gprIndex 0].setWidth 8) _ _ _
          (by rfl) (by exact hc),
      Write_GPR8 => writeGPR8_run_of_lowByte _ _ _ (lowByte_of_rex ‹_›) _
        (by exact hmode.of_cs_lma_eq rfl rfl)]
  · simp only [Operand.read_reg8] at hc
    simp only [eq_false hc, ↓reduceIte]
    spec_run [
      Read_GPR8 => readGPR8_run_of_lowByte _ _ _ (lowByte_of_rex ‹_›) hmode,
      X86.Instructions.Operations.CMPXCHG =>
        cmpxchg_operation_ne _ 8 (by decide) (s.GPR[gprIndex 0].setWidth 8) _ _ _
          (by rfl) (by exact hc)]

theorem cmpxchg_r8_r8_gpr8_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.CMPXCHG_GPR8_GPR8 ip ctx reg rm).run s =
      let dst : Operand 8 := .gpr8 (gprNumber ctx.rex_b4 ctx.rex_b3 rm) (byteRex ctx)
      let src : Operand 8 := .gpr8 (gprNumber ctx.rex_r4 ctx.rex_r3 reg) (byteRex ctx)
      let acc : Operand 8 := .reg 0
      (.ok (), if acc.read s = dst.read s then
        writeOutputs s dst (src.read s, cmpSpec (acc.read s) (dst.read s)) 0
          ip
      else
        writeOutputs s acc (dst.read s, cmpSpec (acc.read s) (dst.read s)) 0
          ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  have hrex : byteRex {ctx with lock_prefix_present := false} = byteRex ctx := rfl
  rw [← hcontext]
  unfold X86.Instructions.CMPXCHG_GPR8_GPR8
  simp only [Operand.read_reg8, writeOutputs, Operand.write_reg8, oracleSkip_zero, hrex]
  by_cases hc : (Operand.reg 0 : Operand 8).read s =
      (Operand.gpr8 (gprNumber ctx.rex_b4 ctx.rex_b3 rm) (byteRex ctx)).read s
  · simp only [Operand.read_reg8] at hc
    simp only [eq_true hc, ↓reduceIte]
    spec_run [
      Read_GPR8 => readGPR8_run_gpr8 _ _ _ hmode,
      X86.Instructions.Operations.CMPXCHG =>
        cmpxchg_operation_eq _ 8 (by decide) (s.GPR[gprIndex 0].setWidth 8) _ _ _
          (by rfl) (by exact hc),
      Write_GPR8 => writeGPR8_run_gpr8 _ _ _ _ (by exact hmode.of_cs_lma_eq rfl rfl)]
  · simp only [Operand.read_reg8] at hc
    simp only [eq_false hc, ↓reduceIte]
    spec_run [
      Read_GPR8 => readGPR8_run_gpr8 _ _ _ hmode,
      X86.Instructions.Operations.CMPXCHG =>
        cmpxchg_operation_ne _ 8 (by decide) (s.GPR[gprIndex 0].setWidth 8) _ _ _
          (by rfl) (by exact hc)]

end X86Proofs
