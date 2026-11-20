import X86Proofs.Core.Operand
import X86Proofs.Program.ReadWrite.WritePair
import X86Proofs.Instructions.Xadd.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem xadd_r8_r8_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hreg : ctx.rex_prefix_present = true ∨ (gprNumber ctx.rex_r4 ctx.rex_r3 reg).toNat < 4)
    (hrm : ctx.rex_prefix_present = true ∨ (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.XADD_GPR8_GPR8 ip ctx reg rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writePairOutputs s (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
        (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
        (xaddSpec (dst.read s) (src.read s)).2.1
        (xaddSpec (dst.read s) (src.read s)).1
        (xaddSpec (dst.read s) (src.read s)).2.2 0
        ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.XADD_GPR8_GPR8
  simp only [Operand.read_reg8, writePairOutputs, Operand.write_reg8, oracleSkip_zero]
  spec_run [
    Read_GPR8 => readGPR8_run_of_lowByte _ _ _ (lowByte_of_rex ‹_›) hmode,
    X86.Instructions.Operations.XADD => xadd_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_of_lowByte _ _ _ (lowByte_of_rex ‹_›) _
      (by exact hmode.of_cs_lma_eq rfl rfl)]

theorem xadd_r8_r8_gpr8_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.XADD_GPR8_GPR8 ip ctx reg rm).run s =
      let dst : Operand 8 := .gpr8 (gprNumber ctx.rex_b4 ctx.rex_b3 rm) (byteRex ctx)
      let src : Operand 8 := .gpr8 (gprNumber ctx.rex_r4 ctx.rex_r3 reg) (byteRex ctx)
      (.ok (), writePairOutputs8 s src dst
        (xaddSpec (dst.read s) (src.read s)).2.1 (xaddSpec (dst.read s) (src.read s)).1
        (xaddSpec (dst.read s) (src.read s)).2.2 0 ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.XADD_GPR8_GPR8
  simp only [writePairOutputs8, oracleSkip_zero]
  spec_run [
    Read_GPR8 => readGPR8_run_gpr8 _ _ _ hmode,
    X86.Instructions.Operations.XADD => xadd_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_gpr8 _ _ _ _
      (hmode.of_cs_lma_eq (by simp only [Operand.write_CS, setFlags])
        (by simp only [Operand.write_IA32_EFER, setFlags]))]

end X86Proofs
