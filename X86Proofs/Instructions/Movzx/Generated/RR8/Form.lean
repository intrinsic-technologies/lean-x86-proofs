
import X86Proofs.Core.Operand
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Movzx.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem movzx_r_r8_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (n : Nat) (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n)
    (hrm : ctx.rex_prefix_present = true ∨ (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.MOVZX_GPRv_GPR8 ip ctx reg rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst (movzxSpec n (src.read s)) ip) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.MOVZX_GPRv_GPR8
    simp only [Operand.read_reg8, writeResult, Operand.write_reg64]
    spec_run [
      Read_GPR8 => readGPR8_run_of_lowByte _ _ _ (lowByte_of_rex ‹_›) hmode,
      liftM => movzx_operation_of_sizes _ 8 64 (by decide) (by decide) _,
      Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.MOVZX_GPRv_GPR8
    simp only [Operand.read_reg8, writeResult, Operand.write_reg32]
    spec_run [
      Read_GPR8 => readGPR8_run_of_lowByte _ _ _ (lowByte_of_rex ‹_›) hmode,
      liftM => movzx_operation_of_sizes _ 8 32 (by decide) (by decide) _,
      Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem movzx_r_r8_gpr8_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (n : Nat) (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.MOVZX_GPRv_GPR8 ip ctx reg rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 8 := .gpr8 (gprNumber ctx.rex_b4 ctx.rex_b3 rm) (byteRex ctx)
      (.ok (), writeResult s dst (movzxSpec n (src.read s)) ip) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.MOVZX_GPRv_GPR8
    simp only [writeResult, Operand.write_reg64]
    spec_run [
      Read_GPR8 => readGPR8_run_gpr8 _ _ _ hmode,
      liftM => movzx_operation_of_sizes _ 8 64 (by decide) (by decide) _,
      Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.MOVZX_GPRv_GPR8
    simp only [writeResult, Operand.write_reg32]
    spec_run [
      Read_GPR8 => readGPR8_run_gpr8 _ _ _ hmode,
      liftM => movzx_operation_of_sizes _ 8 32 (by decide) (by decide) _,
      Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem movzx_r16_r8_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 16)
    (hrm : ctx.rex_prefix_present = true ∨ (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.MOVZX_GPRv_GPR8 ip ctx reg rm).run s =
      let dst : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst (movzxSpec 16 (src.read s)) ip) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.MOVZX_GPRv_GPR8
  simp only [Operand.read_reg8, writeResult, Operand.write_reg16]
  spec_run [
    Read_GPR8 => readGPR8_run_of_lowByte _ _ _ (lowByte_of_rex ‹_›) hmode,
    liftM => movzx_operation_of_sizes _ 8 16 (by decide) (by decide) _,
    Write_GPR => writeGPR16_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem movzx_r16_r8_gpr8_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 16)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.MOVZX_GPRv_GPR8 ip ctx reg rm).run s =
      let dst : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 8 := .gpr8 (gprNumber ctx.rex_b4 ctx.rex_b3 rm) (byteRex ctx)
      (.ok (), writeResult s dst (movzxSpec 16 (src.read s)) ip) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.MOVZX_GPRv_GPR8
  simp only [writeResult, Operand.write_reg16]
  spec_run [
    Read_GPR8 => readGPR8_run_gpr8 _ _ _ hmode,
    liftM => movzx_operation_of_sizes _ 8 16 (by decide) (by decide) _,
    Write_GPR => writeGPR16_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
