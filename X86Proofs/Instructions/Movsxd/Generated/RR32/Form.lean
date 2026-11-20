
import X86Proofs.Core.Operand
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Movsxd.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem movsxd_r_r32_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (n : Nat) (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.MOVSXD_GPRv_GPRz ip ctx reg rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 32 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst (movsxdSpec n (src.read s)) ip) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.MOVSXD_GPRv_GPRz
    simp only [Operand.read_reg32, writeResult, Operand.write_reg64]
    spec_run [
      Read_GPR => readGPR32_run _ _ hmode,
      liftM => movsxd_operation _ 32 64 (by decide) _,
      Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.MOVSXD_GPRv_GPRz
    simp only [Operand.read_reg32, writeResult, Operand.write_reg32]
    spec_run [
      Read_GPR => readGPR32_run _ _ hmode,
      liftM => movsxd_operation _ 32 32 (by decide) _,
      Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem movsxd_r16_r16_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 16)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.MOVSXD_GPRv_GPRz ip ctx reg rm).run s =
      let dst : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst (movsxdSpec 16 (src.read s)) ip) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.MOVSXD_GPRv_GPRz
  simp only [Operand.read_reg16, writeResult, Operand.write_reg16]
  spec_run [
    Read_GPR => readGPR16_run _ _ hmode,
    liftM => movsxd_operation _ 16 16 (by decide) _,
    Write_GPR => writeGPR16_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
