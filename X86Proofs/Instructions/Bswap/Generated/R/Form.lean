
import X86Proofs.Core.Operand
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Bswap.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem bswap_r_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (opcode : BitVec 8) (hmode : In64BitMode s)
    (n : Nat) (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.BSWAP_GPRv ip ctx opcode).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (opcode.extractLsb' 0 3))
      (.ok (), writeResult s dst (bswapSpec (dst.read s)) ip) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.BSWAP_GPRv
    simp only [Operand.read_reg64, writeResult, Operand.write_reg64]
    spec_run [
      Read_GPR => readGPR64_run _ _ hmode,
      X86.Runtime.CheckedSlice.read => checkedSliceRead_zero_run _ _ 8 (by decide) (by decide),
      liftM => liftM_run_of_ok (bswap_operation 64 (by decide) _) _,
      Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.BSWAP_GPRv
    simp only [Operand.read_reg32, writeResult, Operand.write_reg32]
    spec_run [
      Read_GPR => readGPR32_run _ _ hmode,
      X86.Runtime.CheckedSlice.read => checkedSliceRead_zero_run _ _ 8 (by decide) (by decide),
      liftM => liftM_run_of_ok (bswap_operation 32 (by decide) _) _,
      Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
