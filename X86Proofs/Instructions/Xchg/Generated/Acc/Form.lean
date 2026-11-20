import X86Proofs.Core.Operand
import X86Proofs.Program.ReadWrite.WritePair
import X86Proofs.Instructions.Xchg.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem xchg_r_rax_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (opcode : BitVec 8) (hmode : In64BitMode s)
    (n : Nat) (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.XCHG_GPRv_OrAX_0 ip ctx opcode).run s =
      let r := (gprNumber ctx.rex_b4 ctx.rex_b3 (opcode.extractLsb' 0 3))
      let dst : Operand n := .reg r
      let acc : Operand n := .reg 0
      (.ok (), writeResultPair s 0 r (xchgSpec (dst.read s) (acc.read s)).2
        (xchgSpec (dst.read s) (acc.read s)).1 ip) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.XCHG_GPRv_OrAX_0
    simp only [writeResultPair]
    spec_run [
      Read_GPR => readGPR_run _ _ 64 (by decide) (by decide) hmode,
      RAX => rax_run _,
      X86.Runtime.CheckedSlice.read => checkedSliceRead_zero_run _ _ 64 (by decide) (by decide),
      liftM => xchg_operation _ 64 (by decide) _ _,
      Write_RAX => writeRAX_run_of_nat _ 64 (by decide) _,
      Write_GPR => writeGPR_run _ _ 64 (by decide) _ (by exact hmode.of_cs_lma_eq rfl rfl)]
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.XCHG_GPRv_OrAX_0
    simp only [writeResultPair]
    spec_run [
      Read_GPR => readGPR_run _ _ 32 (by decide) (by decide) hmode,
      RAX => rax_run _,
      X86.Runtime.CheckedSlice.read => checkedSliceRead_zero_run _ _ 32 (by decide) (by decide),
      liftM => xchg_operation _ 32 (by decide) _ _,
      Write_RAX => writeRAX_run_of_nat _ 32 (by decide) _,
      Write_GPR => writeGPR_run _ _ 32 (by decide) _ (by exact hmode.of_cs_lma_eq rfl rfl)]

theorem xchg_r16_ax_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (opcode : BitVec 8) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 16)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.XCHG_GPRv_OrAX_0 ip ctx opcode).run s =
      let r := (gprNumber ctx.rex_b4 ctx.rex_b3 (opcode.extractLsb' 0 3))
      let dst : Operand 16 := .reg r
      let acc : Operand 16 := .reg 0
      (.ok (), writeResultPair s 0 r (xchgSpec (dst.read s) (acc.read s)).2
        (xchgSpec (dst.read s) (acc.read s)).1 ip) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.XCHG_GPRv_OrAX_0
  simp only [writeResultPair]
  spec_run [
    Read_GPR => readGPR_run _ _ 16 (by decide) (by decide) hmode,
    RAX => rax_run _,
    X86.Runtime.CheckedSlice.read => checkedSliceRead_zero_run _ _ 16 (by decide) (by decide),
    liftM => xchg_operation _ 16 (by decide) _ _,
    Write_RAX => writeRAX_run_of_nat _ 16 (by decide) _,
    Write_GPR => writeGPR_run _ _ 16 (by decide) _ (by exact hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
