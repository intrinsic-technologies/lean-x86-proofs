import X86Proofs.Step.Selector
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.MovSreg.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem mov_r_sreg_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (n : Nat) (hn : n = 64 ∨ n = 32 ∨ n = 16) (hsize : ctx.operand_size = n)
    (hlock : ctx.lock_prefix_present = false) (hreg : reg.toNat < 6) :
    (X86.Instructions.MOV_GPRv_SEG ip ctx reg rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst (movsregSpec n (segSelector s reg)) ip) := by
  rcases hn with rfl | rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.MOV_GPRv_SEG
    simp only [Bool.false_eq_true, ↓reduceIte, writeResult, Operand.write_reg64]
    spec_bind_with (liftM_run_of_ok (isValidSegmentIndex_read reg hreg) _)
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    spec_run [
      Read_Segment => readSegment_run _ _ hreg,
      liftM => movsreg_operation _ 64 (by decide) _,
      Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.MOV_GPRv_SEG
    simp only [Bool.false_eq_true, ↓reduceIte, writeResult, Operand.write_reg32]
    spec_bind_with (liftM_run_of_ok (isValidSegmentIndex_read reg hreg) _)
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    spec_run [
      Read_Segment => readSegment_run _ _ hreg,
      liftM => movsreg_operation _ 32 (by decide) _,
      Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]
  · have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.MOV_GPRv_SEG
    simp only [Bool.false_eq_true, ↓reduceIte, writeResult, Operand.write_reg16]
    spec_bind_with (liftM_run_of_ok (isValidSegmentIndex_read reg hreg) _)
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    spec_run [
      Read_Segment => readSegment_run _ _ hreg,
      liftM => movsreg_operation _ 16 (by decide) _,
      Write_GPR => writeGPR16_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
