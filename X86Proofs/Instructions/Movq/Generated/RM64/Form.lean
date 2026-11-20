import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Mmx
import X86Proofs.Instructions.Movd.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem movq_r64_mm_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0) (hes : fswES s.FP87_Status = 0)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hosz : ctx.osz_prefix_present = false)
    (hrep : ctx.rep_prefix = 0) :
    (X86.Instructions.MOVQ_GPR64_MMXq ip ctx reg rm).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 64 := .mmx reg
      (.ok (), writeResult (mmxEnter s) dst (movdSpec 64 64 (src.read s)) ip) := by
  unfold X86.Instructions.MOVQ_GPR64_MMXq
  simp only [hlock, hw, hosz, hrep]
  simp only [writeResult, mmxEnter, Operand.write_reg64, Operand.read_mmx]
  spec_run [
    Read_MMX => readMMX_run _ _,
    X86.Runtime.CheckedSlice.read => checkedSliceRead_mmx_run _ _,
    X86.CR0.EM => cr0EM_run_of_cr0 hcr0,
    X86.CR0.TS => cr0TS_run_of_cr0 hcr0,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
    X86.FP87_Status.setTOP => fp87StatusSetTOP_run _,
    liftM => liftM_run_of_ok (mov_wdq_operation 64 64 64 (by decide) (by decide) (by decide) _) _,
    Write_GPR => writeGPR64_run _ _ _ (by exact hmode.of_cs_lma_eq rfl rfl),
    X86.FP87_Tag_Word.assign => fp87TagWordAssign_run _ _]

end X86Proofs
