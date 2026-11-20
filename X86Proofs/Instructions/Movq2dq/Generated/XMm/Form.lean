import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Mmx
import X86Proofs.Instructions.Xorps.Form
import X86Proofs.Instructions.Mov.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem movq2dq_xmm_mm_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (hes : fswES s.FP87_Status = 0)
    (hlock : ctx.lock_prefix_present = false) (hvex : ctx.vex_prefix_present = false)
    (hevex : ctx.evex_prefix_present = false) :
    (X86.Instructions.MOVQ2DQ_XMMdq_MMXq ip ctx reg rm).run s =
      let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 64 := .mmx rm
      (.ok (), writeResult (mmxEnter s) dst ((src.read s).setWidth 128) ip) := by
  unfold X86.Instructions.MOVQ2DQ_XMMdq_MMXq
  simp only [hlock, hvex, hevex]
  simp only [writeResult, mmxEnter, Operand.write_xmm, Operand.read_mmx]
  spec_run [
    Read_MMX => readMMX_run _ _,
    X86.Runtime.CheckedSlice.read => checkedSliceRead_mmx_run _ _,
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
    X86.FP87_Status.setTOP => fp87StatusSetTOP_run _,
    liftM => liftM_run_of_ok (mov_operation_except 64 _) _,
    Write_XMM => writeXMM64_run _ _ _ (by exact hmode.of_cs_lma_eq rfl rfl),
    X86.FP87_Tag_Word.assign => fp87TagWordAssign_run _ _]

end X86Proofs
