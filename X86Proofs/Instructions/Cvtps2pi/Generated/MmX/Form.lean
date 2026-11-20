import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Mmx
import X86Proofs.Instructions.Xorps.Form
import X86Proofs.Instructions.Cvtps2dq.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cvtps2pi_mm_xmm_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (hes : fswES s.FP87_Status = 0)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hrep : ctx.rep_prefix = 0)
    (hevex : ctx.evex_prefix_present = false)
    (hevexb : ctx.evex_b = 0)
    (hm : MxcsrPre s)
    (hok : cvtps2piOk s.MXCSR
      ((Operand.xmm (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 128).read s)) :
    (X86.Instructions.CVTPS2PI_MMXq_XMMq ip ctx 3 reg rm).run s =
      let dst : Operand 64 := .mmx reg
      let src : Operand 128 := .xmm (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      some (.ok (), writeResult
        (mmxEnter ((Operand.mxcsr : Operand 32).write s
          (mxOr s.MXCSR (cvtps2piFlags s.MXCSR (src.read s)))))
        dst (cvtps2piSpec s.MXCSR (src.read s)) ip) := by
  unfold X86.Instructions.CVTPS2PI_MMXq_XMMq
  simp only [hlock, hosz, hrep, calculateRM_run_of_mod3 rm ctx hevex]
  simp only [writeResult, mmxEnter, Operand.write_mmx, Operand.write_mxcsr, Operand.read_xmm]
  pspec_run [
    Read_XMM => readXMM128_run _ _ hmode,
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
    X86.FP87_Status.setTOP => fp87StatusSetTOP_run _,
    X86.FP87_Tag_Word.assign => fp87TagWordAssign_run _ _,
    X86.Instructions.Operations.CVTPf2i =>
      cvtps2pi_operation 128 (.inr rfl) _ _ _ _ hevexb (by exact hm) (by exact hok),
    Write_MMX => writeMMX_run _ _ _]

end X86Proofs
