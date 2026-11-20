import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Float
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Xorps.Form
import X86Proofs.Instructions.Cvttps2dq.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cvttps2dq_xmm_xmm_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hlock : ctx.lock_prefix_present = false)
    (hvex : ctx.vex_prefix_present = false)
    (hevex : ctx.evex_prefix_present = false)
    (hm : MxcsrPre s)
    (hok : cvttps2dqOk s.MXCSR ((Operand.xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 128).read s)
      ((Operand.xmm (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 128).read s)) :
    (X86.Instructions.CVTTPS2DQ_XMMdq_XMMps ip ctx 3 reg rm).run s =
      let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 128 := .xmm (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      some (.ok (), writeResult
        ((Operand.mxcsr : Operand 32).write s
          (mxOr s.MXCSR (cvttps2dqFlags s.MXCSR (dst.read s) (src.read s))))
        dst (cvttps2dqSpec s.MXCSR (dst.read s) (src.read s)) ip) := by
  have hm' : In64BitMode
      { s with Next_IP := ip, MXCSR := mxOr s.MXCSR (cvttps2dqFlags s.MXCSR
        ((Operand.xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 128).read s)
        ((Operand.xmm (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 128).read s)) } :=
    hmode.of_cs_lma_eq rfl rfl
  unfold X86.Instructions.CVTTPS2DQ_XMMdq_XMMps
  simp only [hlock, hvex, hevex, calculateRM_run_of_mod3 rm ctx hevex]
  pspec_run [
    Read_XMM => readXMM_run _ _ _ (by decide) (by decide) hmode,
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    X86.Instructions.Operations.CVTTPf2i => cvttps2dq_operation _ _ _ (by exact hm) (by exact hok)]
  refine (partialSpecM_liftTotal_run _ (writeXMM128_run _ _ _ hm')).trans ?_
  simp only [writeResult, Operand.write_xmm, Operand.write_mxcsr, Operand.read_xmm,
    concatBits_xmm_reg]
  rfl

end X86Proofs
