import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Float
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Xorps.Form
import X86Proofs.Instructions.Cvtpd2ps.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cvtpd2ps_xmm_xmm_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hlock : ctx.lock_prefix_present = false)
    (hrep : ctx.rep_prefix = 0)
    (hvex : ctx.vex_prefix_present = false)
    (hevex : ctx.evex_prefix_present = false)
    (hevexb : ctx.evex_b = 0)
    (hm : MxcsrPre s)
    (hok : cvtpd2psOk s.MXCSR ((Operand.xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 128).read s)
      ((Operand.xmm (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 128).read s)) :
    (X86.Instructions.CVTPD2PS_XMMps_XMMpd ip ctx 3 reg rm).run s =
      let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 128 := .xmm (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult
        ((Operand.mxcsr : Operand 32).write s
          (mxOr s.MXCSR (cvtpd2psFlags s.MXCSR (dst.read s) (src.read s))))
        dst (cvtpd2psSpec s.MXCSR (dst.read s) (src.read s)) ip) := by
  have hm' : In64BitMode
      { s with Next_IP := ip, MXCSR := mxOr s.MXCSR (cvtpd2psFlags s.MXCSR
        ((Operand.xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 128).read s)
        ((Operand.xmm (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 128).read s)) } :=
    hmode.of_cs_lma_eq rfl rfl
  unfold X86.Instructions.CVTPD2PS_XMMps_XMMpd
  simp only [hlock, hrep, hvex, hevex, calculateRM_run_of_mod3 rm ctx hevex, liftM_ok]
  spec_run [
    Read_XMM => readXMM_run _ _ _ (by decide) (by decide) hmode,
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    X86.Instructions.Operations.CVTPg2Pf => cvtpd2ps_operation _ _ _ _ _ hevexb (by exact hm) (by exact hok)]
  refine (writeXMM128_run _ _ _ hm').trans ?_
  simp only [writeResult, Operand.write_xmm, Operand.write_mxcsr, Operand.read_xmm,
    concatBits_xmm_reg]
  rfl

end X86Proofs
