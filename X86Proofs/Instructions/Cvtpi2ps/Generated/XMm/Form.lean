import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Mmx
import X86Proofs.Instructions.Xorps.Form
import X86Proofs.Instructions.Cvtpi2ps.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cvtpi2ps_xmm_mm_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (hes : fswES s.FP87_Status = 0)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hrep : ctx.rep_prefix = 0)
    (hvex : ctx.vex_prefix_present = false)
    (hevex : ctx.evex_prefix_present = false)
    (hm : MxcsrPre s)
    (hok : cvtpi2psOk s.MXCSR
      ((Operand.xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 128).read s)
      ((Operand.mmx rm : Operand 64).read s)) :
    (X86.Instructions.CVTPI2PS_XMMq_MMXq ip ctx reg rm).run s =
      let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 64 := .mmx rm
      (.ok (), writeResult
        (mmxEnter ((Operand.mxcsr : Operand 32).write s
          (mxOr s.MXCSR (cvtpi2psFlags s.MXCSR (dst.read s) (src.read s)))))
        dst (cvtpi2psSpec s.MXCSR (dst.read s) (src.read s)) ip) := by
  unfold X86.Instructions.CVTPI2PS_XMMq_MMXq
  simp only [hlock, hosz, hrep, hvex, hevex]
  simp only [writeResult, mmxEnter, Operand.write_xmm, Operand.write_mxcsr, Operand.read_xmm,
    Operand.read_mmx]
  spec_run [
    Read_XMM => readXMM128_run _ _ hmode,
    Read_MMX => readMMX_run _ _,
    X86.Runtime.CheckedSlice.read => checkedSliceRead_mmx_run _ _,
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
    X86.FP87_Status.setTOP => fp87StatusSetTOP_run _,
    X86.FP87_Tag_Word.assign => fp87TagWordAssign_run _ _,
    X86.Instructions.Operations.CVTPI2PS =>
      cvtpi2ps_operation _ _ _ (by exact hm) (by exact hok),
    Write_XMM => writeXMM128_run _ _ _ (by exact hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
