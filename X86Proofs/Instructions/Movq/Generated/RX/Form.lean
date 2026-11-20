import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Xorps.Form
import X86Proofs.Instructions.Movd.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem movq_r64_xmm_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hrep : ctx.rep_prefix = 0)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1) :
    (X86.Instructions.MOVQ_GPR64_XMMq ip ctx reg rm).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult s dst (movdSpec 64 64 (src.read s)) ip) := by
  unfold X86.Instructions.MOVQ_GPR64_XMMq
  simp only [hrep, hlock, hw, writeResult, Operand.write_reg64]
  spec_run [
    Read_XMM => readXMM128_run _ _ hmode,
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    liftM => liftM_run_of_ok (mov_wdq_operation 64 128 64 (by decide) (by decide) (by decide) _) _,
    Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
