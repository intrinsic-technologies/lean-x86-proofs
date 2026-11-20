import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Float
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Xorps.Form
import X86Proofs.Instructions.Cvts2si.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cvtss2si_r32_xmm_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hevex : ctx.evex_prefix_present = false)
    (hevexb : ctx.evex_b = 0)
    (hm : MxcsrPre s)
    (hok : cvts2siOk 32 32 s.MXCSR ((Operand.xmm (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 128).read s)) :
    (X86.Instructions.CVTSS2SI_GPR32d_XMMss ip ctx 3 reg rm).run s =
      let dst : Operand 32 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 128 := .xmm (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      some (.ok (), writeResult
        ((Operand.mxcsr : Operand 32).write s (mxOr s.MXCSR (cvts2siFlags 32 32 s.MXCSR (src.read s))))
        dst (cvts2siSpec 32 32 s.MXCSR (src.read s)) ip) := by
  unfold X86.Instructions.CVTSS2SI_GPR32d_XMMss
  simp only [hlock, hw, calculateRM_run_of_mod3 rm ctx hevex, writeResult,
    Operand.write_reg32]
  pspec_run [
    Read_XMM => readXMM128_run _ _ hmode,
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    X86.Instructions.Operations.CVTSf2SI => cvts2si_operation 32 128 32 (.inl rfl) (.inr rfl) (.inl rfl) _ _ _ _ hevexb (by exact hm) (by exact hok),
    Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
