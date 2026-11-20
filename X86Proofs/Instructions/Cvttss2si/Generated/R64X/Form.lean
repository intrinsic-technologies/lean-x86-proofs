import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Float
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Xorps.Form
import X86Proofs.Instructions.Cvtts2si.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cvttss2si_r64_xmm_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hevex : ctx.evex_prefix_present = false)
    (hm : MxcsrPre s)
    (hok : cvtts2siOk 32 64 s.MXCSR ((Operand.xmm (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 128).read s)) :
    (X86.Instructions.CVTTSS2SI_GPR64q_XMMss ip ctx 3 reg rm).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 128 := .xmm (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      some (.ok (), writeResult
        ((Operand.mxcsr : Operand 32).write s (mxOr s.MXCSR (cvtts2siFlags 32 64 s.MXCSR (src.read s))))
        dst (cvtts2siSpec 32 64 s.MXCSR (src.read s)) ip) := by
  unfold X86.Instructions.CVTTSS2SI_GPR64q_XMMss
  simp only [hlock, hw, calculateRM_run_of_mod3 rm ctx hevex, writeResult,
    Operand.write_reg64]
  pspec_run [
    Read_XMM => readXMM128_run _ _ hmode,
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    X86.Instructions.Operations.CVTTSf2SI => cvtts2si_operation 32 128 64 (.inl rfl) (.inr rfl) (.inr rfl) _ _ (by exact hm) (by exact hok),
    Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
