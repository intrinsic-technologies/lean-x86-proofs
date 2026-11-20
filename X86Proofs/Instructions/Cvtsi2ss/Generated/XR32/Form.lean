import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Float
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Xorps.Form
import X86Proofs.Instructions.Cvtsi2s.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cvtsi2ss_xmm_r32_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hvex : ctx.vex_prefix_present = false)
    (hevex : ctx.evex_prefix_present = false)
    (hevexb : ctx.evex_b = 0)
    (hm : MxcsrPre s)
    (hok : cvtsi2sOk 32 32 s.MXCSR ((Operand.xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 128).read s)
      ((Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 32).read s)) :
    (X86.Instructions.CVTSI2SS_XMMss_GPR32d ip ctx 3 reg rm).run s =
      let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 32 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult
        ((Operand.mxcsr : Operand 32).write s
          (mxOr s.MXCSR (cvtsi2sFlags 32 32 s.MXCSR (dst.read s) (src.read s))))
        dst (cvtsi2sSpec 32 32 s.MXCSR (dst.read s) (src.read s)) ip) := by
  have hm' : In64BitMode
      { s with Next_IP := ip, MXCSR := mxOr s.MXCSR (cvtsi2sFlags 32 32 s.MXCSR
        ((Operand.xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 128).read s)
        ((Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 32).read s)) } :=
    hmode.of_cs_lma_eq rfl rfl
  unfold X86.Instructions.CVTSI2SS_XMMss_GPR32d
  simp only [hlock, hw, hvex, hevex]
  spec_run [
    Read_XMM => readXMM128_run _ _ hmode,
    Read_GPR => readGPR32_run _ _ hmode,
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    X86.Instructions.Operations.CVTSI2Sf => cvtsi2s_operation 32 32 (.inl rfl) (.inl rfl) _ _ _ _ _ hevexb (by exact hm) (by exact hok)]
  refine (writeXMM128_run _ _ _ hm').trans ?_
  simp only [writeResult, Operand.write_xmm, Operand.write_mxcsr, Operand.read_xmm,
    Operand.read_reg32, concatBits_xmm_reg]

end X86Proofs
