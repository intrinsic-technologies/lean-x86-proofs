import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Float
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Xorps.Form
import X86Proofs.Instructions.Cmpfs.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cmpss_xmm_xmm_imm8_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (imm : BitVec 8) (hmode : In64BitMode s)
    (hmt : In64BitMode t) (hsse : Prelude.SupportedSSE Bindings.processor t)
    (hlock : ctx.lock_prefix_present = false)
    (hvex : ctx.vex_prefix_present = false)
    (hevex : ctx.evex_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t))
    (hm : MxcsrPre t)
    (hok : cmpfsOk 32 t.MXCSR ((Operand.xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 128).read s)
      ((Operand.xmm (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 32).read s) imm) :
    (X86.Instructions.CMPSS_XMMss_XMMss_IMMb ip ctx 3 reg rm).run s =
      let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 32 := .xmm (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult
        ((Operand.mxcsr : Operand 32).write t
          (mxOr t.MXCSR (cmpfsFlags 32 t.MXCSR (dst.read s) (src.read s) imm)))
        dst (cmpfsSpec 32 t.MXCSR (dst.read s) (src.read s) imm) (BitVec.add ip 1#64)) := by
  have hm' : In64BitMode
      { t with Next_IP := BitVec.add ip 1#64, MXCSR := mxOr t.MXCSR (cmpfsFlags 32 t.MXCSR
        ((Operand.xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 128).read s)
        ((Operand.xmm (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 32).read s) imm) } :=
    hmt.of_cs_lma_eq rfl rfl
  unfold X86.Instructions.CMPSS_XMMss_XMMss_IMMb
  simp only [hlock, hvex, hevex, calculateRM_run_of_mod3 rm ctx hevex, liftM_ok]
  spec_run [
    Read_XMM => readXMM_run _ _ _ (by decide) (by decide) hmode,
    Mem_Fetch => hfetch,
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    X86.Instructions.Operations.CMP3Sf => cmpfs_operation 32 (by decide) _ _ _ _ (by exact hm) (by exact hok)]
  refine (writeXMM128_run _ _ _ hm').trans ?_
  simp only [writeResult, Operand.write_xmm, Operand.write_mxcsr, Operand.read_xmm,
    concatBits_xmm_reg]
  rfl

end X86Proofs
