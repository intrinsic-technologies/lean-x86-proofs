import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Xorps.Form
import X86Proofs.Instructions.Movss.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem movsd_xmm_xmm_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hlock : ctx.lock_prefix_present = false)
    (hvex : ctx.vex_prefix_present = false)
    (hevex : ctx.evex_prefix_present = false) :
    (X86.Instructions.MOVSD_XMM_XMMsd_XMMsd_0F10 ip ctx 3 reg rm).run s =
      let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 128 := .xmm (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst (movsRegSpec 64 (dst.read s) (src.read s)) ip) := by
  have hm' : In64BitMode { s with Next_IP := ip } := hmode.of_cs_lma_eq rfl rfl
  unfold X86.Instructions.MOVSD_XMM_XMMsd_XMMsd_0F10
  simp only [hlock, hvex, hevex, calculateRM_run_of_mod3 rm ctx hevex, liftM_ok]
  spec_run [
    Read_XMM => readXMM128_run _ _ hmode,
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    liftM => liftM_run_of_ok (movs_reg_operation 64 (by decide) _ _) _]
  refine (writeXMM128_run _ _ _ hm').trans ?_
  simp only [writeResult, Operand.write_xmm, Operand.read_xmm, concatBits_xmm_reg]

end X86Proofs
