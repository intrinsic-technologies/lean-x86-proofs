import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Xorps.Form
import X86Proofs.Instructions.Shufp.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

attribute [local irreducible] X86.Instructions.Operations.SHUFP_lanes

theorem shufpd_xmm_xmm_imm8_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (imm : BitVec 8) (hmode : In64BitMode s)
    (hmt : In64BitMode t) (hsse : Prelude.SupportedSSE Bindings.processor t)
    (hrep : ctx.rep_prefix = 0)
    (hlock : ctx.lock_prefix_present = false)
    (hvex : ctx.vex_prefix_present = false)
    (hevex : ctx.evex_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) :
    (X86.Instructions.SHUFPD_XMMpd_XMMpd_IMMb ip ctx 3 reg rm).run s =
      let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 128 := .xmm (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      some (.ok (), writeResult t dst (shufpdSpec (dst.read s) (src.read s) imm)
        (BitVec.add ip 1#64)) := by
  unfold X86.Instructions.SHUFPD_XMMpd_XMMpd_IMMb
  simp only [hrep, hlock, hvex, hevex, calculateRM_run_of_mod3 rm ctx hevex]
  pspec_run [
    Read_XMM => readXMM128_run _ _ hmode,
    Mem_Fetch => hfetch,
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    Instructions.Operations.SHUFP_lanes =>
      partialResult_lift_run (shufpd_operation _ _ _) _]
  refine (partialSpecM_liftTotal_run _ (writeXMM128_run _ _ _ ?hm)).trans ?_
  case hm => exact hmt.of_cs_lma_eq rfl rfl
  simp only [writeResult, Operand.write_xmm, Operand.read_xmm, concatBits_xmm_reg]
  rfl

end X86Proofs
