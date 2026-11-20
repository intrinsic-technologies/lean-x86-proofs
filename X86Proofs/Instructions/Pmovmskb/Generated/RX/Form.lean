import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Xorps.Form
import X86Proofs.Instructions.Movmsk.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem pmovmskb_r32_xmm_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hrep : ctx.rep_prefix = 0)
    (hlock : ctx.lock_prefix_present = false)
    (hevex : ctx.evex_prefix_present = false) :
    (X86.Instructions.PMOVMSKB_GPR32_XMMdq ip ctx 3 reg rm).run s =
      let dst : Operand 32 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 128 := .xmm (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst (movmskSpec 8 (src.read s)) ip) := by
  unfold X86.Instructions.PMOVMSKB_GPR32_XMMdq
  simp only [hrep, hlock, calculateRM_run_of_mod3 rm ctx hevex, liftM_ok, writeResult,
    Operand.write_reg32]
  spec_run [
    Read_XMM => readXMM128_run _ _ hmode,
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    liftM => liftM_run_of_ok (movmsk_operation 8 (by decide) _) _,
    Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
