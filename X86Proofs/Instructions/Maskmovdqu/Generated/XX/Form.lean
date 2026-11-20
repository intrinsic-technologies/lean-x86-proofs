import X86Proofs.Step.Sse
import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Xorps.Form
import X86Proofs.Instructions.Maskmovdqu.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem maskmovdqu_xmm_xmm_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hrep : ctx.rep_prefix = 0)
    (hlock : ctx.lock_prefix_present = false)
    (hevex : ctx.evex_prefix_present = false)
    (haddr : ctx.address_size = 64)
    (hm64 : ctx.is_mode64 = true)
    (hsr : ctx.seg_prefix_present = true → SegReady ctx.segment)
    (h : DataReady s) (hds : s.DS = {userStackSegment with is_stack := some false})
    (hss : s.SS = userStackSegment) (hw : MemWritable s (segAddr ctx (rdi.read s)) 16) :
    (X86.Instructions.MASKMOVDQU_XMMxub_XMMxub ip ctx 3 reg rm).run s =
      let src : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let mask : Operand 128 := .xmm (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), maskmovState (segAddr ctx (rdi.read s)) (src.read s) (mask.read s) ip s) := by
  unfold X86.Instructions.MASKMOVDQU_XMMxub_XMMxub
  simp only [haddr, hrep, hlock, calculateRM_run_of_mod3 rm ctx hevex, liftM_ok]
  spec_run [
    Read_XMM => readXMM128_run _ _ hmode,
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse]
  simp only [concatBits_xmm_reg]
  exact maskmovdqu_operation _ (h.withNextIP ip) ctx hm64 hds hss hsr _ _ (hw.of_external_eq rfl)

end X86Proofs
