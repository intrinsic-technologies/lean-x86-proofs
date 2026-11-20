import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Float
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Xorps.Form
import X86Proofs.Instructions.Ucomis.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem ucomiss_xmm_xmm_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hrep : ctx.rep_prefix = 0)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hevex : ctx.evex_prefix_present = false)
    (hevexb : ctx.evex_b = 0)
    (hm : MxcsrPre s)
    (hok : ucomisOk 32 s.MXCSR ((Operand.xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 128).read s)
      ((Operand.xmm (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 32).read s)) :
    (X86.Instructions.UCOMISS_XMMss_XMMss ip ctx 3 reg rm).run s =
      let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 32 := .xmm (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeFpFlags s (mxOr s.MXCSR (ucomisExc 32 s.MXCSR (dst.read s) (src.read s)))
        (ucomisFlags 32 s.MXCSR (dst.read s) (src.read s)) ip) := by
  unfold X86.Instructions.UCOMISS_XMMss_XMMss
  simp only [hrep, hlock, hosz, calculateRM_run_of_mod3 rm ctx hevex, liftM_ok]
  spec_run [
    Read_XMM => readXMM_run _ _ _ (by decide) (by decide) hmode,
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    X86.Instructions.Operations.UCOMISf => ucomis_operation 32 (by decide) _ _ _ _ _ hevexb (by exact hm) (by exact hok)]

end X86Proofs
