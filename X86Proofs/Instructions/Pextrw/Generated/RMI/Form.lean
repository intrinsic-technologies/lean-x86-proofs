import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Mmx
import X86Proofs.Instructions.Pextrw.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem pextrw_r32_mm_imm8_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (imm : BitVec 8) (hmt : In64BitMode t)
    (hcr0 : Prelude.CR0.SSEEnabled t.CR0) (hes : fswES t.FP87_Status = 0)
    (hrep : ctx.rep_prefix = 0) (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) :
    (X86.Instructions.PEXTRW_GPR32_MMXq_IMMb ip ctx reg rm).run s =
      let dst : Operand 32 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 64 := .mmx rm
      some (.ok (), writeResult (mmxEnter t) dst (pextrwMmxSpec (src.read s) imm)
        (BitVec.add ip 1#64)) := by
  unfold X86.Instructions.PEXTRW_GPR32_MMXq_IMMb
  simp only [hrep, hlock, hosz]
  simp only [writeResult, mmxEnter, Operand.write_reg32, Operand.read_mmx]
  pspec_run [    Read_MMX => readMMX_run _ _,
    X86.Runtime.CheckedSlice.read => checkedSliceRead_mmx_prun _ _,
    Mem_Fetch => hfetch,
    X86.CR0.EM => cr0EM_run_of_cr0 hcr0,
    X86.CR0.TS => cr0TS_run_of_cr0 hcr0,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
    X86.FP87_Status.setTOP => fp87StatusSetTOP_run _,
    Instructions.Operations.PEXTR =>
      partialResult_lift_run (pextrw_mmx_operation _ _) _,
    Write_GPR => writeGPR32_run _ _ _ (by exact hmt.of_cs_lma_eq rfl rfl),
    X86.FP87_Tag_Word.assign => fp87TagWordAssign_run _ _]

end X86Proofs
