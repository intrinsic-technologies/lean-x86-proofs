import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Mmx
import X86Proofs.Instructions.Pinsrw.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem pinsrw_mm_r32_imm8_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (imm : BitVec 8) (hmode : In64BitMode s)
    (hcr0 : Prelude.CR0.SSEEnabled t.CR0) (hes : fswES t.FP87_Status = 0)
    (hrep : ctx.rep_prefix = 0) (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) :
    (X86.Instructions.PINSRW_MMXq_GPR32_IMMb ip ctx reg rm).run s =
      let dst : Operand 64 := .mmx reg
      let src : Operand 32 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      some (.ok (), writeResult (mmxEnter t) dst (pinsrwMmxSpec (dst.read s) (src.read s) imm)
        (BitVec.add ip 1#64)) := by
  unfold X86.Instructions.PINSRW_MMXq_GPR32_IMMb
  simp only [hrep, hlock, hosz]
  simp only [writeResult, mmxEnter, Operand.write_mmx, Operand.read_mmx, Operand.read_reg32]
  pspec_run [    Read_MMX => readMMX_run _ _,
    X86.Runtime.CheckedSlice.read => checkedSliceRead_mmx_prun _ _,
    Read_GPR => readGPR32_run _ _ hmode,
    Mem_Fetch => hfetch,
    X86.CR0.EM => cr0EM_run_of_cr0 hcr0,
    X86.CR0.TS => cr0TS_run_of_cr0 hcr0,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
    X86.FP87_Status.setTOP => fp87StatusSetTOP_run _,
    Instructions.Operations.PINSR =>
      partialResult_lift_run (pinsrw_mmx_operation 32 (by decide) _ _ _) _,
    Write_MMX => writeMMX_run _ _ _,
    X86.FP87_Tag_Word.assign => fp87TagWordAssign_run _ _]

end X86Proofs
