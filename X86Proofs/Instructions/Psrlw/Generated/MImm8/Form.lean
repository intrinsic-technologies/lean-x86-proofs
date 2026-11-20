import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Mmx
import X86Proofs.Instructions.Psrl.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem psrlw_mm_imm8_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (imm : BitVec 8)
    (hcr0 : Prelude.CR0.SSEEnabled t.CR0) (hes : fswES t.FP87_Status = 0)
    (hrep : ctx.rep_prefix = 0) (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) :
    (X86.Instructions.PSRLW_MMXq_IMMb ip ctx rm).run s =
      let dst : Operand 64 := .mmx rm
      (.ok (), writeResult (mmxEnter t) dst (psrlMmxSpec 16 (dst.read s) imm.toNat)
        (BitVec.add ip 1#64)) := by
  unfold X86.Instructions.PSRLW_MMXq_IMMb
  simp only [hrep, hlock, hosz]
  simp only [writeResult, mmxEnter, Operand.write_mmx, Operand.read_mmx]
  spec_run [
    Read_MMX => readMMX_run _ _,
    X86.Runtime.CheckedSlice.read => checkedSliceRead_mmx_run _ _,
    Mem_Fetch => hfetch,
    Std.Bits.Sign_Extend => signExtend8_run _ _,
    X86.CR0.EM => cr0EM_run_of_cr0 hcr0,
    X86.CR0.TS => cr0TS_run_of_cr0 hcr0,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
    X86.FP87_Status.setTOP => fp87StatusSetTOP_run _,
    liftM => liftM_run_of_ok (psrl_mmx_imm_operation 16 (by decide) _ _) _,
    Write_MMX => writeMMX_run _ _ _,
    X86.FP87_Tag_Word.assign => fp87TagWordAssign_run _ _]

end X86Proofs
