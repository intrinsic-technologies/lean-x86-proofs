import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Mmx
import X86Proofs.Instructions.Psubus.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem psubusb_mm_mm_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0) (hes : fswES s.FP87_Status = 0)
    (hrep : ctx.rep_prefix = 0) (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) :
    (X86.Instructions.PSUBUSB_MMXq_MMXq ip ctx reg rm).run s =
      let dst : Operand 64 := .mmx reg
      let src : Operand 64 := .mmx rm
      (.ok (), writeResult (mmxEnter s) dst (psubusMmxSpec 8 (dst.read s) (src.read s)) ip) := by
  unfold X86.Instructions.PSUBUSB_MMXq_MMXq
  simp only [hrep, hlock, hosz]
  simp only [writeResult, mmxEnter, Operand.write_mmx, Operand.read_mmx]
  spec_run [
    Read_MMX => readMMX_run _ _,
    X86.Runtime.CheckedSlice.read => checkedSliceRead_mmx_run _ _,
    X86.CR0.EM => cr0EM_run_of_cr0 hcr0,
    X86.CR0.TS => cr0TS_run_of_cr0 hcr0,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
    X86.FP87_Status.setTOP => fp87StatusSetTOP_run _,
    liftM => liftM_run_of_ok (psubus_mmx_operation 8 (by decide) _ _) _,
    Write_MMX => writeMMX_run _ _ _,
    X86.FP87_Tag_Word.assign => fp87TagWordAssign_run _ _]

end X86Proofs
