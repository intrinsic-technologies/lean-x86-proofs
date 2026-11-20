import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Mmx
import X86Proofs.Instructions.Maskmovq.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem maskmovq_mm_mm_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0) (hes : fswES s.FP87_Status = 0)
    (hrep : ctx.rep_prefix = 0) (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (haddr : ctx.address_size = 64)
    (hm64 : ctx.is_mode64 = true)
    (hsr : ctx.seg_prefix_present = true → SegReady ctx.segment)
    (h : DataReady s) (hds : s.DS = {userStackSegment with is_stack := some false})
    (hss : s.SS = userStackSegment) (hw : MemWritable s (segAddr ctx (rdi.read s)) 8) :
    (X86.Instructions.MASKMOVQ_MMXq_MMXq ip ctx reg rm).run s =
      let src : Operand 64 := .mmx reg
      let mask : Operand 64 := .mmx rm
      (.ok (), maskmovqState (segAddr ctx (rdi.read s)) (src.read s) (mask.read s) ip s) := by
  have ht : DataReady (withNextIP (mmxEnter s) ip) :=
    h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
      h.tables
  unfold X86.Instructions.MASKMOVQ_MMXq_MMXq
  simp only [haddr, hrep, hlock, hosz]
  spec_run [
    Read_MMX => readMMX_run _ _,
    X86.Runtime.CheckedSlice.read => checkedSliceRead_mmx_run _ _,
    X86.CR0.EM => cr0EM_run_of_cr0 hcr0,
    X86.CR0.TS => cr0TS_run_of_cr0 hcr0,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
    X86.FP87_Status.setTOP => fp87StatusSetTOP_run _,
    X86.FP87_Tag_Word.assign => fp87TagWordAssign_run _ _]
  exact maskmovq_operation _ ht ctx hm64 hds hss hsr _ _ (hw.of_external_eq rfl)

end X86Proofs
