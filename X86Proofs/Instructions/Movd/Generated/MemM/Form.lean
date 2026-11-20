import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Mmx
import X86Proofs.Instructions.Movd.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem movd_m32_mm_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3) (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hosz : ctx.osz_prefix_present = false)
    (hrep : ctx.rep_prefix = 0)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hcr0 : Prelude.CR0.SSEEnabled t.CR0) (hes : fswES t.FP87_Status = 0)
    (hmw : MemWritable t lin 4) :
    (X86.Instructions.MOVD_MEMd_MMXd_0 ip ctx mod reg rm).run s =
      let src : Operand 64 := .mmx reg
      (.ok (), writeResult (mmxEnter (dataAccess t "store")) (.mem lin : Operand 32)
        (movdSpec 32 32 (src.read t)) next) := by
  have ht' : DataReady (withNextIP { t with FP87_Status := mmxStatus t.FP87_Status } next) :=
    ht.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
      ht.tables
  unfold X86.Instructions.MOVD_MEMd_MMXd_0
  simp only [haddr, hlock, hw, hosz, hrep]
  simp only [writeResult, mmxEnter, Operand.write, Operand.read_mmx]
  refine (specM_bind_run _ _ hea).trans ?_
  simp only [hrip, liftM_ok]
  spec_run [
    Read_MMX => readMMX_run _ _,
    X86.Runtime.CheckedSlice.read => checkedSliceRead_mmx_run _ _,
    X86.CR0.EM => cr0EM_run_of_cr0 hcr0,
    X86.CR0.TS => cr0TS_run_of_cr0 hcr0,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
    X86.FP87_Status.setTOP => fp87StatusSetTOP_run _,
    liftM => liftM_run_of_ok (mov_wdq_operation 32 64 32 (by decide) (by decide) (by decide) _) _,
    Logical_Mem_Write => logicalMemWrite_run_seg_align _ ht' seg addr lin hseg 32 (by decide) _
      .Normal_Alignment (AlignmentOk.normal _ _) hmw.low hmw.mem,
    X86.FP87_Tag_Word.assign => fp87TagWordAssign_run _ _]

end X86Proofs
