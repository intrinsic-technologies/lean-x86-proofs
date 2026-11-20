import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Mmx
import X86Proofs.Instructions.Paddus.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem paddusw_mm_m_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3) (haddr : ctx.address_size = asz)
    (hrep : ctx.rep_prefix = 0) (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hcr0 : Prelude.CR0.SSEEnabled t.CR0) (hes : fswES t.FP87_Status = 0)
    (hlow : lin.toNat + 8 ≤ 2^32)
    (hmem : ∀ i, i < 8 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.PADDUSW_MMXq_MEMq ip ctx mod reg rm).run s =
      let dst : Operand 64 := .mmx reg
      let x := (Operand.mem lin : Operand 64).read t
      (.ok (), writeResult (mmxEnter (dataAccess t "load")) dst
        (paddusMmxSpec 16 (dst.read t) x) next) := by
  have hread := logicalMemRead_run_seg t ht seg addr lin hseg 64 (by decide) .Memory_Read
    (.inl rfl) hlow hmem
  unfold X86.Instructions.PADDUSW_MMXq_MEMq
  simp only [haddr, hrep, hlock, hosz]
  simp only [writeResult, mmxEnter, Operand.write_mmx, Operand.read_mmx]
  refine (specM_bind_run _ _ hea).trans ?_
  simp only [hrip, liftM_ok]
  spec_run [
    Read_MMX => readMMX_run _ _,
    X86.Runtime.CheckedSlice.read => checkedSliceRead_mmx_run _ _,
    X86.CR0.EM => cr0EM_run_of_cr0 hcr0,
    X86.CR0.TS => cr0TS_run_of_cr0 hcr0,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
    Logical_Mem_Read => hread,
    X86.FP87_Status.setTOP => fp87StatusSetTOP_run _,
    liftM => liftM_run_of_ok (paddus_mmx_operation 16 (by decide) _ _) _,
    Write_MMX => writeMMX_run _ _ _,
    X86.FP87_Tag_Word.assign => fp87TagWordAssign_run _ _]

end X86Proofs
