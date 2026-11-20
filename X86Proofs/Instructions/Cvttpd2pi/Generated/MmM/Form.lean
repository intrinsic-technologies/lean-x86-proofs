import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Mmx
import X86Proofs.Instructions.Xorps.Form
import X86Proofs.Instructions.Cvttpd2dq.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cvttpd2pi_mm_m_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false)
    (hrep : ctx.rep_prefix = 0)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hsse : Prelude.SupportedSSE Bindings.processor t)
    (hes : fswES t.FP87_Status = 0) (halign : lin.toNat % 16 = 0)
    (hlow : lin.toNat + 16 ≤ 2^32)
    (hmem : ∀ i, i < 16 → (t.external[lin + BitVec.ofNat 64 i]?).isSome)
    (hm : MxcsrPre t) (hok : cvttpd2piOk t.MXCSR ((Operand.mem lin : Operand 128).read t)) :
    (X86.Instructions.CVTTPD2PI_MMXq_MEMpd ip ctx mod reg rm).run s =
      let dst : Operand 64 := .mmx reg
      let x := (Operand.mem lin : Operand 128).read t
      some (.ok (), writeResult
        (mmxEnter ((Operand.mxcsr : Operand 32).write (dataAccess t "load")
          (mxOr t.MXCSR (cvttpd2piFlags t.MXCSR x))))
        dst (cvttpd2piSpec t.MXCSR x) next) := by
  have hread := logicalMemRead_run_seg_align t ht seg addr lin hseg 128 (by decide)
    .Memory_Read (.inl rfl) .Explicitly_Aligned (fun _ => halign) hlow hmem
  unfold X86.Instructions.CVTTPD2PI_MMXq_MEMpd
  simp only [haddr, hlock, hrep]
  simp only [writeResult, mmxEnter, Operand.write_mmx, Operand.write_mxcsr]
  pspec_run [
    Effective_Address => hea,
    Handle_RIP_Relative_Address => partialSpecM_liftM_run_of_ok hrip _,
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
    Logical_Mem_Read => hread,
    X86.FP87_Status.setTOP => fp87StatusSetTOP_run _,
    X86.FP87_Tag_Word.assign => fp87TagWordAssign_run _ _,
    X86.Instructions.Operations.CVTTPg2i =>
      cvttpd2pi_operation _ _ (by exact hm) (by exact hok),
    Write_MMX => writeMMX_run _ _ _]

end X86Proofs
