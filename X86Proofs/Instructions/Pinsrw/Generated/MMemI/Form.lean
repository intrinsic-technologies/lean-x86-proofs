import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Mmx
import X86Proofs.Instructions.Pinsrw.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem pinsrw_mm_m_imm8_form [Bindings] {asz : Int} (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (haddr : ctx.address_size = asz)
    (hrep : ctx.rep_prefix = 0) (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool} (imm : BitVec 8)
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch next 8).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address asz isRip off (BitVec.add next 1#64) = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (hu : DataReady u) (hcr0 : Prelude.CR0.SSEEnabled u.CR0) (hes : fswES u.FP87_Status = 0)
    (hlow : lin.toNat + 2 ≤ 2^32)
    (hmem : ∀ i, i < 2 → (u.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.PINSRW_MMXq_MEMw_IMMb ip ctx mod reg rm).run s =
      let dst : Operand 64 := .mmx reg
      let x := (Operand.mem lin : Operand 16).read u
      some (.ok (), writeResult (mmxEnter (dataAccess u "load")) dst
        (pinsrwMmxSpec (dst.read t) x imm) (BitVec.add next 1#64)) := by
  have hread := logicalMemRead_run_seg u hu seg addr lin hseg 16 (by decide) .Memory_Read
    (.inl rfl) hlow hmem
  unfold X86.Instructions.PINSRW_MMXq_MEMw_IMMb
  simp only [haddr, hrep, hlock, hosz]
  simp only [writeResult, mmxEnter, Operand.write_mmx, Operand.read_mmx]
  pspec_run [
    Effective_Address => hea,
    Read_MMX => readMMX_run _ _,
    X86.Runtime.CheckedSlice.read => checkedSliceRead_mmx_prun _ _,
    Mem_Fetch => hfetch,
    Handle_RIP_Relative_Address => partialSpecM_liftM_run_of_ok hrip _,
    X86.CR0.EM => cr0EM_run_of_cr0 hcr0,
    X86.CR0.TS => cr0TS_run_of_cr0 hcr0,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
    Logical_Mem_Read => hread,
    X86.FP87_Status.setTOP => fp87StatusSetTOP_run _,
    Instructions.Operations.PINSR =>
      partialResult_lift_run (pinsrw_mmx_operation 16 (by decide) _ _ _) _,
    Write_MMX => writeMMX_run _ _ _,
    X86.FP87_Tag_Word.assign => fp87TagWordAssign_run _ _]

end X86Proofs
