import X86Proofs.Program.ReadWrite.X87Mem
import X86Proofs.Instructions.Fldcw.Operation
import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem fldcw_m16_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context)
    (mod : BitVec 2) (rm : BitVec 3)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
        (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin) (ht : DataReady t)
    (hcr0 : Prelude.CR0.SSEEnabled t.CR0)
    (hes : fswES t.FP87_Status = 0)
    (hfm : FcwMasked (fldcwWord ((Operand.mem lin : Operand 16).read t)))
    (hlow : lin.toNat + 2 ≤ 2^32)
    (hmem : ∀ i, i < 2 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.FLDCW_MEMmem16 ip ctx mod rm).run s =
      (.ok (), x87LdcwOut (dataAccess t "load") next 4
          (fldcwWord ((Operand.mem lin : Operand 16).read t))
          (fswCCOracle t.FP87_Status (dataAccess t "load").oracle)) := by
  have hread := logicalMemRead_run_seg t ht seg addr lin hseg 16 (by decide) .Memory_Read
    (.inl rfl) hlow hmem
  unfold X86.Instructions.FLDCW_MEMmem16
  simp only [haddr, hlock]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [FP87.Is_Enabled => isEnabled_run hcr0,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.FLDCW => fldcw_operation _ _ hfm]

end X86Proofs
