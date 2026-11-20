import X86Proofs.Program.ReadWrite.X87Mem
import X86Proofs.Instructions.Fnstsw.Operation
import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem fnstsw_m16_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context)
    (mod : BitVec 2) (rm : BitVec 3)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
        (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin) (ht : DataReady t)
    (hcr0 : Prelude.CR0.SSEEnabled t.CR0)
    (hlow : lin.toNat + 2 ≤ 2^32)
    (hmem : ∀ i, i < 2 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.FNSTSW_MEMmem16 ip ctx mod rm).run s =
      (.ok (), (Operand.mem lin : Operand 16).write
          (dataAccess (x87CtlOut t next 4 (fswCCOracle t.FP87_Status t.oracle)) "store")
          t.FP87_Status) := by
  have hwrite (u : RamState) (hu : DataReady u) (hext : u.external = t.external)
      (v : BitVec 16) :=
    logicalMemWrite_run_seg u hu seg addr lin hseg 16 (by decide) v hlow
      (by rw [hext]; exact hmem)
  unfold X86.Instructions.FNSTSW_MEMmem16
  simp only [haddr, hlock]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run_until [FP87.Is_Enabled => isEnabled_run hcr0]
  refine specM_tryCatch_run _ _ ?_
  spec_run_until [X86.Instructions.Operations.FNSTSW => fnstsw_m_operation _]
  refine (hwrite _ ?_ (by rfl) _).trans ?_
  · exact ht.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl
      rfl rfl ht.tables
  rfl

end X86Proofs
