import X86Proofs.Program.ReadWrite.X87Mem
import X86Proofs.Instructions.Fld.Operation
import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem fild_m32_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (opcode : BitVec 8)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
        (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin) (ht : DataReady t)
    (hcr0 : Prelude.CR0.SSEEnabled t.CR0)
    (hes : fswES t.FP87_Status = 0)
    (hm : FcwMasked t.FP87_Control)
    (hfdp : Prelude.ReportsCPUFeature Bindings.processor t CPUID_FDP_EXCPTN_ONLY_Encoding true)
    (hmode : In64BitMode t)
    (hpush : ftwTag t.FP87_Tag_Word (fswTop t.FP87_Status + 7) = 3)
    (hlow : lin.toNat + 4 ≤ 2^32)
    (hmem : ∀ i, i < 4 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.FILD_ST0_MEMmem32int ip ctx mod reg rm opcode).run s =
      some (.ok (), x87Out (dataAccess t "load") next 3
        (fprSet t.FP87 (fswTop t.FP87_Status - 1)
            (x87FromInt (size := 32) ((Operand.mem lin : Operand 32).read t)))
        (ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status - 1)
            (x87Tag (x87FromInt (size := 32) ((Operand.mem lin : Operand 32).read t))))
        (fswSetTop (fldStatus t.FP87_Status (dataAccess t "load").oracle)
            (fswTop t.FP87_Status - 1))) := by
  have hfdp' : ∀ u : RamState, SameControls t u →
      Prelude.ReportsCPUFeature Bindings.processor u CPUID_FDP_EXCPTN_ONLY_Encoding true :=
    fun _ h => reportsCPUFeature_of_sameControls h hfdp
  have hread := logicalMemRead_run_seg t ht seg addr lin hseg 32 (by decide) .Memory_Read
    (.inl rfl) hlow hmem
  unfold X86.Instructions.FILD_ST0_MEMmem32int
  simp only [haddr, hlock]
  refine (partialSpecM_liftTotal_bind_run _ _ hea).trans ?_
  simp only [hrip]
  pspec_run_until [FP87.Is_Enabled => isEnabled_run hcr0,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes]
  pspec_run_until [Logical_Mem_Read => hread,
    FP87.Convert_From_Integer => partialResult_lift_run (fp87ConvertFromInteger_eq32 _) _]
  refine (partialSpecM_liftTotal_bind_run _ _
    (fld_operation _ _ 0 true (.inl rfl) ?_ ?_)).trans ?_
  · exact hpush
  · exact hm
  pspec_run_until [FP87.Push => push_run _, X86.Helpers.ST_write => stWrite_run _ _ 0 rfl _]
  refine (partialSpecM_liftTotal_run _ (updateInstructionInfo_run _ _ _ _ _ _ ?_ ?_ ?_)).trans ?_
  · exact hmode.of_cs_lma_eq rfl rfl
  · simpa using hes
  · exact hfdp' _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [fswTop_fswSetTop, fswTop_fldStatus, add_zero3']
  rfl

end X86Proofs
