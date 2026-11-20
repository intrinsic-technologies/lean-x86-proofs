import X86Proofs.Program.ReadWrite.X87Mem
import X86Proofs.Instructions.Fld.Operation
import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem fld_m80_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (opcode : BitVec 8)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
        (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin) (hseg8 : SegAccess seg (addr + 8) (lin + 8))
    (ht : DataReady t)
    (hcr0 : Prelude.CR0.SSEEnabled t.CR0)
    (hes : fswES t.FP87_Status = 0)
    (hm : FcwMasked t.FP87_Control)
    (hfdp : Prelude.ReportsCPUFeature Bindings.processor t CPUID_FDP_EXCPTN_ONLY_Encoding true)
    (hmode : In64BitMode t)
    (hpush : ftwTag t.FP87_Tag_Word (fswTop t.FP87_Status + 7) = 3)
    (hlow : lin.toNat + 10 ≤ 2^32)
    (hmem : ∀ i, i < 10 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.FLD_ST0_MEMmem80real ip ctx mod reg rm opcode).run s =
      (.ok (), x87Out
          (dataAccess (dataAccess { t with oracle := oracleSkip t.oracle 464 } "load") "load") next
          3
        (fprSet t.FP87 (fswTop t.FP87_Status - 1) ((Operand.mem lin : Operand 80).read t))
        (ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status - 1)
            (x87Tag ((Operand.mem lin : Operand 80).read t)))
        (fswSetTop
            (fldStatus t.FP87_Status (oracleSkip (oracleSkip (oracleSkip t.oracle 464) 464) 464))
            (fswTop t.FP87_Status - 1))) := by
  have hfdp' : ∀ u : RamState, SameControls t u →
      Prelude.ReportsCPUFeature Bindings.processor u CPUID_FDP_EXCPTN_ONLY_Encoding true :=
    fun _ h => reportsCPUFeature_of_sameControls h hfdp
  have hlin8 : (lin + 8).toNat = lin.toNat + 8 := by
    rw [BitVec.toNat_add, show (8 : BitVec 64).toNat = 8 from rfl]
    omega
  have hcheck := checkLogicalAddressIsReadable80_run_seg t ht seg addr lin hseg hlow
  have hread (u : RamState) (hu : DataReady u) (hext : u.external = t.external) :=
    logicalMemRead_run_seg u hu seg addr lin hseg 64 (by decide) .Memory_Read
      (.inl rfl) (by omega) (by rw [hext]; exact fun i hi => hmem i (by omega))
  have hread8 (u : RamState) (hu : DataReady u) (hext : u.external = t.external) :=
    logicalMemRead_run_seg u hu seg (addr + 8) (lin + 8) hseg8 16 (by decide) .Memory_Read
      (.inl rfl) (by omega) (by
        rw [hext]
        intro i hi
        rw [ofNat_add_eight]
        exact hmem _ (by omega))
  unfold X86.Instructions.FLD_ST0_MEMmem80real
  simp only [haddr, hlock]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run_until [FP87.Is_Enabled => isEnabled_run hcr0,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes]
  refine (specM_bind_run _ _ hcheck).trans ?_
  refine (specM_bind_run _ _ (hread _ (ht.oracle (oracleSkip t.oracle 464)) rfl)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) addr 8)) _
    (value := (addr + 8 : BitVec 64)) rfl).trans ?_
  refine (specM_bind_run _ _
    (hread8 _ ((ht.oracle (oracleSkip t.oracle 464)).dataAccess "load") rfl)).trans ?_
  refine (specM_bind_run _ _
    (s := dataAccess (dataAccess { t with oracle := oracleSkip t.oracle 464 } "load") "load")
    (t := dataAccess (dataAccess { t with oracle := oracleSkip t.oracle 464 } "load") "load")
    (value := (Operand.mem lin : Operand 80).read t) ?_).trans ?_
  · rw [show (Operand.mem lin : Operand 80).read t = memLoad t.external (lin + 8) 16 ++
      memLoad t.external lin 64 from memLoad80 _ _, ← ofNat_shiftLeft_add_eq_append_any,
      concatBits_eq_pure _ _ (by decide) (by decide)]
    rfl
  spec_run_until []
  refine (specM_bind_run _ _ (fld_operation _ _ 0 true (.inl rfl) ?_ ?_)).trans ?_
  · exact hpush
  · exact hm
  spec_run_until [FP87.Push => push_run _, X86.Helpers.ST_write => stWrite_run _ _ 0 rfl _]
  refine (updateInstructionInfo_run _ _ _ _ _ _ ?_ ?_ ?_).trans ?_
  · exact hmode.of_cs_lma_eq rfl rfl
  · simpa using hes
  · exact hfdp' _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [fswTop_fswSetTop, fswTop_fldStatus, add_zero3', x87Out, dataAccess]

end X86Proofs
