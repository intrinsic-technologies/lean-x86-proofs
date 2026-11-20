import X86Proofs.Program.ReadWrite.X87Mem
import X86Proofs.Instructions.Fst.Operation
import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem fstp_m80_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
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
    (h0 : ftwTag t.FP87_Tag_Word (fswTop t.FP87_Status) ≠ 3)
    (hlow : lin.toNat + 10 ≤ 2^32)
    (htables : PageTableEntriesApart lin.toNat (10))
    (hmem : ∀ i, i < 10 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.FSTP_MEMmem80real_ST0 ip ctx mod reg rm opcode).run s =
      (.ok (), x87Out
          ((Operand.mem lin : Operand 80).write
          (dataAccess (dataAccess { t with oracle := oracleSkip t.oracle 464 } "store") "store")
          t.FP87[fprIndex (fswTop t.FP87_Status)]) next 3
        (t.FP87)
        (ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status) 3)
        (fswSetTop
            (fstStatus t.FP87_Status (oracleSkip (oracleSkip (oracleSkip t.oracle 464) 464) 464))
            (fswTop t.FP87_Status + 1))) := by
  have hfdp' : ∀ u : RamState, SameControls t u →
      Prelude.ReportsCPUFeature Bindings.processor u CPUID_FDP_EXCPTN_ONLY_Encoding true :=
    fun _ h => reportsCPUFeature_of_sameControls h hfdp
  have hlin8 : (lin + 8).toNat = lin.toNat + 8 := by
    rw [BitVec.toNat_add, show (8 : BitVec 64).toNat = 8 from rfl]
    omega
  have hcheck (u : RamState) (hu : DataReady u) :=
    checkLogicalAddressIsWritable_run_seg u hu seg (addr + 8) (lin + 8) hseg8 16 (by decide)
      (by omega)
  have hwrite (u : RamState) (hu : DataReady u) (hext : u.external = t.external)
      (v : BitVec 64) :=
    logicalMemWrite_run_seg u hu seg addr lin hseg 64 (by decide) v (by omega)
      (by rw [hext]; exact fun i hi => hmem i (by omega))
  have hwrite8 (u : RamState) (hu : DataReady u) (v₀ : BitVec 64)
      (hext : u.external = memStore t.external lin v₀) (v : BitVec 16) :=
    logicalMemWrite_run_seg u hu seg (addr + 8) (lin + 8) hseg8 16 (by decide) v (by omega)
      (by
        rw [hext]
        intro i hi
        rw [ofNat_add_eight]
        exact memStore_isSome _ _ _ _ (hmem _ (by omega)))
  rw
      [← x87CommitFsw_fst t.FP87_Status (oracleSkip (oracleSkip (oracleSkip t.oracle 464) 464) 464),
      ← x87CommitFsw_fswSetTop]
  unfold X86.Instructions.FSTP_MEMmem80real_ST0
  simp only [haddr, hlock]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run_until [FP87.Is_Enabled => isEnabled_run hcr0,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes]
  spec_run_until [FP87.Read_STi => readSTi_run _ _ 0 rfl]
  refine (specM_bind_run _ _ (fst_operation _ _ ?_ ?_)).trans ?_
  · exact h0
  · exact hm
  simp only [↓reduceIte]
  spec_run_until []
  refine (specM_bind_run _ _ (hcheck _ ?_)).trans ?_
  · exact ht.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl
      rfl rfl ht.tables
  spec_run_until []
  refine (specM_bind_run _ _ (hwrite _ ?_ (by rfl) _)).trans ?_
  · exact ht.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl
      rfl rfl ht.tables
  spec_run_until []
  refine (specM_bind_run _ _ (hwrite8 _ ?_ _ (by rfl) _)).trans ?_
  · exact ht.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl
      rfl rfl (IdentityPageTableMemory.memStore ht.tables lin _ (by omega) (by omega))
  spec_run_until [FP87.Pop => pop_run _,
    FP87.Process_Exceptions => processExceptions_run _ _
      (by simp only [Operand.write, dataAccess]; exact hm),
    X86.UNSPECIFIED => unspecified1_run _]
  refine (updateInstructionInfo_run _ _ _ _ _ _ ?_ ?_ ?_).trans ?_
  · refine hmode.of_cs_lma_eq ?_ ?_
    · simp only [Operand.write, dataAccess]
    · simp only [Operand.write, dataAccess]
  · simp only [Operand.write, dataAccess]
    show fswES (x87CommitFsw (fswSetTop t.FP87_Status (fswTop t.FP87_Status + 1))
        (x87ReportFsw t.FP87_Status 0 0)
            (oracleSkip (oracleSkip (oracleSkip t.oracle 464) 464) 464)) = 0
    simpa using hes
  · refine hfdp' _ ?_
    simp only [Operand.write, dataAccess]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [Operand.write, dataAccess, add_zero3', Int.reduceToNat, memStore80,
    extractLsb'_hi_append_lo, x87Out]
  rfl

end X86Proofs
