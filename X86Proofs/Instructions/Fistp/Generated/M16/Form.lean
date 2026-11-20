import X86Proofs.Program.ReadWrite.X87Mem
import X86Proofs.Instructions.Fist.Operation
import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem fistp_m16_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
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
    (h0 : ftwTag t.FP87_Tag_Word (fswTop t.FP87_Status) ≠ 3)
    (hok : X87ToIntOk (fcwRC t.FP87_Control) 16 t.FP87[fprIndex (fswTop t.FP87_Status)])
    (hlow : lin.toNat + 2 ≤ 2^32)
    (hmem : ∀ i, i < 2 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.FISTP_MEMmem16int_ST0 ip ctx mod reg rm opcode).run s =
      (.ok (), x87Out
          ((Operand.mem lin : Operand 16).write
          (dataAccess { t with oracle := oracleSkip t.oracle 464 } "store")
          (x87ToInt (fcwRC t.FP87_Control) 16 t.FP87[fprIndex (fswTop t.FP87_Status)]).1) next 3
        (t.FP87)
        (ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status) 3)
        (fswSetTop
            (x87StoreStatus t.FP87_Status (oracleSkip (oracleSkip t.oracle 464) 464)
            (x87ToInt (fcwRC t.FP87_Control) 16 t.FP87[fprIndex (fswTop t.FP87_Status)]).2.1
            (fistFlags
            (x87ToInt (fcwRC t.FP87_Control) 16 t.FP87[fprIndex (fswTop t.FP87_Status)]).2.2))
            (fswTop t.FP87_Status + 1))) := by
  have hfdp' : ∀ u : RamState, SameControls t u →
      Prelude.ReportsCPUFeature Bindings.processor u CPUID_FDP_EXCPTN_ONLY_Encoding true :=
    fun _ h => reportsCPUFeature_of_sameControls h hfdp
  unfold X86.Instructions.FISTP_MEMmem16int_ST0
  simp only [haddr, hlock]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  have hcheck (u : RamState) (hu : DataReady u) :=
    checkLogicalAddressIsWritable_run_seg u hu seg addr lin hseg 16 (by decide) hlow
  have hwrite (u : RamState) (hu : DataReady u) (hext : u.external = t.external)
      (v : BitVec 16) :=
    logicalMemWrite_run_seg u hu seg addr lin hseg 16 (by decide) v hlow
      (by rw [hext]; exact hmem)
  rw
      [← x87CommitFsw_store t.FP87_Status (oracleSkip (oracleSkip t.oracle 464) 464), ←
      x87CommitFsw_fswSetTop]
  spec_run_until [FP87.Is_Enabled => isEnabled_run hcr0,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
    FP87.Read_STi => readSTi_run _ _ 0 rfl]
  refine (specM_bind_run _ _ (hcheck _ ?_)).trans ?_
  · exact ht.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl
      rfl rfl ht.tables
  refine (specM_bind_run _ _ (fist_operation _ _ _ (by decide) ?_ ?_ ?_)).trans ?_
  · exact h0
  · exact hm
  · simpa only [dataAccess_FP87_Control, dataAccess_FP87, add_zero3, add_zero3'] using hok
  simp only [↓reduceIte]
  refine (specM_bind_run _ _ (hwrite _ ?_ (by rfl) _)).trans ?_
  · exact ht.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl
      rfl rfl ht.tables
  spec_run_until [FP87.Pop => pop_run _,
  FP87.Process_Exceptions => processExceptions_run _ _ (by exact hm),
    X86.UNSPECIFIED => unspecified1_run _]
  refine (updateInstructionInfo_run _ _ _ _ _ _ ?_ ?_ ?_).trans ?_
  · exact hmode.of_cs_lma_eq rfl rfl
  · simp only [Operand.write, dataAccess, add_zero3']
    show fswES (x87CommitFsw (fswSetTop t.FP87_Status (fswTop t.FP87_Status + 1))
        (x87ReportFsw t.FP87_Status
            (if (x87ToInt (fcwRC t.FP87_Control) 16 t.FP87[fprIndex (fswTop t.FP87_Status)]).2.1 =
            true then 1 else 0)
            (fistFlags
            (x87ToInt (fcwRC t.FP87_Control) 16 t.FP87[fprIndex (fswTop t.FP87_Status)]).2.2))
        (oracleSkip (oracleSkip t.oracle 464) 464)) = 0
    simpa using hes
  · exact hfdp' _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [Operand.write, dataAccess, add_zero3']
  rfl

end X86Proofs
