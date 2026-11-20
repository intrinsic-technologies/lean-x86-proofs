import X86Proofs.Program.ReadWrite.X87
import X86Proofs.Instructions.Fst.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem fstp_st_form [Bindings] (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (opcode : BitVec 8)
    (hlock : ctx.lock_prefix_present = false)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0)
    (hes : fswES s.FP87_Status = 0)
    (hm : FcwMasked s.FP87_Control)
    (hfdp : Prelude.ReportsCPUFeature Bindings.processor s CPUID_FDP_EXCPTN_ONLY_Encoding true)
    (hmode : In64BitMode s)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3) :
    (X86.Instructions.FSTP_X87_ST0 ip ctx mod reg rm opcode).run s =
      (.ok (), x87Out s ip 3
        (fprSet s.FP87 (fswTop s.FP87_Status + rm) s.FP87[fprIndex (fswTop s.FP87_Status)])
        (ftwSet
            (ftwSet s.FP87_Tag_Word (fswTop s.FP87_Status + rm)
            (x87Tag s.FP87[fprIndex (fswTop s.FP87_Status)])) (fswTop s.FP87_Status) 3)
        (fswSetTop (fstStatus s.FP87_Status s.oracle) (fswTop s.FP87_Status + 1))) := by
  have hfdp' : ∀ t : RamState, SameControls s t →
      Prelude.ReportsCPUFeature Bindings.processor t CPUID_FDP_EXCPTN_ONLY_Encoding true :=
    fun _ h => reportsCPUFeature_of_sameControls h hfdp
  rw [← x87CommitFsw_fst s.FP87_Status s.oracle, ← x87CommitFsw_fswSetTop]
  unfold X86.Instructions.FSTP_X87_ST0
  simp only [hlock]
  spec_run_until [FP87.Is_Enabled => isEnabled_run hcr0,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
        FP87.Read_STi => readSTi_run _ _ 0 rfl]
  refine (specM_bind_run _ _ (fst_operation _ _ ?_ ?_)).trans ?_
  · exact h0
  · exact hm
  spec_run_until [X86.Helpers.ST_write => stWrite_run _ _ rm (unsigned_eq rm) _,
    FP87.Pop => pop_run _,
    FP87.Process_Exceptions => processExceptions_run _ _ (by exact hm),
    X86.UNSPECIFIED => unspecified1_run _]
  refine (updateInstructionInfo_run _ _ _ _ _ _ ?_ ?_ ?_).trans ?_
  · exact hmode.of_cs_lma_eq rfl rfl
  · show fswES
      (x87CommitFsw (fswSetTop s.FP87_Status (fswTop s.FP87_Status + 1))
      (x87ReportFsw s.FP87_Status 0 0) s.oracle) = 0
    simpa using hes
  · exact hfdp' _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [add_zero3']
  rfl

end X86Proofs
