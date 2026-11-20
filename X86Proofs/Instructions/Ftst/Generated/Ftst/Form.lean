import X86Proofs.Program.ReadWrite.X87
import X86Proofs.Instructions.Ftst.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem ftst_form [Bindings] (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (opcode : BitVec 8)
    (hlock : ctx.lock_prefix_present = false)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0)
    (hes : fswES s.FP87_Status = 0)
    (hm : FcwMasked s.FP87_Control)
    (hfdp : Prelude.ReportsCPUFeature Bindings.processor s CPUID_FDP_EXCPTN_ONLY_Encoding true)
    (hmode : In64BitMode s)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (hok : X87CompareOk true s.FP87[fprIndex (fswTop s.FP87_Status)] 0) :
    (X86.Instructions.FTST ip ctx mod reg rm opcode).run s =
      (.ok (), x87Out s ip 0
        (s.FP87)
        (s.FP87_Tag_Word)
        (x87CmpFsw s.FP87_Status (x87Compare true s.FP87[fprIndex (fswTop s.FP87_Status)] 0).1
            (x87Compare true s.FP87[fprIndex (fswTop s.FP87_Status)] 0).2)) := by
  have hfdp' : ∀ t : RamState, SameControls s t →
      Prelude.ReportsCPUFeature Bindings.processor t CPUID_FDP_EXCPTN_ONLY_Encoding true :=
    fun _ h => reportsCPUFeature_of_sameControls h hfdp
  have h0' : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 0) ≠ 3 := by simpa using h0
  unfold X86.Instructions.FTST
  simp only [hlock]
  spec_run_until [FP87.Is_Enabled => isEnabled_run hcr0,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
        X86.Helpers.ST => st_run _ _ 0 rfl h0']
  refine (specM_bind_run _ _ (ftst_operation _ _ ?_ ?_ ?_)).trans ?_
  · exact h0
  · exact hm
  · simpa using hok
  spec_run_until []
  refine (updateInstructionInfo_run _ _ _ _ _ _ ?_ ?_ ?_).trans ?_
  · exact hmode.of_cs_lma_eq rfl rfl
  · simpa using hes
  · exact hfdp' _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [add_zero3']
  rfl

end X86Proofs
