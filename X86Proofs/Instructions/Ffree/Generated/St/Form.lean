import X86Proofs.Program.ReadWrite.X87
import X86Proofs.Instructions.Ffree.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem ffree_st_form [Bindings] (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (opcode : BitVec 8)
    (hlock : ctx.lock_prefix_present = false)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0)
    (hes : fswES s.FP87_Status = 0)
    (hfdp : Prelude.ReportsCPUFeature Bindings.processor s CPUID_FDP_EXCPTN_ONLY_Encoding true)
    (hmode : In64BitMode s) :
    (X86.Instructions.FFREE_X87 ip ctx mod reg rm opcode).run s =
      (.ok (), x87Out s ip 3
        (s.FP87)
        (ftwSet s.FP87_Tag_Word (fswTop s.FP87_Status + rm) 3)
        (fswC1Zero s.FP87_Status s.oracle)) := by
  have hfdp' : ∀ t : RamState, SameControls s t →
      Prelude.ReportsCPUFeature Bindings.processor t CPUID_FDP_EXCPTN_ONLY_Encoding true :=
    fun _ h => reportsCPUFeature_of_sameControls h hfdp
  unfold X86.Instructions.FFREE_X87
  simp only [hlock]
  spec_run_until [FP87.Is_Enabled => isEnabled_run hcr0,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
    X86.Instructions.Operations.FFREE => ffree_operation _ _]
  refine (updateInstructionInfo_run _ _ _ _ _ _ ?_ ?_ ?_).trans ?_
  · exact hmode.of_cs_lma_eq rfl rfl
  · simpa using hes
  · exact hfdp' _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rfl

end X86Proofs
