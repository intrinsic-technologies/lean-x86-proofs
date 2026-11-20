import X86Proofs.Program.ReadWrite.X87
import X86Proofs.Instructions.Fld1.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem fld1_form [Bindings] (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (opcode : BitVec 8)
    (hlock : ctx.lock_prefix_present = false)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0)
    (hes : fswES s.FP87_Status = 0)
    (hm : FcwMasked s.FP87_Control)
    (hfdp : Prelude.ReportsCPUFeature Bindings.processor s CPUID_FDP_EXCPTN_ONLY_Encoding true)
    (hmode : In64BitMode s)
    (hpush : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 7) = 3) :
    (X86.Instructions.FLD1 ip ctx mod reg rm opcode).run s =
      (.ok (), x87Out s ip 3
        (fprSet s.FP87 (fswTop s.FP87_Status - 1) (x87Const 0 (fcwRC s.FP87_Control)))
        (ftwSet s.FP87_Tag_Word (fswTop s.FP87_Status - 1)
            (x87Tag (x87Const 0 (fcwRC s.FP87_Control))))
        (fswSetTop (fldStatus s.FP87_Status s.oracle) (fswTop s.FP87_Status - 1))) := by
  have hfdp' : ∀ t : RamState, SameControls s t →
      Prelude.ReportsCPUFeature Bindings.processor t CPUID_FDP_EXCPTN_ONLY_Encoding true :=
    fun _ h => reportsCPUFeature_of_sameControls h hfdp
  unfold X86.Instructions.FLD1
  simp only [hlock]
  spec_run_until [liftM => liftM_run_of_ok (fp87One_eq (fcwRC s.FP87_Control)) _,
    FP87.Is_Enabled => isEnabled_run hcr0,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes]
  refine (specM_bind_run _ _ (fldConstant_operation _ _ ?_ ?_)).trans ?_
  · exact hpush
  · exact hm
  spec_run_until [FP87.Push => push_run _,
    X86.Helpers.ST_write => stWrite_run _ _ 0 rfl _]
  refine (updateInstructionInfo_run _ _ _ _ _ _ ?_ ?_ ?_).trans ?_
  · exact hmode.of_cs_lma_eq rfl rfl
  · simpa using hes
  · exact hfdp' _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [fswTop_fswSetTop, fswTop_fldStatus, add_zero3']
  rfl

end X86Proofs
