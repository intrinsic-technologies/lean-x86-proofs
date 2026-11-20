import X86Proofs.Program.ReadWrite.X87
import X86Proofs.Instructions.Fsqrt.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem fsqrt_form [Bindings] (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (opcode : BitVec 8)
    (hlock : ctx.lock_prefix_present = false)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0)
    (hes : fswES s.FP87_Status = 0)
    (hm : FcwMasked s.FP87_Control)
    (hfdp : Prelude.ReportsCPUFeature Bindings.processor s CPUID_FDP_EXCPTN_ONLY_Encoding true)
    (hmode : In64BitMode s)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (hok : X87SqrtOk s.FP87_Control s.FP87[fprIndex (fswTop s.FP87_Status)]) :
    (X86.Instructions.FSQRT ip ctx mod reg rm opcode).run s =
      (.ok (), x87Out s ip 6
        (fprSet s.FP87 (fswTop s.FP87_Status)
            (x87Sqrt s.FP87_Control s.FP87[fprIndex (fswTop s.FP87_Status)]).1)
        (ftwSet s.FP87_Tag_Word (fswTop s.FP87_Status)
            (x87Tag (x87Sqrt s.FP87_Control s.FP87[fprIndex (fswTop s.FP87_Status)]).1))
        (x87ArithFsw (s.FP87_Status) s.FP87_Status s.oracle
            (x87Sqrt s.FP87_Control s.FP87[fprIndex (fswTop s.FP87_Status)]).2.1
            (x87Sqrt s.FP87_Control s.FP87[fprIndex (fswTop s.FP87_Status)]).2.2)) := by
  have hfdp' : ∀ t : RamState, SameControls s t →
      Prelude.ReportsCPUFeature Bindings.processor t CPUID_FDP_EXCPTN_ONLY_Encoding true :=
    fun _ h => reportsCPUFeature_of_sameControls h hfdp
  have h0' : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 0) ≠ 3 := by simpa using h0
  unfold X86.Instructions.FSQRT
  simp only [hlock]
  spec_run_until [FP87.Is_Enabled => isEnabled_run hcr0,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
        FP87.Read_STi => readSTi_run _ _ 0 rfl]
  refine (specM_bind_run _ _ (fsqrt_operation _ _ ?_ ?_ ?_)).trans ?_
  · exact h0
  · exact hm
  · simpa using hok
  spec_run_until [FP87.Is_Unmasked_Pre_Computation_Exception =>
      isUnmaskedPre_masked _ _ (by exact hm),
    X86.Helpers.ST_write => stWrite_run _ _ 0 rfl _,
    FP87.Process_Exceptions => processExceptions_run _ _ (by exact hm),
    X86.UNSPECIFIED => unspecified1_run _]
  refine (updateInstructionInfo_run _ _ _ _ _ _ ?_ ?_ ?_).trans ?_
  · exact hmode.of_cs_lma_eq rfl rfl
  · show fswES (x87ArithFsw (s.FP87_Status) s.FP87_Status s.oracle _ _) = 0
    simpa using hes
  · exact hfdp' _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [add_zero3']
  rfl

end X86Proofs
