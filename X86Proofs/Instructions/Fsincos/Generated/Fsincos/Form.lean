import X86Proofs.Program.ReadWrite.X87
import X86Proofs.Instructions.Fsincos.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem fsincos_form [Bindings] (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (opcode : BitVec 8)
    (hlock : ctx.lock_prefix_present = false)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0)
    (hes : fswES s.FP87_Status = 0)
    (hm : FcwMasked s.FP87_Control)
    (hfdp : Prelude.ReportsCPUFeature Bindings.processor s CPUID_FDP_EXCPTN_ONLY_Encoding true)
    (hmode : In64BitMode s)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (hpush : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 7) = 3)
    (hok : X87BindOk (FP87.Sin_Cos s.FP87[fprIndex (fswTop s.FP87_Status)]) s.FP87_Control) :
    (X86.Instructions.FSINCOS ip ctx mod reg rm opcode).run s =
      some
          (.ok (), x87Out s ip
          (if
          (x87BindVal (FP87.Sin_Cos s.FP87[fprIndex (fswTop s.FP87_Status)]) s.FP87_Control).2.2.2.1
          = true then 3 else 2)
        (if
            (x87BindVal (FP87.Sin_Cos s.FP87[fprIndex (fswTop s.FP87_Status)])
            s.FP87_Control).2.2.2.1 then s.FP87 else fprSet
            (fprSet s.FP87 (fswTop s.FP87_Status)
            (x87BindVal (FP87.Sin_Cos s.FP87[fprIndex (fswTop s.FP87_Status)]) s.FP87_Control).2.1)
            (fswTop s.FP87_Status - 1)
            (x87BindVal (FP87.Sin_Cos s.FP87[fprIndex (fswTop s.FP87_Status)]) s.FP87_Control).1)
        (if
            (x87BindVal (FP87.Sin_Cos s.FP87[fprIndex (fswTop s.FP87_Status)])
            s.FP87_Control).2.2.2.1 then s.FP87_Tag_Word else ftwSet
            (ftwSet s.FP87_Tag_Word (fswTop s.FP87_Status)
            (x87Tag
            (x87BindVal (FP87.Sin_Cos s.FP87[fprIndex (fswTop s.FP87_Status)]) s.FP87_Control).2.1))
            (fswTop s.FP87_Status - 1)
            (x87Tag
            (x87BindVal (FP87.Sin_Cos s.FP87[fprIndex (fswTop s.FP87_Status)]) s.FP87_Control).1))
        (if
            (x87BindVal (FP87.Sin_Cos s.FP87[fprIndex (fswTop s.FP87_Status)])
            s.FP87_Control).2.2.2.1 then x87CosFsw s.FP87_Status s.oracle
            (x87BindVal (FP87.Sin_Cos s.FP87[fprIndex (fswTop s.FP87_Status)]) s.FP87_Control).2.2.1
            (x87BindVal (FP87.Sin_Cos s.FP87[fprIndex (fswTop s.FP87_Status)])
            s.FP87_Control).2.2.2.1
            (x87BindVal (FP87.Sin_Cos s.FP87[fprIndex (fswTop s.FP87_Status)])
            s.FP87_Control).2.2.2.2 else fswSetTop
            (x87CosFsw s.FP87_Status s.oracle
            (x87BindVal (FP87.Sin_Cos s.FP87[fprIndex (fswTop s.FP87_Status)]) s.FP87_Control).2.2.1
            (x87BindVal (FP87.Sin_Cos s.FP87[fprIndex (fswTop s.FP87_Status)])
            s.FP87_Control).2.2.2.1
            (x87BindVal (FP87.Sin_Cos s.FP87[fprIndex (fswTop s.FP87_Status)])
            s.FP87_Control).2.2.2.2) (fswTop s.FP87_Status - 1))) := by
  have hfdp' : ∀ t : RamState, SameControls s t →
      Prelude.ReportsCPUFeature Bindings.processor t CPUID_FDP_EXCPTN_ONLY_Encoding true :=
    fun _ h => reportsCPUFeature_of_sameControls h hfdp
  have h0' : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 0) ≠ 3 := by simpa using h0
  unfold X86.Instructions.FSINCOS
  simp only [hlock]
  pspec_run_until [FP87.Is_Enabled => isEnabled_run hcr0,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
    X86.Helpers.ST => st_run _ _ 0 rfl h0',
    X86.Instructions.Operations.FSINCOS => fsincos_operation _ _ (by exact h0) (by exact hpush)
      (by exact hm) (by simpa using hok)]
  simp only [add_zero3']
  cases (x87BindVal (FP87.Sin_Cos s.FP87[fprIndex (fswTop s.FP87_Status)]) s.FP87_Control).2.2.2.1
      <;>
  · pspec_run_until [FP87.Push => push_run _,
      X86.Helpers.ST_write => stWrite_run' _ _ (by decide) _,
      X86.Helpers.Null_Segment => partialSpecM_liftM_run_of_ok (nullSegment_eq _) _]
    refine (partialSpecM_liftTotal_run _ (updateInstructionInfo_run _ _ _ _ _ _ ?_ ?_ ?_)).trans ?_
    · exact hmode.of_cs_lma_eq rfl rfl
    · simpa using hes
    · exact hfdp' _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    simp only [add_zero3', fswTop_x87CosFsw, fswTop_fswSetTop, BitVec.sub_add_cancel,
      show BitVec.ofInt 3 1 = 1 from rfl, show BitVec.ofInt 3 0 = 0 from rfl]
    rfl

end X86Proofs
