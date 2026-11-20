import X86Proofs.Step.Paging
import X86Proofs.Core.Operand

/-!
# Layer 2: ENDBR64

`F3 0F 1E FA` is `ENDBR64` if CPUID reports CET_SS and a reserved NOP (`NOP_GPRv_GPRv_0F1E`)
otherwise (`Step/Decode/Legacy1Opcode1E.lean`). Both check for a LOCK prefix and set `Next_IP`;
`ENDBR64` then clears the CET end-branch tracker only if end-branch tracking is enabled
(`Is_End_Branch_Enabled`), which it is not with `CR4.CET` clear (`isEndBranchEnabled_run`, from
`Prelude.SupportedIntegerCR4`). So either form only sets `Next_IP`.
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers

/-- With `CR4.CET` clear, CET end-branch tracking is off. -/
theorem isEndBranchEnabled_run {σ : Type} (s : X86.State σ) (hcpl : 0 ≤ s.CPL ∧ s.CPL ≤ 3)
    (hcr4 : Prelude.SupportedIntegerCR4 s.CR4) :
    (Is_End_Branch_Enabled s.CPL).run s = (.ok false, s) := by
  simp [Is_End_Branch_Enabled, cr4CET_eq, cr0PE_eq, rflagsVM_eq,
    x86_runtime, hcpl, HAnd.hAnd, AndOp.and, strictAnd, supportedIntegerCR4_extractLsb_cet hcr4,
    bind, pure, get, getThe, ExceptT.bind, ExceptT.pure, ExceptT.run, ExceptT.mk, ExceptT.bindCont,
    StateT.bind, StateT.pure, MonadStateOf.get, StateT.get, Functor.map, StateT.map, Bind.bind,
    Pure.pure, ExceptT.lift, liftM, monadLift, MonadLift.monadLift]

/-- Layer 2 for `ENDBR64`: with CPUID reporting CET_SS, without a LOCK prefix and with `CR4.CET`
clear, it succeeds and only sets `Next_IP`. -/
theorem endbr64_form [Bindings] (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false)
    (hcet : Prelude.ReportsCPUFeature Bindings.processor s CPUID_CET_SS_Encoding true)
    (hcpl : 0 ≤ s.CPL ∧ s.CPL ≤ 3) (hcr4 : Prelude.SupportedIntegerCR4 s.CR4) :
    (X86.Instructions.ENDBR64 ip ctx).run s = (.ok (), withNextIP s ip) := by
  unfold X86.Instructions.ENDBR64 X86.Instructions.Operations.ENDBR64
  refine (specM_bind_run _ _ (s := s) (t := s) (value := true) ?_).trans ?_
  · exact cpuidCETSS_run hcet
  simp only [hlock, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run _ _ (s := s) (t := withNextIP s ip) (value := ()) rfl).trans ?_
  refine (specM_bind_run _ _ (s := withNextIP s ip) (t := withNextIP s ip) (value := false)
    ?_).trans rfl
  exact (specM_bind_run _ _ (s := withNextIP s ip) rfl).trans
    (isEndBranchEnabled_run (withNextIP s ip) hcpl hcr4)

/-- Layer 2 for `NOP_GPRv_GPRv_0F1E` (the reserved NOPs of `0F 1E`): without a LOCK prefix it
succeeds and only sets `Next_IP`. -/
theorem nop_0F1E_form {σ : Type} (s : X86.State σ) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.NOP_GPRv_GPRv_0F1E ip ctx).run s = (.ok (), withNextIP s ip) := by
  simp [X86.Instructions.NOP_GPRv_GPRv_0F1E, hlock]
  rfl

end X86Proofs
