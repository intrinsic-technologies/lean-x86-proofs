import X86Proofs.Core.Run
import X86Proofs.Core.Operand

/-!
# Layer 2: PAUSE

`PAUSE` (`F3 90`) checks for a LOCK prefix and for VMX non-root operation (where lean-x86 does not
model the PAUSE-exiting controls: `Unimplemented_Feature`), sets `Next_IP` and does nothing else
(`Operations.PAUSE` is `pure ()`: the SDM allows no delay and no architectural change).
-/

namespace X86Proofs

open X86 X86.Helpers

/-- Layer 2 for `PAUSE`: without a LOCK prefix and outside VMX non-root operation it succeeds and
only sets `Next_IP`. -/
theorem pause_form {σ : Type} [X86.Helpers.Unimplemented_Feature.Binding σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (hlock : ctx.lock_prefix_present = false)
    (hvmx : s.VMX_Operation_Mode ≠ VMX_Operation_Type.VMX_Non_Root) :
    (X86.Instructions.PAUSE ip ctx).run s = (.ok (), withNextIP s ip) := by
  unfold X86.Instructions.PAUSE
  simp only [hlock, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run _ _ (s := s) (t := s) (value := s) rfl).trans ?_
  have hb : (s.VMX_Operation_Mode == VMX_Operation_Type.VMX_Non_Root) = false :=
    beq_eq_false_iff_ne.mpr hvmx
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  rfl

end X86Proofs
