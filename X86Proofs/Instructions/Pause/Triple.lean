import X86Proofs.Instructions.Pause.Step
import X86Proofs.Instructions.Nop.Triple
import X86Proofs.Program.Compose

/-!
# PAUSE triple

`pause_triple p`: `F3 90` at `p`, outside VMX non-root operation (`PausePre`: lean-x86 does not
model the PAUSE-exiting VM-execution controls, `Unimplemented_Feature`), has the effect of a NOP of
2 bytes (`nopEffect p 2`: only RIP moves).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The precondition of `pause_triple`: RIP = `p`, and the processor is not in VMX non-root
operation. -/
structure PausePre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  vmx : s.VMX_Operation_Mode ≠ X86.Helpers.VMX_Operation_Type.VMX_Non_Root

/-- The step behind `pause_triple`: only RIP moves, to `p + 2`. -/
theorem pause_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (PausePre p) (codeRange p [0xF3, 0x90]) (fun _ => nopEffect p 2) := by
  rintro s h hcode ⟨rfl, hvmx⟩
  exact ⟨_, pause_step s h [0xF3] (by simpa using scanPrefix_f3) (by simp) rfl rfl rfl hvmx
      hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_withNextIP h 2 _, nopEffect_holds h 2⟩

/-- The triple for `pause` (`F3 90`) at `p`: only RIP moves, to `p + 2`. -/
theorem pause_triple [Bindings] (p : BitVec 64) :
    Triple (PausePre p) (codeRange p [0xF3, 0x90]) (Effect.post fun _ => nopEffect p 2) :=
  Triple.of_effect (fun _ _ => nopEffect_avoids p 2 _) (pause_effect_step p)

section Carry

variable {e : Effect} {s s' : RamState}

@[x86_pre] theorem PausePre.of_holds (h : e.Holds s s') {p : BitVec 64} (hrip : e.rip = p)
    (hvmx : s.VMX_Operation_Mode ≠ X86.Helpers.VMX_Operation_Type.VMX_Non_Root) :
    PausePre p s' :=
  ⟨h.rip_of hrip, h.VMX_eq ▸ hvmx⟩

end Carry

end X86Proofs
