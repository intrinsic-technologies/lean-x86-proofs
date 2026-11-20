import X86Proofs.Instructions.Endbr64.Step
import X86Proofs.Instructions.Nop.Triple

/-!
# ENDBR64 triple

`endbr64_triple p`: `F3 0F 1E FA` at `p` has the effect of a NOP of 4 bytes (`nopEffect p 4`:
only RIP moves), whether CPUID reports CET_SS or not: end-branch tracking needs `CR4.CET`, which a
ready state has clear. The precondition is RIP = `p` alone.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The step behind `endbr64_triple`: only RIP moves, to `p + 4`. -/
theorem endbr64_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xF3, 0x0F, 0x1E, 0xFA])
      (fun _ => nopEffect p 4) := by
  rintro s h hcode rfl
  exact ⟨_, endbr64_step s h [0xF3] (by simpa using scanPrefix_f3) (by simp) rfl rfl rfl
      hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_withNextIP h 4 _, nopEffect_holds h 4⟩

/-- The triple for `endbr64` (`F3 0F 1E FA`) at `p`: only RIP moves, to `p + 4`. -/
theorem endbr64_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => s.RIP = p) (codeRange p [0xF3, 0x0F, 0x1E, 0xFA])
      (Effect.post fun _ => nopEffect p 4) :=
  Triple.of_effect (fun _ _ => nopEffect_avoids p 4 _) (endbr64_effect_step p)

end X86Proofs
