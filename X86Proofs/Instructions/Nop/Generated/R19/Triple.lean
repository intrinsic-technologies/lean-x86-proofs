import X86Proofs.Instructions.Nop.Generated.R19.Step
import X86Proofs.Instructions.Nop.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem nop_19_r_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x0F, 0x19, modrm])
      (fun _ => nopEffect p 3) := by
  rintro s h hcode rfl
  exact ⟨_, nop_19_r_step s h modrm hmod hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_withNextIP h 3 _, nopEffect_holds h 3⟩

theorem nop_19_r_triple [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [0x0F, 0x19, modrm])
      (Effect.post fun _ => nopEffect p 3) :=
  Triple.of_effect (fun _ _ => nopEffect_avoids p 3 _)
    (nop_19_r_effect_step p modrm hmod)

end X86Proofs
