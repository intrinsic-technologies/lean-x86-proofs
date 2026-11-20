import X86Proofs.Instructions.Cpuid.Step
import X86Proofs.Program.Compose

/-!
# CPUID triple

`cpuid_triple p r`: `0F A2` at `p` writes the processor's answer `r` for leaf EAX and subleaf ECX
to RAX, RBX, RCX, RDX, each zero-extended (`cpuidEffect p r`). The answer is a parameter fixed by
the precondition (`CpuidPre p r`: `cpuidResult Bindings.processor s EAX ECX = .ok r`, the
processor's CPUID binding), which also asks for the processor not to be in VMX non-root operation
(a VM exit), CPUID faulting disabled (a #GP at CPL 3) and `IA32_MISC_ENABLE.LIMIT_CPUID_MAXVAL`
clear (which changes the leaf asked).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The precondition of `cpuid_triple`: RIP = `p`, not in VMX non-root operation, CPUID faulting
disabled, the leaf limit clear, and the processor's answer for leaf EAX and subleaf ECX is `r`. -/
structure CpuidPre [Bindings] (p : BitVec 64) (r : Cpuid.Registers) (s : RamState) : Prop where
  rip : s.RIP = p
  vmx : s.VMX_Operation_Mode ≠ VMX_Operation_Type.VMX_Non_Root
  fault : s.PLATFORM_INFO.CPUID_FAULTING_EN = 0
  limit : s.IA32_MISC_ENABLE.LIMIT_CPUID_MAXVAL = 0
  result : cpuidResult Bindings.processor s ((Operand.reg 0 : Operand 32).read s)
    ((Operand.reg 1 : Operand 32).read s) = .ok r

/-- The effect of CPUID at `p` with answer `r`: RAX, RBX, RCX, RDX get `r` (EAX, EBX, ECX, EDX
order), zero-extended, and RIP moves to `p + 2`. -/
def cpuidEffect (p : BitVec 64) (r : Cpuid.Registers) (_s : RamState) : Effect :=
  { rip := p + 2
    writes := [⟨(Operand.reg 0 : Operand 64), r.1.setWidth 64⟩,
      ⟨(Operand.reg 3 : Operand 64), r.2.1.setWidth 64⟩,
      ⟨(Operand.reg 1 : Operand 64), r.2.2.1.setWidth 64⟩,
      ⟨(Operand.reg 2 : Operand 64), r.2.2.2.setWidth 64⟩] }

@[simp] theorem cpuidEffect_components (p : BitVec 64) (r : Cpuid.Registers) (s : RamState) :
    (cpuidEffect p r s).components = [.reg 0, .reg 3, .reg 1, .reg 2, .rip] := rfl

/-- The step behind `cpuid_triple`. -/
theorem cpuid_effect_step [Bindings] (p : BitVec 64) (r : Cpuid.Registers) :
    StepEffect (CpuidPre p r) (codeRange p [0x0F, 0xA2]) (cpuidEffect p r) := by
  rintro s h hcode ⟨rfl, hvmx, hfault, hlimit, hr⟩
  refine ⟨_, cpuid_step s h [] (by simp) (by simp) rfl rfl hvmx hfault hlimit r hr
      hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_cpuid h _ _ _, ?_⟩
  exact ⟨afterStep_cpuid_rip h _ _ _, Operand.read_afterStep_cpuid s _ _ r, trivial,
    AgreesExcept.afterStep_cpuid s _ _ r⟩

/-- The triple for `cpuid` (`0F A2`) at `p` with answer `r`. -/
theorem cpuid_triple [Bindings] (p : BitVec 64) (r : Cpuid.Registers) :
    Triple (CpuidPre p r) (codeRange p [0x0F, 0xA2]) (Effect.post (cpuidEffect p r)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cpuidEffect_components]; simp [Component.Covers]) _) (cpuid_effect_step p r)

@[x86_local] theorem cpuidEffect_local {p : BitVec 64} {r : Cpuid.Registers} :
    Effect.Local (cpuidEffect p r) := by
  effect_local [cpuidEffect]

section Carry

variable {e : Effect} {s s' : RamState}

@[x86_pre] theorem CpuidPre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} {r : Cpuid.Registers} (hrip : e.rip = p)
    (hvmx : s.VMX_Operation_Mode ≠ VMX_Operation_Type.VMX_Non_Root)
    (hfault : s.PLATFORM_INFO.CPUID_FAULTING_EN = 0)
    (hlimit : s.IA32_MISC_ENABLE.LIMIT_CPUID_MAXVAL = 0)
    (hres : cpuidResult Bindings.processor s ((Operand.reg 0 : Operand 32).read (e.after s true))
      ((Operand.reg 1 : Operand 32).read (e.after s true)) = .ok r) : CpuidPre p r s' :=
  ⟨h.rip_of hrip, h.VMX_eq ▸ hvmx, h.PLATFORM_INFO_eq ▸ hfault, h.IA32_MISC_ENABLE_eq ▸ hlimit,
    by rw [Obs.back_reg ho, Obs.back_reg ho, h.cpuidResult_eq]; exact hres⟩

end Carry

end X86Proofs
