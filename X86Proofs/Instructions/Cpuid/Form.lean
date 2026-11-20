import X86Proofs.Instructions.Cpuid.Operation

/-!
# Layer 2: CPUID

`CPUID` (`0F A2`) checks for a LOCK prefix and for VMX non-root operation (a VM exit), sets
`Next_IP` and runs `Operations.CPUID` (`cpuid_operation`): RAX, RBX, RCX, RDX get the processor's
answer for leaf EAX and subleaf ECX, zero-extended.
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers

/-- Layer 2 for `CPUID`: without a LOCK prefix, outside VMX non-root operation, with CPUID
faulting disabled and the leaf limit clear, and with the processor answering `r` for leaf EAX and
subleaf ECX, it succeeds, sets `Next_IP` and writes `r` to RAX, RBX, RCX, RDX. -/
theorem cpuid_form [Bindings] (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false)
    (hvmx : s.VMX_Operation_Mode ≠ VMX_Operation_Type.VMX_Non_Root)
    (hfault : s.PLATFORM_INFO.CPUID_FAULTING_EN = 0)
    (hlimit : s.IA32_MISC_ENABLE.LIMIT_CPUID_MAXVAL = 0) (r : Cpuid.Registers)
    (hr : cpuidResult Bindings.processor s ((Operand.reg 0 : Operand 32).read s)
      ((Operand.reg 1 : Operand 32).read s) = .ok r) :
    (X86.Instructions.CPUID ip ctx).run s = (.ok (), cpuidState (withNextIP s ip) r) := by
  unfold X86.Instructions.CPUID
  simp only [hlock, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run _ _ (s := s) (t := s) (value := s) rfl).trans ?_
  have hb : (s.VMX_Operation_Mode == VMX_Operation_Type.VMX_Non_Root) = false :=
    beq_eq_false_iff_ne.mpr hvmx
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run _ _ (s := s) (t := withNextIP s ip) (value := ()) rfl).trans ?_
  exact cpuid_operation (withNextIP s ip) hfault hlimit r hr

end X86Proofs
