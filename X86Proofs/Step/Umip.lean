import X86Proofs.Step.Prefix
import X86Proofs.Step.Address

/-!
# Reading system registers at CPL 3 (`CR4.UMIP`)

SGDT, SIDT, SLDT, SMSW and STR store a descriptor-table register, a selector or the low bits of CR0.
At CPL > 0 lean-x86 raises #GP for them when CR4.UMIP (bit 11, user-mode instruction prevention) is
set, and in VMX non-root operation it may take a VM exit (descriptor-table exiting) or, for SMSW,
read the CR0 read shadow. `SysRegReadable s` rules both out: UMIP clear and not in VMX non-root
operation; it is a precondition of those triples (UMIP is not fixed by `ReadyToStep`). `cr4UMIP_run`
is lean-x86's `CR4.UMIP` read and `checkSTR_run` STR's checks (`Check_STR`); this file is the one
that looks inside them (architecture rule 5).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- SGDT, SIDT, SLDT, SMSW and STR can read their register at CPL 3: CR4.UMIP is clear and the
processor is not in VMX non-root operation. -/
structure SysRegReadable (s : RamState) : Prop where
  umip : s.CR4.extractLsb' 11 1 = 0
  vmx : s.VMX_Operation_Mode ≠ VMX_Operation_Type.VMX_Non_Root

/-- `CR4.UMIP` returns bit 11 of CR4. -/
theorem cr4UMIP_run {σ : Type} (s : X86.State σ) :
    (CR4.UMIP : X86.Runtime.SpecM X86.Exception (X86.State σ) X86.Runtime.Bit).run s =
      (.ok (s.CR4.extractLsb' 11 1), s) := by
  simp [CR4.UMIP, x86_runtime, bind, pure, get, getThe, MonadStateOf.get, ExceptT.run,
    ExceptT.bind, ExceptT.mk, ExceptT.pure, ExceptT.lift, StateT.bind, liftM,
    monadLift, MonadLift.monadLift]
  rfl

/-- The steps keep `SysRegReadable` facts: they read only CR4 and the VMX mode. -/
theorem SysRegReadable.of_eq {s t : RamState} (h : SysRegReadable s) (hcr4 : t.CR4 = s.CR4)
    (hvmx : t.VMX_Operation_Mode = s.VMX_Operation_Mode) : SysRegReadable t :=
  ⟨hcr4 ▸ h.umip, hvmx ▸ h.vmx⟩

/-- STR's checks (`Check_STR`: LOCK, real and virtual-8086 mode, VMX descriptor-table exiting, UMIP)
pass in IA-32e mode without a LOCK prefix when the task register is readable. -/
theorem checkSTR_run (s : RamState) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false) (hcr0 : Prelude.SupportedIntegerCR0 s.CR0)
    (hlma : s.IA32_EFER.LMA = 1) (h : SysRegReadable s) :
    (Check_STR (σ := Ram) ctx).run s = (.ok (), s) := by
  have hb : (s.VMX_Operation_Mode == VMX_Operation_Type.VMX_Non_Root) = false := by
    simpa using h.vmx
  have hu : (s.CR4.extractLsb' 11 1 == 1) = false := by rw [h.umip]; rfl
  unfold Check_STR
  simp only [hlock, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run _ _ (s := s) (t := s) (value := false) ?_).trans ?_
  · rw [specM_bind_run _ _ (currentMode_run s hcr0 hlma)]
    rfl
  simp only [Bool.false_eq_true, ↓reduceIte]
  spec_run [MonadState.get => get_run _, CR4.UMIP => cr4UMIP_run _]
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (cr4UMIP_run s), specM_bind_run _ _ (get_run s)]
  simp only [hu, HAnd.hAnd, AndOp.and, strictAnd, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

end X86Proofs
