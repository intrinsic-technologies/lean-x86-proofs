import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Program.Agrees
import X86Proofs.Instructions.Nop.Decode

/-!
# Layer 3: NOP step theorems

One step theorem per encoding, each with result `afterStep s len fun t => withNextIP t (RIP + len)`:
- `nop_step`: `90` (no prefix).
- `nop_66_step`: `66 90` (`xchg ax, ax`; the operand-size prefix path, `step_66_legacy0`).
- `nop_r_step`: `0F 1F /0` with a register operand (the `0F` escape path, `step_none_legacy1`).

What a step whose form only sets `Next_IP` preserves (for any length): `afterStep_withNextIP_rip`,
`ReadyToStep.afterStep_withNextIP`, `AgreesExcept.afterStep_withNextIP` (only RIP changes).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- After a form that only sets `Next_IP := nextIP`, RIP is `nextIP`. -/
theorem afterStep_withNextIP_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (nextIP : BitVec 64) :
    (afterStep s length fun t => withNextIP t nextIP).RIP = nextIP := by
  simp [afterStep, finishStep, withNextIP, afterFetches, beforeFetch, resetStepFields,
    h.ready.repeatClear, h.ready.msr]

/-- Preservation: after a form that only sets `Next_IP`, the state is ready to step again. -/
theorem ReadyToStep.afterStep_withNextIP [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t => withNextIP t nextIP) := by
  have hst : SameControls s (afterStep s length fun t => withNextIP t nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass, hc.debug,
      hc.aet⟩,
    ⟨h.memory.cr3, h.memory.tables⟩,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, hr.tf, hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-- A step whose form only sets `Next_IP` changes only RIP (besides the per-step bookkeeping). -/
theorem AgreesExcept.afterStep_withNextIP (s : RamState) (length : Nat) (nextIP : BitVec 64) :
    AgreesExcept [.rip] s (afterStep s length fun t => withNextIP t nextIP) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r => rfl
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem addr len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => rfl
  · simp only [fixedPart, afterStep, finishStep, withNextIP, afterFetches, beforeFetch, resetStepFields]

/-- Layer 3 for `nop` (`90`): one `step` only moves RIP to RIP + 1. -/
theorem nop_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x90]) (hlow : s.RIP.toNat + 1 ≤ 2^32) :
    X86.Machine.step s =
      some (.next (afterStep s 1 fun t => withNextIP t (BitVec.add s.RIP 1#64))) := by
  have hdecode := decodeLegacy0_run_of_90 s h hcode hlow
  rw [nop_form _ _ _ rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x90 [] (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    hcode hlow hdecode (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)

/-- Layer 3 for `66 90` (`xchg ax, ax`): one `step` only moves RIP to RIP + 2. -/
theorem nop_66_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x66, 0x90]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    X86.Machine.step s =
      some (.next (afterStep s 2 fun t => withNextIP t (BitVec.add s.RIP 2#64))) := by
  have hdecode := decodeLegacy0_run_of_66_90 s h hcode hlow
  rw [nop_form _ _ _ rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_66_legacy0 s _ h 0x90 [] (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    hcode hlow hdecode (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)

/-- Layer 3 for `nop r/m32` with a register operand (`0F 1F /0`, `mod = 3`): one `step` only
moves RIP to RIP + 3. -/
theorem nop_r_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hcode : BytesAt s s.RIP [0x0F, 0x1F, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    X86.Machine.step s =
      some (.next (afterStep s 3 fun t => withNextIP t (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy1_run_of_0F_1F_register s h modrm hmod hreg hcode hlow
  rw [nop_r_form _ _ _ rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy1 s _ h 0x1F [modrm] (by decide) hcode hlow hdecode
    (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)

end X86Proofs
