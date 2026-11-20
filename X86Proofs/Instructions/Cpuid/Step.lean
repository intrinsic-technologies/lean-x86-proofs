import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Program.Agrees
import X86Proofs.Program.ReadWrite.Stack
import X86Proofs.Program.ReadWrite.WritePair
import X86Proofs.Instructions.Cpuid.Decode

/-!
# Layer 3: CPUID

What a step whose form ends in `cpuidState` leaves: `afterStep_cpuid_rip`,
`ReadyToStep.afterStep_cpuid`, `AgreesExcept.afterStep_cpuid` (only RAX, RBX, RCX, RDX and RIP
change) and `Operand.read_afterStep_cpuid` (each of the four registers is its answer,
zero-extended). The step theorem `cpuid_step` takes any prefix list the scan covers without LOCK,
and the processor's answer `r` for leaf EAX and subleaf ECX in the state before the step.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- After a CPUID step, RIP is `nextIP`. -/
theorem afterStep_cpuid_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (nextIP : BitVec 64) (r : Cpuid.Registers) :
    (afterStep s length fun t => cpuidState (withNextIP t nextIP) r).RIP = nextIP := by
  simp [afterStep, finishStep, cpuidState, withNextIP, Operand.write, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- After `cpuidState`, a register other than RAX, RBX, RCX, RDX reads as before. -/
theorem Operand.read_cpuidState_of_ne (t : RamState) (r : Cpuid.Registers) {g : BitVec 5}
    (hg : g ∉ [0, 3, 1, 2]) :
    (Operand.reg g : Operand 64).read (cpuidState t r) = (Operand.reg g : Operand 64).read t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hg
  obtain ⟨h0, h3, h1, h2⟩ := hg
  have ne (i : BitVec 5) (hi : i ≠ g) : (gprIndex i).val ≠ (gprIndex g).val :=
    Fin.val_ne_of_ne (gprIndex_ne hi)
  simp only [cpuidState, Operand.write_reg_eq_set, Operand.read_reg64, Fin.getElem_fin,
    Vector.getElem_set_ne _ _ (ne 0 (Ne.symm h0)), Vector.getElem_set_ne _ _ (ne 3 (Ne.symm h3)),
    Vector.getElem_set_ne _ _ (ne 1 (Ne.symm h1)), Vector.getElem_set_ne _ _ (ne 2 (Ne.symm h2))]

/-- After a CPUID step, RAX, RBX, RCX and RDX are the four answers, zero-extended. -/
theorem Operand.read_afterStep_cpuid (s : RamState) (length : Nat) (nextIP : BitVec 64)
    (r : Cpuid.Registers) :
    let t := afterStep s length fun t => cpuidState (withNextIP t nextIP) r
    (Operand.reg 0 : Operand 64).read t = r.1.setWidth 64 ∧
      (Operand.reg 3 : Operand 64).read t = r.2.1.setWidth 64 ∧
      (Operand.reg 1 : Operand 64).read t = r.2.2.1.setWidth 64 ∧
      (Operand.reg 2 : Operand 64).read t = r.2.2.2.setWidth 64 := by
  simp only [Operand.read_afterStep]
  simp only [cpuidState, Operand.write_reg_eq_set, Operand.read_reg64, mergeGPR_32,
    Fin.getElem_fin]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Vector.getElem_set_ne _ _ (by decide), Vector.getElem_set_ne _ _ (by decide),
      Vector.getElem_set_ne _ _ (by decide), Vector.getElem_set_self]
  · rw [Vector.getElem_set_ne _ _ (by decide), Vector.getElem_set_ne _ _ (by decide),
      Vector.getElem_set_self]
  · rw [Vector.getElem_set_ne _ _ (by decide), Vector.getElem_set_self]
  · rw [Vector.getElem_set_self]

/-- A CPUID step changes only RAX, RBX, RCX, RDX and RIP (besides the per-step bookkeeping). -/
theorem AgreesExcept.afterStep_cpuid (s : RamState) (length : Nat) (nextIP : BitVec 64)
    (r : Cpuid.Registers) :
    AgreesExcept [.reg 0, .reg 3, .reg 1, .reg 2, .rip] s
      (afterStep s length fun t => cpuidState (withNextIP t nextIP) r) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg g =>
      have hg : g ∉ [0, 3, 1, 2] := fun h => hc (by simp_all)
      have := (Operand.read_afterStep s length
        (fun t => cpuidState (withNextIP t nextIP) r) (.reg g : Operand 64)).trans
        (Operand.read_cpuidState_of_ne _ r hg)
      simp only [Operand.read_reg64] at this
      exact this
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem a len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => rfl
  · simp only [fixedPart, afterStep, finishStep, cpuidState, withNextIP, Operand.write,
      afterFetches, beforeFetch, resetStepFields]

/-- Preservation for a CPUID step: the state after it is ready to step again. -/
theorem ReadyToStep.afterStep_cpuid [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (nextIP : BitVec 64) (r : Cpuid.Registers) :
    ReadyToStep (afterStep s length fun t => cpuidState (withNextIP t nextIP) r) :=
  h.of_agreesExcept (AgreesExcept.afterStep_cpuid s length nextIP r) h.memory.tables

/-- Layer 3 for `CPUID` (`0F A2`, any prefix list without LOCK): outside VMX non-root operation,
with CPUID faulting disabled, the leaf limit clear and the processor answering `r` for leaf EAX
and subleaf ECX, one `step` writes `r` to RAX, RBX, RCX, RDX (zero-extended) and moves RIP. -/
theorem cpuid_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hvmx : s.VMX_Operation_Mode ≠ VMX_Operation_Type.VMX_Non_Root)
    (hfault : s.PLATFORM_INFO.CPUID_FAULTING_EN = 0)
    (hlimit : s.IA32_MISC_ENABLE.LIMIT_CPUID_MAXVAL = 0) (r : Cpuid.Registers)
    (hr : cpuidResult Bindings.processor s ((Operand.reg 0 : Operand 32).read s)
      ((Operand.reg 1 : Operand 32).read s) = .ok r)
    (hcode : BytesAt s s.RIP (pre ++ [0x0F, 0xA2]))
    (hlow : s.RIP.toNat + (pre.length + 2) ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2) fun t =>
      cpuidState (withNextIP t (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2)))) r)) := by
  have hlen' : (pre ++ [0x0F, 0xA2]).length = pre.length + 2 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x0F, 0xA2]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy1_run_of_cpuid s h _ hrex2 _ (pre.length + 1) (by omega)
    (by simp) hcode hlow'
  have hr' : cpuidResult Bindings.processor (afterFetches (beforeFetch s) (pre.length + 1 + 2))
      ((Operand.reg 0 : Operand 32).read (afterFetches (beforeFetch s) (pre.length + 1 + 2)))
      ((Operand.reg 1 : Operand 32).read (afterFetches (beforeFetch s) (pre.length + 1 + 2))) =
        .ok r := by
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact hr
  rw [cpuid_form (afterFetches (beforeFetch s) (pre.length + 1 + 2)) _ _ hlock hvmx hfault hlimit r
      hr',
    show pre.length + 1 + 1 = pre.length + 2 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xA2 [] hpre ⟨by decide, by decide⟩ (by omega) hcode hlow'
    hdecode ((hmode (pre.length + 3)).of_cs_lma_eq rfl rfl)

end X86Proofs
