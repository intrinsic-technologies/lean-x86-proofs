import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Program.Agrees
import X86Proofs.Program.ReadWrite.Stack
import X86Proofs.Instructions.Nop.Step
import X86Proofs.Instructions.Fence.Decode

/-!
# Layer 3: LFENCE, MFENCE, SFENCE

What a step whose form ends in `fenceState` (a NOP plus a trace event) leaves:
`afterStep_fence_rip`, `ReadyToStep.afterStep_fence`, `AgreesExcept.afterStep_fence` (only RIP
changes; the trace is bookkeeping). The step theorems `lfence_step`, `mfence_step`, `sfence_step`
take any prefix list the scan covers without `66` and REP, a register ModRM byte with the fence's
`reg` digit, and the CPUID feature (SSE2, SSE) reported.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- After a fence step, RIP is `nextIP`. -/
theorem afterStep_fence_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (nextIP : BitVec 64) (msg : String) :
    (afterStep s length fun t => fenceState t nextIP msg).RIP = nextIP := by
  simp [afterStep, finishStep, fenceState, withNextIP, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- A fence step changes only RIP (besides the bookkeeping: the trace event). -/
theorem AgreesExcept.afterStep_fence (s : RamState) (length : Nat) (nextIP : BitVec 64)
    (msg : String) :
    AgreesExcept [.rip] s (afterStep s length fun t => fenceState t nextIP msg) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r => rfl
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
  · simp only [fixedPart, afterStep, finishStep, fenceState, withNextIP, afterFetches,
      beforeFetch, resetStepFields]

/-- Preservation for a fence step: the state after it is ready to step again. -/
theorem ReadyToStep.afterStep_fence [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (nextIP : BitVec 64) (msg : String) :
    ReadyToStep (afterStep s length fun t => fenceState t nextIP msg) :=
  h.of_agreesExcept (AgreesExcept.afterStep_fence s length nextIP msg) h.memory.tables

/-- Layer 3 for `LFENCE` (`0F AE /5`, `mod = 3`, any prefix list without `66` and REP): one
`step` only moves RIP (and records the fence). -/
theorem lfence_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hfeat : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5)
    (hcode : BytesAt s s.RIP (pre ++ [0x0F, 0xAE, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 3) ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3) fun t =>
      fenceState t (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3))) "lfence")) := by
  have hlen' : (pre ++ [0x0F, 0xAE, modrm]).length = pre.length + 3 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x0F, 0xAE, modrm]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy1_run_of_AE_lfence s h hfeat _ (pre.length + 1) modrm hmod hreg
    hcode hlow' (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) (by omega) _
    hrex2 hosz hrep
  rw [lfence_form _ _ _ hlock hosz hrep, show pre.length + 1 + 2 = pre.length + 3 by omega]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xAE [modrm] hpre ⟨by decide, by decide⟩ (by omega) hcode
    hlow' hdecode ((hmode (pre.length + 1 + 3)).of_cs_lma_eq rfl rfl)

/-- Layer 3 for `MFENCE` (`0F AE /6`, `mod = 3`, any prefix list without `66` and REP): one
`step` only moves RIP (and records the fence). -/
theorem mfence_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hfeat : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6)
    (hcode : BytesAt s s.RIP (pre ++ [0x0F, 0xAE, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 3) ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3) fun t =>
      fenceState t (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3))) "mfence")) := by
  have hlen' : (pre ++ [0x0F, 0xAE, modrm]).length = pre.length + 3 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x0F, 0xAE, modrm]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy1_run_of_AE_mfence s h hfeat _ (pre.length + 1) modrm hmod hreg
    hcode hlow' (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) (by omega) _
    hrex2 hosz hrep
  rw [mfence_form _ _ _ hlock hosz hrep, show pre.length + 1 + 2 = pre.length + 3 by omega]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xAE [modrm] hpre ⟨by decide, by decide⟩ (by omega) hcode
    hlow' hdecode ((hmode (pre.length + 1 + 3)).of_cs_lma_eq rfl rfl)

/-- Layer 3 for `SFENCE` (`0F AE /7`, `mod = 3`, any prefix list without `66` and REP): one
`step` only moves RIP (and records the fence). -/
theorem sfence_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hfeat : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE_Encoding true)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7)
    (hcode : BytesAt s s.RIP (pre ++ [0x0F, 0xAE, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 3) ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3) fun t =>
      fenceState t (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3))) "sfence")) := by
  have hlen' : (pre ++ [0x0F, 0xAE, modrm]).length = pre.length + 3 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x0F, 0xAE, modrm]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy1_run_of_AE_sfence s h hfeat _ (pre.length + 1) modrm hmod hreg
    hcode hlow' (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) (by omega) _
    hrex2 hosz
  rw [sfence_form _ _ _ hlock hosz hrep, show pre.length + 1 + 2 = pre.length + 3 by omega]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xAE [modrm] hpre ⟨by decide, by decide⟩ (by omega) hcode
    hlow' hdecode ((hmode (pre.length + 1 + 3)).of_cs_lma_eq rfl rfl)

end X86Proofs
