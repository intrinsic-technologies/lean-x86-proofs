import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Instructions.Nop.Step
import X86Proofs.Instructions.Endbr64.Decode

/-!
# Layer 3: ENDBR64

`endbr64_step`: for any prefix list the scan covers with `F3` (`rep_prefix = 243`) and without
LOCK, one `step` only moves RIP past `F3 0F 1E FA`, whether CPUID reports CET_SS (`ENDBR64`, with
end-branch tracking off: `CR4.CET` is clear in a ready state) or not (a reserved NOP). The step
facts are `withNextIP`'s (`Instructions/Nop/Step.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- Layer 3 for `ENDBR64` (`F3 0F 1E FA`, any prefix list with `F3`): one `step` only moves RIP. -/
theorem endbr64_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 12)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0x0F, 0x1E, 0xFA]))
    (hlow : s.RIP.toNat + (pre.length + 3) ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3) fun t =>
      withNextIP t (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3))))) := by
  have hlen' : (pre ++ [0x0F, 0x1E, 0xFA]).length = pre.length + 3 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x0F, 0x1E, 0xFA]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  obtain ⟨cet, hc⟩ := h.features.cetSS
  have hdecode := decodeLegacy1_run_of_endbr64 s h cet hc _ (pre.length + 1) hcode hlow'
    (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) (by omega) _ hrex2 hrep
  have hform : (if cet then
      X86.Instructions.ENDBR64 (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1 + 2)))
        (scanContext s.DS (PrefixSegments.ofState s) pre)
    else X86.Instructions.NOP_GPRv_GPRv_0F1E
      (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1 + 2)))
        (scanContext s.DS (PrefixSegments.ofState s) pre)).run
      (afterFetches (beforeFetch s) (pre.length + 1 + 3)) =
      (.ok (), withNextIP (afterFetches (beforeFetch s) (pre.length + 1 + 3))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1 + 2)))) := by
    cases cet
    · exact nop_0F1E_form _ _ _ hlock
    · exact endbr64_form _ _ _ hlock
        (reportsCPUFeature_of_sameControls (s := s)
          (t := afterFetches (beforeFetch s) (pre.length + 1 + 3))
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hc) h.cpu.cpl h.cpu.cr4
  rw [hform, show pre.length + 1 + 2 = pre.length + 3 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0x1E [0xFA] hpre ⟨by decide, by decide⟩ (by omega) hcode
    hlow' hdecode ((hmode (pre.length + 1 + 3)).of_cs_lma_eq rfl rfl)

end X86Proofs
