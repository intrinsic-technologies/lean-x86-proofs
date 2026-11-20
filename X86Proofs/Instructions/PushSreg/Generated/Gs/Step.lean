import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Call.Step
import X86Proofs.Instructions.PushSreg.Generated.Gs.Decode
import X86Proofs.Instructions.PushSreg.Generated.Gs.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem push_gs_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hmode64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0x0F, 0xA8]))
    (hlow : s.RIP.toNat + (pre.length + 2) ≤ 2^32)
    (hw : MemWritable s (pushAddr s) 8) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2) fun t =>
      pushState { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2)) }
        (pushsregSpec 64 s.GS.selector))) := by
  have hlen' : (pre ++ [0x0F, 0xA8]).length = pre.length + 2 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x0F, 0xA8]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy1_run_of_A8_push s h _ (pre.length + 1) hcode hlow'
    (by simp) (by omega) _ hrex2
  obtain ⟨hd, hss⟩ := call_start h (pre.length + 1 + 2)
  rw [push_gs_form _ _ _ hmode64 hosz hlock hd (hmode _) hss
      (hw.of_external_eq rfl),
    show pre.length + 1 + 1 = pre.length + 2 by omega,
    show pre.length + 1 + 2 = pre.length + 2 + 1 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xA8 [] hpre ⟨by decide, by decide⟩ (by omega)
    hcode hlow' hdecode ((hmode (pre.length + 2 + 1)).of_cs_lma_eq rfl rfl)

theorem push16_gs_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hmode64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw0 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hcode : BytesAt s s.RIP (pre ++ [0x0F, 0xA8]))
    (hlow : s.RIP.toNat + (pre.length + 2) ≤ 2^32)
    (hw : MemWritable s (pushAddr16 s) 2) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2) fun t =>
      pushState16 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2)) }
        (pushsregSpec 16 s.GS.selector))) := by
  have hlen' : (pre ++ [0x0F, 0xA8]).length = pre.length + 2 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x0F, 0xA8]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy1_run_of_A8_push s h _ (pre.length + 1) hcode hlow'
    (by simp) (by omega) _ hrex2
  obtain ⟨hd, hss⟩ := call_start h (pre.length + 1 + 2)
  rw [push16_gs_form _ _ _ hmode64 hosz hw0 hlock hd (hmode _) hss
      (hw.of_external_eq rfl),
    show pre.length + 1 + 1 = pre.length + 2 by omega,
    show pre.length + 1 + 2 = pre.length + 2 + 1 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xA8 [] hpre ⟨by decide, by decide⟩ (by omega)
    hcode hlow' hdecode ((hmode (pre.length + 2 + 1)).of_cs_lma_eq rfl rfl)

end X86Proofs
