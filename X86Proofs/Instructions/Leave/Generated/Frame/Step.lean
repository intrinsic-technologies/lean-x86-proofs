import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Call.Step
import X86Proofs.Instructions.Leave.Generated.Frame.Decode
import X86Proofs.Instructions.Leave.Generated.Frame.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem leave_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hmode64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xC9]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hr : MemReadable s ((Operand.reg 5 : Operand 64).read s) 8) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      leaveState { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xC9]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xC9]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_C9_leave s h _ hrex2 _ pre.length (by omega)
    (by simp) hcode hlow'
  obtain ⟨hd, hss⟩ := call_start h (pre.length + 2)
  rw [leave_form _ _ _ hmode64 hosz hlock (hmode _) hd hss (hr.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xC9 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem leave16_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hmode64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw0 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hcode : BytesAt s s.RIP (pre ++ [0xC9]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hr : MemReadable s ((Operand.reg 5 : Operand 64).read s) 2) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      leaveState16 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xC9]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xC9]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_C9_leave s h _ hrex2 _ pre.length (by omega)
    (by simp) hcode hlow'
  obtain ⟨hd, hss⟩ := call_start h (pre.length + 2)
  rw [leave16_form _ _ _ hmode64 hosz hw0 hlock (hmode _) hd hss (hr.of_external_eq rfl)]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xC9 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

end X86Proofs
