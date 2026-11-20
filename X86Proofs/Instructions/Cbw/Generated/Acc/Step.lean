
import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Cbw.Generated.Acc.Decode
import X86Proofs.Instructions.Cbw.Generated.Acc.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cdqe_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hcode : BytesAt s s.RIP (pre ++ [0x98]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      writeResult t (Operand.reg 0 : Operand 64) (cbwSpec 64 ((Operand.reg 0 : Operand 32).read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))))) := by
  have hlen' : (pre ++ [0x98]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x98]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_98_cdqe s h _ hrex2 hw _ pre.length
    (by omega) (by simp) hcode hlow'
  rw [cdqe_form _ _ _ hlock hw] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x98 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem cwde_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hcode : BytesAt s s.RIP (pre ++ [0x98]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      writeResult t (Operand.reg 0 : Operand 32) (cbwSpec 32 ((Operand.reg 0 : Operand 16).read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))))) := by
  have hlen' : (pre ++ [0x98]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x98]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_98_cwde s h _ hrex2 hosz hw _ pre.length
    (by omega) (by simp) hcode hlow'
  rw [cwde_form _ _ _ hlock hosz hw] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x98 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem cbw_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hcode : BytesAt s s.RIP (pre ++ [0x98]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      writeResult t (Operand.reg 0 : Operand 16) (cbwSpec 16 ((Operand.reg 0 : Operand 8).read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))))) := by
  have hlen' : (pre ++ [0x98]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x98]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_98_cbw s h _ hrex2 hosz hw _ pre.length
    (by omega) (by simp) hcode hlow'
  rw [cbw_form _ _ _ hlock hosz hw] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x98 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

end X86Proofs
