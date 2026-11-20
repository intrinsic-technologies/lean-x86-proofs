
import X86Proofs.Step.AfterStep
import X86Proofs.Step.PrefixScan
import X86Proofs.Program.ReadWrite.X87
import X86Proofs.Instructions.Fwait.Generated.Fwait.Decode
import X86Proofs.Instructions.Fwait.Generated.Fwait.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem fwait_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0)
    (hes : fswES s.FP87_Status = 0)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0x9B]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      x87CtlOut t (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))) 4
          (fswCCOracle t.FP87_Status t.oracle))) := by
  have hlen' : (pre ++ [0x9B]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x9B]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hdecode := decodeLegacy0_run_of_fwait s h _ hrex2 _ pre.length (by omega) (by simp) hcode
      hlow'
  let t := afterFetches (beforeFetch s) (pre.length + 2)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [fwait_form t _ _ hlock hcr0 hes] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x9B _ hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    (hmode.of_cs_lma_eq rfl rfl)

end X86Proofs
