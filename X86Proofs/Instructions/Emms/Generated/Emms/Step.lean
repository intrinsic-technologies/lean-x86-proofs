import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.Mmx
import X86Proofs.Instructions.Emms.Generated.Emms.Decode
import X86Proofs.Instructions.Emms.Generated.Emms.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem emms_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0) (hes : fswES s.FP87_Status = 0)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor s CPUID_MMX_Encoding true)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0x0F, 0x77]))
    (hlow : s.RIP.toNat + (pre.length + 2) ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2) fun t =>
      { t with
        Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2))
        FP87_Tag_Word := emmsSpec
        FP87_Status := mmxStatus t.FP87_Status })) := by
  have hlen' : (pre ++ [0x0F, 0x77]).length = pre.length + 2 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x0F, 0x77]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hcr0' (k : Nat) : Prelude.CR0.SSEEnabled (afterFetches (beforeFetch s) k).CR0 := hcr0
  have hes' (k : Nat) : fswES (afterFetches (beforeFetch s) k).FP87_Status = 0 := hes
  have hdecode := decodeLegacy1_run_of_77_mmx s h hmmx _ (pre.length + 1) hcode hlow'
    (by simp) (by omega) _ hrex2 hosz
  rw [emms_form _ _ _ (hcr0' _) (hes' _) hrep hlock hosz,
    show pre.length + 1 + 1 = pre.length + 2 by omega,
    show pre.length + 1 + 2 = pre.length + 2 + 1 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0x77 [] hpre ⟨by decide, by decide⟩ (by omega)
    hcode hlow' hdecode ((hmode (pre.length + 2 + 1)).of_cs_lma_eq rfl rfl)

end X86Proofs
