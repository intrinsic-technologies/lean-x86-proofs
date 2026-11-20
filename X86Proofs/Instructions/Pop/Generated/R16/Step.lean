import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Call.Step
import X86Proofs.Instructions.Pop.Form
import X86Proofs.Instructions.Pop.Generated.R16.Decode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem pop_r16_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hmode64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw0 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (op : UInt8) (hop : PopOpcode op) (hcode : BytesAt s s.RIP (pre ++ [op]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hr : MemReadable s (stackPtr s) 2) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      popState16 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) }
        (gprNumber ctx.rex_b4 ctx.rex_b3 (opcodeReg op)))) := by
  intro ctx
  have hlen' : (pre ++ [op]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [op]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_pop_at s h _ hrex2 op hop _ pre.length (by omega)
    (by simp) hcode hlow'
  obtain ⟨hd, hss⟩ := call_start h (pre.length + 2)
  rw [pop_r16_form _ _ _ _ hmode64 hosz hw0 hlock (hmode _) hd hss (hr.of_external_eq rfl)]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre op [] hpre hop.legacyOpcode (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

end X86Proofs
