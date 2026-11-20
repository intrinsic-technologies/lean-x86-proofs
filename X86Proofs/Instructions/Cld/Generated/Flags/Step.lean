
import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Cld.Generated.Flags.Decode
import X86Proofs.Instructions.Cld.Generated.Flags.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cld_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xFC]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      writeResult t (Operand.df : Operand 1) cldSpec
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))))) := by
  have hlen' : (pre ++ [0xFC]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xFC]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_FC_cld s h _ hrex2 _ pre.length (by omega)
    (by simp) hcode hlow'
  rw [cld_form _ _ _ hlock] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xFC [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

end X86Proofs
