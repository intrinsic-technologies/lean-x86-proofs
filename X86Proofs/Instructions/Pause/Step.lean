import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Pause.Decode

/-!
# Layer 3: PAUSE

`pause_step`: for any prefix list the scan covers with `F3` (`rep_prefix = 243`), outside VMX
non-root operation, one `step` only moves RIP past the instruction (as a NOP:
`withNextIP`, whose step facts are `Instructions/Nop/Step.lean`'s).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- Layer 3 for `PAUSE` (`F3 90`, any prefix list with `F3`): one `step` only moves RIP. -/
theorem pause_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hvmx : s.VMX_Operation_Mode ≠ VMX_Operation_Type.VMX_Non_Root)
    (hcode : BytesAt s s.RIP (pre ++ [0x90]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      withNextIP t (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))))) := by
  have hlen' : (pre ++ [0x90]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x90]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_90_pause s h _ hrex2 hrep _ pre.length (by omega)
    (by simp) hcode hlow'
  rw [pause_form (afterFetches (beforeFetch s) (pre.length + 2)) _ _ hlock hvmx] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x90 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

end X86Proofs
