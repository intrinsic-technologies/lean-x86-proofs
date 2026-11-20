import X86Proofs.Step.AfterStep
import X86Proofs.Step.FetchImm
import X86Proofs.Instructions.Branch.Step
import X86Proofs.Instructions.Jrcxz.Generated.Rel8.Decode
import X86Proofs.Instructions.Jrcxz.Generated.Rel8.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem jrcxz_rel8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (disp : BitVec 8) (hcode : BytesAt s s.RIP (pre ++ 0xE3 :: immBytes 8 disp))
    (hlow : s.RIP.toNat + (pre.length + 2) ≤ 2^32)
    (htarget : rcx.read s = 0#64 →
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2))) (disp.signExtend 64)).toNat < 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2) fun t =>
      branchState t (rcx.read s == 0#64) (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2)))
        (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2))) (disp.signExtend 64)))) := by
  have hlen' : (pre ++ 0xE3 :: immBytes 8 disp).length = pre.length + 2 := by simp
  have hlow' : s.RIP.toNat + (pre ++ 0xE3 :: immBytes 8 disp).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_E3_jrcxz s h _ hrex2 haddr _ pre.length
    (by omega) (by simp) hcode hlow'
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (pre ++ 0xE3 :: immBytes 8 disp) := hcode
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 2) h.fetchReady hc
    hlow' 8 (by decide) disp (pre.length + 1)
    (fun j hj => by
      rw [List.getElem?_append_right (by omega),
        show pre.length + 1 + j - pre.length = j + 1 by omega, List.getElem?_cons_succ]
      exact immBytes_getElem? disp hj)
    (by rw [hlen']; omega) (by omega)
  rw [jrcxz_rel8_form _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))) _ disp
    haddr hlock hrex2 himm (hmode _)
    (h.branchReady _) (by rw [add_ofNat_add]; exact htarget),
    add_ofNat_add, show pre.length + 1 + 1 = pre.length + 2 by omega,
    show pre.length + 2 + 8 / 8 = pre.length + 2 + 1 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · cases rcx.read s == 0#64 <;> exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xE3 _ hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2 + 1)).of_cs_lma_eq
      (by cases rcx.read s == 0#64 <;> rfl)
      (by cases rcx.read s == 0#64 <;> rfl))

theorem jecxz_rel8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (disp : BitVec 8) (hcode : BytesAt s s.RIP (pre ++ 0xE3 :: immBytes 8 disp))
    (hlow : s.RIP.toNat + (pre.length + 2) ≤ 2^32)
    (htarget : (rcx.read s).setWidth 32 = 0#32 →
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2))) (disp.signExtend 64)).toNat < 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2) fun t =>
      branchState t ((rcx.read s).setWidth 32 == 0#32) (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2)))
        (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2))) (disp.signExtend 64)))) := by
  have hlen' : (pre ++ 0xE3 :: immBytes 8 disp).length = pre.length + 2 := by simp
  have hlow' : s.RIP.toNat + (pre ++ 0xE3 :: immBytes 8 disp).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_E3_jecxz s h _ hrex2 haddr _ pre.length
    (by omega) (by simp) hcode hlow'
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (pre ++ 0xE3 :: immBytes 8 disp) := hcode
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 2) h.fetchReady hc
    hlow' 8 (by decide) disp (pre.length + 1)
    (fun j hj => by
      rw [List.getElem?_append_right (by omega),
        show pre.length + 1 + j - pre.length = j + 1 by omega, List.getElem?_cons_succ]
      exact immBytes_getElem? disp hj)
    (by rw [hlen']; omega) (by omega)
  rw [jecxz_rel8_form _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))) _ disp
    haddr hlock hrex2 himm (hmode _)
    (h.branchReady _) (by rw [add_ofNat_add]; exact htarget),
    add_ofNat_add, show pre.length + 1 + 1 = pre.length + 2 by omega,
    show pre.length + 2 + 8 / 8 = pre.length + 2 + 1 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · cases (rcx.read s).setWidth 32 == 0#32 <;> exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xE3 _ hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2 + 1)).of_cs_lma_eq
      (by cases (rcx.read s).setWidth 32 == 0#32 <;> rfl)
      (by cases (rcx.read s).setWidth 32 == 0#32 <;> rfl))

end X86Proofs
