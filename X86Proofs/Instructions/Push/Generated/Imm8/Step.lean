import X86Proofs.Step.AfterStep
import X86Proofs.Step.FetchImm
import X86Proofs.Instructions.Call.Step
import X86Proofs.Instructions.Push.Generated.Imm8.Decode
import X86Proofs.Instructions.Push.Generated.Imm8.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem push_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hmode64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (imm : BitVec 8) (hcode : BytesAt s s.RIP (pre ++ 0x6A :: immBytes 8 imm))
    (hlow : s.RIP.toNat + (pre.length + 2) ≤ 2^32)
    (hw : MemWritable s (pushAddr s) 8) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2) fun t =>
      pushState { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2)) }
        (imm.signExtend 64))) := by
  have hlen' : (pre ++ 0x6A :: immBytes 8 imm).length = pre.length + 2 := by simp
  have hlow' : s.RIP.toNat + (pre ++ 0x6A :: immBytes 8 imm).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_6A_push s h _ hrex2 _ pre.length (by omega)
    (by simp) hcode hlow'
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (pre ++ 0x6A :: immBytes 8 imm) := hcode
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 2) h.fetchReady hc
    hlow' 8 (by decide) imm (pre.length + 1)
    (fun j hj => by
      rw [List.getElem?_append_right (by omega),
        show pre.length + 1 + j - pre.length = j + 1 by omega, List.getElem?_cons_succ]
      exact immBytes_getElem? imm hj)
    (by rw [hlen']; omega) (by omega)
  obtain ⟨hd, hss⟩ := call_start h (pre.length + 2 + 8 / 8)
  rw [push_imm8_form _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))) _ imm
    hmode64 hosz hlock himm hd hss (hw.of_external_eq rfl),
    add_ofNat_add, show pre.length + 1 + 1 = pre.length + 2 by omega,
    show pre.length + 2 + 8 / 8 = pre.length + 2 + 1 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x6A _ hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2 + 1)).of_cs_lma_eq rfl rfl)

theorem push16_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hmode64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw0 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (imm : BitVec 8) (hcode : BytesAt s s.RIP (pre ++ 0x6A :: immBytes 8 imm))
    (hlow : s.RIP.toNat + (pre.length + 2) ≤ 2^32)
    (hw : MemWritable s (pushAddr16 s) 2) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2) fun t =>
      pushState16 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2)) }
        (imm.signExtend 16))) := by
  have hlen' : (pre ++ 0x6A :: immBytes 8 imm).length = pre.length + 2 := by simp
  have hlow' : s.RIP.toNat + (pre ++ 0x6A :: immBytes 8 imm).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_6A_push s h _ hrex2 _ pre.length (by omega)
    (by simp) hcode hlow'
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (pre ++ 0x6A :: immBytes 8 imm) := hcode
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 2) h.fetchReady hc
    hlow' 8 (by decide) imm (pre.length + 1)
    (fun j hj => by
      rw [List.getElem?_append_right (by omega),
        show pre.length + 1 + j - pre.length = j + 1 by omega, List.getElem?_cons_succ]
      exact immBytes_getElem? imm hj)
    (by rw [hlen']; omega) (by omega)
  obtain ⟨hd, hss⟩ := call_start h (pre.length + 2 + 8 / 8)
  rw [push16_imm8_form _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))) _ imm
    hmode64 hosz hw0 hlock himm hd hss (hw.of_external_eq rfl),
    add_ofNat_add, show pre.length + 1 + 1 = pre.length + 2 by omega,
    show pre.length + 2 + 8 / 8 = pre.length + 2 + 1 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x6A _ hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2 + 1)).of_cs_lma_eq rfl rfl)

end X86Proofs
