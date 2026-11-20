import X86Proofs.Step.AfterStep
import X86Proofs.Step.FetchImm
import X86Proofs.Instructions.Call.Step
import X86Proofs.Instructions.Push.Generated.Imm32.Decode
import X86Proofs.Instructions.Push.Generated.Imm32.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem push_imm32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hmode64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (imm : BitVec 32) (hcode : BytesAt s s.RIP (pre ++ 0x68 :: immBytes 32 imm))
    (hlow : s.RIP.toNat + (pre.length + 5) ≤ 2^32)
    (hw : MemWritable s (pushAddr s) 8) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 5) fun t =>
      pushState { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 5)) }
        (imm.signExtend 64))) := by
  have hlen' : (pre ++ 0x68 :: immBytes 32 imm).length = pre.length + 5 := by simp
  have hlow' : s.RIP.toNat + (pre ++ 0x68 :: immBytes 32 imm).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_68_push s h _ hrex2 _ pre.length (by omega)
    (by simp) hcode hlow'
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (pre ++ 0x68 :: immBytes 32 imm) := hcode
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 2) h.fetchReady hc
    hlow' 32 (by decide) imm (pre.length + 1)
    (fun j hj => by
      rw [List.getElem?_append_right (by omega),
        show pre.length + 1 + j - pre.length = j + 1 by omega, List.getElem?_cons_succ]
      exact immBytes_getElem? imm hj)
    (by rw [hlen']; omega) (by omega)
  obtain ⟨hd, hss⟩ := call_start h (pre.length + 2 + 32 / 8)
  rw [push_imm32_form _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))) _ imm
    hmode64 hosz hlock himm hd hss (hw.of_external_eq rfl),
    add_ofNat_add, show pre.length + 1 + 4 = pre.length + 5 by omega,
    show pre.length + 2 + 32 / 8 = pre.length + 5 + 1 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x68 _ hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 5 + 1)).of_cs_lma_eq rfl rfl)

theorem push16_imm16_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hmode64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw0 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (imm : BitVec 16) (hcode : BytesAt s s.RIP (pre ++ 0x68 :: immBytes 16 imm))
    (hlow : s.RIP.toNat + (pre.length + 3) ≤ 2^32)
    (hw : MemWritable s (pushAddr16 s) 2) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3) fun t =>
      pushState16 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3)) }
        (imm.signExtend 16))) := by
  have hlen' : (pre ++ 0x68 :: immBytes 16 imm).length = pre.length + 3 := by simp
  have hlow' : s.RIP.toNat + (pre ++ 0x68 :: immBytes 16 imm).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_68_push s h _ hrex2 _ pre.length (by omega)
    (by simp) hcode hlow'
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (pre ++ 0x68 :: immBytes 16 imm) := hcode
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 2) h.fetchReady hc
    hlow' 16 (by decide) imm (pre.length + 1)
    (fun j hj => by
      rw [List.getElem?_append_right (by omega),
        show pre.length + 1 + j - pre.length = j + 1 by omega, List.getElem?_cons_succ]
      exact immBytes_getElem? imm hj)
    (by rw [hlen']; omega) (by omega)
  obtain ⟨hd, hss⟩ := call_start h (pre.length + 2 + 16 / 8)
  rw [push16_imm16_form _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))) _ imm
    hmode64 hosz hw0 hlock himm hd hss (hw.of_external_eq rfl),
    add_ofNat_add, show pre.length + 1 + 2 = pre.length + 3 by omega,
    show pre.length + 2 + 16 / 8 = pre.length + 3 + 1 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x68 _ hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 3 + 1)).of_cs_lma_eq rfl rfl)

end X86Proofs
