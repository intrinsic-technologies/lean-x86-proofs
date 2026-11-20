import X86Proofs.Step.AfterStep
import X86Proofs.Step.FetchImm
import X86Proofs.Instructions.Call.Step
import X86Proofs.Instructions.Enter.Generated.Frame.Decode
import X86Proofs.Instructions.Enter.Generated.Frame.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem enter_l0_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hmode64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (size : BitVec 16) (hcode : BytesAt s s.RIP (pre ++ 0xC8 :: (immBytes 16 size ++ [0x00])))
    (hlow : s.RIP.toNat + (pre.length + 4) ≤ 2^32) (hw : MemWritable s (pushAddr s) 8)
    (hcheck : (pushAddr s - size.setWidth 64).toNat + 8 ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 4) fun t =>
      enterState0 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4)) }
        size)) := by
  have hlen' : (pre ++ 0xC8 :: (immBytes 16 size ++ [0x00])).length = pre.length + 4 := by simp
  have hlow' : s.RIP.toNat + (pre ++ 0xC8 :: (immBytes 16 size ++ [0x00])).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_C8_enter s h _ hrex2 _ pre.length (by omega)
    (by simp) hcode hlow'
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0xC8 :: (immBytes 16 size ++ [0x00])) := hcode
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 2) h.fetchReady hc
    hlow' 16 (by decide) size (pre.length + 1)
    (fun j hj => by
      rw [List.getElem?_append_right (by omega),
        show pre.length + 1 + j - pre.length = j + 1 by omega, List.getElem?_cons_succ,
        List.getElem?_append_left (by simpa using hj)]
      exact immBytes_getElem? size hj)
    (by rw [hlen']; omega) (by omega)
  have hlevel := memFetch_run_of_bytesAt (beforeFetch s) (pre.length + 2 + 16 / 8) h.fetchReady hc
    hlow' (pre.length + 3) (by simp) (by omega)
  simp only [show (pre ++ 0xC8 :: (immBytes 16 size ++ [0x00]))[pre.length + 3] = 0x00 by
    simp] at hlevel
  rw [show pre.length + 3 = pre.length + 1 + 2 by omega, ← add_ofNat_add] at hlevel
  obtain ⟨hd, hss⟩ := call_start h (pre.length + 2 + 16 / 8 + 1)
  rw [enter_l0_form _ _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))) _ size hmode64
    hosz hlock (hmode _) (call_start h (pre.length + 2)).2 himm hlevel hd hss
    (hw.of_external_eq rfl) hcheck,
    add_ofNat_add, show pre.length + 1 + 3 = pre.length + 4 by omega,
    show pre.length + 2 + 16 / 8 + 1 = pre.length + 4 + 1 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xC8 _ hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 4 + 1)).of_cs_lma_eq rfl rfl)

theorem enter_l1_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hmode64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (size : BitVec 16) (hcode : BytesAt s s.RIP (pre ++ 0xC8 :: (immBytes 16 size ++ [0x01])))
    (hlow : s.RIP.toNat + (pre.length + 4) ≤ 2^32) (hw : MemWritable s (pushAddr s) 8)
    (hw2 : MemWritable s (pushAddr s - 8) 8)
    (hcheck : (pushAddr s - 8 - size.setWidth 64).toNat + 8 ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 4) fun t =>
      enterState1 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4)) }
        size)) := by
  have hlen' : (pre ++ 0xC8 :: (immBytes 16 size ++ [0x01])).length = pre.length + 4 := by simp
  have hlow' : s.RIP.toNat + (pre ++ 0xC8 :: (immBytes 16 size ++ [0x01])).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_C8_enter s h _ hrex2 _ pre.length (by omega)
    (by simp) hcode hlow'
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0xC8 :: (immBytes 16 size ++ [0x01])) := hcode
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 2) h.fetchReady hc
    hlow' 16 (by decide) size (pre.length + 1)
    (fun j hj => by
      rw [List.getElem?_append_right (by omega),
        show pre.length + 1 + j - pre.length = j + 1 by omega, List.getElem?_cons_succ,
        List.getElem?_append_left (by simpa using hj)]
      exact immBytes_getElem? size hj)
    (by rw [hlen']; omega) (by omega)
  have hlevel := memFetch_run_of_bytesAt (beforeFetch s) (pre.length + 2 + 16 / 8) h.fetchReady hc
    hlow' (pre.length + 3) (by simp) (by omega)
  simp only [show (pre ++ 0xC8 :: (immBytes 16 size ++ [0x01]))[pre.length + 3] = 0x01 by
    simp] at hlevel
  rw [show pre.length + 3 = pre.length + 1 + 2 by omega, ← add_ofNat_add] at hlevel
  obtain ⟨hd, hss⟩ := call_start h (pre.length + 2 + 16 / 8 + 1)
  rw [enter_l1_form _ _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))) _ size hmode64
    hosz hlock (hmode _) (call_start h (pre.length + 2)).2 himm hlevel hd hss
    (hw.of_external_eq rfl) (hw2.of_external_eq rfl) hcheck,
    add_ofNat_add, show pre.length + 1 + 3 = pre.length + 4 by omega,
    show pre.length + 2 + 16 / 8 + 1 = pre.length + 4 + 1 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xC8 _ hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 4 + 1)).of_cs_lma_eq rfl rfl)

theorem enter_ln_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hmode64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (size : BitVec 16) (L : Nat) (hL : 2 ≤ L) (hL' : L < 32) (hcode : BytesAt s s.RIP (pre ++ 0xC8 :: (immBytes 16 size ++ [UInt8.ofNat L])))
    (hlow : s.RIP.toNat + (pre.length + 4) ≤ 2^32)
    (hw : ∀ k ≤ L, MemWritable s (pushAddr s - 8 * BitVec.ofNat 64 k) 8)
    (hr : ∀ k < L - 1,
      MemReadable s ((Operand.reg 5 : Operand 64).read s - 8 * BitVec.ofNat 64 (k + 1)) 8)
    (hcheck : (pushAddr s - 8 * BitVec.ofNat 64 L - size.setWidth 64).toNat + 8 ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 4) fun t =>
      enterStateN { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4)) }
        L size)) := by
  have hlen' : (pre ++ 0xC8 :: (immBytes 16 size ++ [UInt8.ofNat L])).length = pre.length + 4 := by simp
  have hlow' : s.RIP.toNat + (pre ++ 0xC8 :: (immBytes 16 size ++ [UInt8.ofNat L])).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_C8_enter s h _ hrex2 _ pre.length (by omega)
    (by simp) hcode hlow'
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0xC8 :: (immBytes 16 size ++ [UInt8.ofNat L])) := hcode
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 2) h.fetchReady hc
    hlow' 16 (by decide) size (pre.length + 1)
    (fun j hj => by
      rw [List.getElem?_append_right (by omega),
        show pre.length + 1 + j - pre.length = j + 1 by omega, List.getElem?_cons_succ,
        List.getElem?_append_left (by simpa using hj)]
      exact immBytes_getElem? size hj)
    (by rw [hlen']; omega) (by omega)
  have hlevel := memFetch_run_of_bytesAt (beforeFetch s) (pre.length + 2 + 16 / 8) h.fetchReady hc
    hlow' (pre.length + 3) (by simp) (by omega)
  simp only [show (pre ++ 0xC8 :: (immBytes 16 size ++ [UInt8.ofNat L]))[pre.length + 3] = UInt8.ofNat L by
    simp] at hlevel
  rw [show pre.length + 3 = pre.length + 1 + 2 by omega, ← add_ofNat_add] at hlevel
  obtain ⟨hd, hss⟩ := call_start h (pre.length + 2 + 16 / 8 + 1)
  rw [enter_ln_form _ _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))) _ size L hL hL'
    hmode64 hosz hlock (hmode _) (call_start h (pre.length + 2)).2 himm hlevel hd hss
    (fun k hk => (hw k hk).of_external_eq rfl) (fun k hk => (hr k hk).of_external_eq rfl) hcheck,
    add_ofNat_add, show pre.length + 1 + 3 = pre.length + 4 by omega,
    show pre.length + 2 + 16 / 8 + 1 = pre.length + 4 + 1 by omega] at hdecode
  have hkeep (t : RamState) :
      (enterStateN t L size).Repeat_String_Operation = t.Repeat_String_Operation := by
    obtain ⟨e, o, tr, he⟩ := enterCopies_eq (pushMem t (pushAddr t)
      ((Operand.reg 5 : Operand 64).read t)) (pushAddr t) ((Operand.reg 5 : Operand 64).read t)
      (L - 1)
    simp only [enterStateN, he]
    simp [enterFinish, checkAccess, pushMem, Operand.write, stackAccess]
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · simp only [hkeep]
    exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xC8 _ hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 4 + 1)).of_cs_lma_eq (enterStateN_CS _ _ _)
      (by rw [enterStateN_IA32_EFER]))

end X86Proofs
