import X86Proofs.Step.AfterStep
import X86Proofs.Step.FetchImm
import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Instructions.Mov.Generated.MoffsStore.Decode
import X86Proofs.Instructions.Mov.Generated.MoffsStore.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem mov_moffs_rax_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 6)
    (n : Nat) (hn : n = 64 ∨ n = 32 ∨ n = 16)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (hctx : SegMoffsContext (scanContext s.DS (PrefixSegments.ofState s) pre) s.DS)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false) (moffs : BitVec 64)
    (hcode : BytesAt s s.RIP (pre ++ 0xA3 :: immBytes 64 moffs))
    (hlow : s.RIP.toNat + (pre.length + 9) ≤ 2^32)
    (hw : MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) moffs) (n / 8)) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 9) fun t =>
      writeResult (dataAccess t "store") (.mem (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) moffs) : Operand n)
        (movSpec ((Operand.reg 0 : Operand n).read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 9))))) := by
  have hlen' : (pre ++ 0xA3 :: immBytes 64 moffs).length = pre.length + 9 := by simp
  have hlow' : s.RIP.toNat + (pre ++ 0xA3 :: immBytes 64 moffs).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_A3_moffs s h _ hrex2 _ pre.length (by omega) (by simp) hcode
    hlow'
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (pre ++ 0xA3 :: immBytes 64 moffs) := hcode
  have hoff := directMemoryOffset_run_seg (beforeFetch s) (pre.length + 2) h.fetchReady h.cpu.ds _ hctx
    hc hlow' moffs (pre.length + 1)
    (fun j hj => by
      rw [List.getElem?_append_right (by omega),
        show pre.length + 1 + j - pre.length = j + 1 by omega, List.getElem?_cons_succ]
      exact immBytes_getElem? moffs hj)
    (by rw [hlen']; omega) (by omega)
  rw [show pre.length + 1 + 8 = pre.length + 9 by omega,
    show pre.length + 2 + 8 = pre.length + 9 + 1 by omega] at hoff
  rw [mov_m_rax_form _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))) _
    n hn hsize hctx.addr hrex2 hlock _ _ _ hoff (by rw [handleRIPRelativeAddress64_run]; rfl) _
    (SegAccess.ctx hctx.seg false moffs) (memAlu_dataReady h _) (hw.of_external_eq rfl)] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xA3 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode ((hmode (pre.length + 9 + 1)).of_cs_lma_eq rfl rfl)

theorem mov_moffs_rax_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 10)
    (n : Nat) (hn : n = 64 ∨ n = 32 ∨ n = 16)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (hctx : SegMoffsContext32 (scanContext s.DS (PrefixSegments.ofState s) pre) s.DS)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false) (moffs : BitVec 32)
    (hcode : BytesAt s s.RIP (pre ++ 0xA3 :: immBytes 32 moffs))
    (hlow : s.RIP.toNat + (pre.length + 5) ≤ 2^32)
    (hw : MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (moffs.setWidth 64)) (n / 8)) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 5) fun t =>
      writeResult (dataAccess t "store") (.mem (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (moffs.setWidth 64)) : Operand n)
        (movSpec ((Operand.reg 0 : Operand n).read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 5))))) := by
  have hlen' : (pre ++ 0xA3 :: immBytes 32 moffs).length = pre.length + 5 := by simp
  have hlow' : s.RIP.toNat + (pre ++ 0xA3 :: immBytes 32 moffs).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_A3_moffs s h _ hrex2 _ pre.length (by omega) (by simp) hcode
    hlow'
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (pre ++ 0xA3 :: immBytes 32 moffs) := hcode
  have hoff := directMemoryOffset32_run_seg (beforeFetch s) (pre.length + 2) h.fetchReady h.cpu.ds _ hctx
    hc hlow' moffs (pre.length + 1)
    (fun j hj => by
      rw [List.getElem?_append_right (by omega),
        show pre.length + 1 + j - pre.length = j + 1 by omega, List.getElem?_cons_succ]
      exact immBytes_getElem? moffs hj)
    (by rw [hlen']; omega) (by omega)
  rw [show pre.length + 1 + 4 = pre.length + 5 by omega,
    show pre.length + 2 + 4 = pre.length + 5 + 1 by omega] at hoff
  rw [mov_m_rax_form _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))) _
    n hn hsize hctx.addr hrex2 hlock _ _ _ hoff (handleRIPRelativeAddress32_zext_run _ _) _
    (SegAccess.ctx hctx.seg false (moffs.setWidth 64)) (memAlu_dataReady h _) (hw.of_external_eq rfl)] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xA3 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode ((hmode (pre.length + 5 + 1)).of_cs_lma_eq rfl rfl)

theorem mov_moffs8_al_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 6)
    (hctx : SegMoffsContext (scanContext s.DS (PrefixSegments.ofState s) pre) s.DS)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false) (moffs : BitVec 64)
    (hcode : BytesAt s s.RIP (pre ++ 0xA2 :: immBytes 64 moffs))
    (hlow : s.RIP.toNat + (pre.length + 9) ≤ 2^32)
    (hw : MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) moffs) 1) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 9) fun t =>
      writeResult (dataAccess t "store") (.mem (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) moffs) : Operand 8)
        (movSpec ((Operand.reg 0 : Operand 8).read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 9))))) := by
  have hlen' : (pre ++ 0xA2 :: immBytes 64 moffs).length = pre.length + 9 := by simp
  have hlow' : s.RIP.toNat + (pre ++ 0xA2 :: immBytes 64 moffs).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_A2_moffs s h _ hrex2 _ pre.length (by omega) (by simp) hcode
    hlow'
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (pre ++ 0xA2 :: immBytes 64 moffs) := hcode
  have hoff := directMemoryOffset_run_seg (beforeFetch s) (pre.length + 2) h.fetchReady h.cpu.ds _ hctx
    hc hlow' moffs (pre.length + 1)
    (fun j hj => by
      rw [List.getElem?_append_right (by omega),
        show pre.length + 1 + j - pre.length = j + 1 by omega, List.getElem?_cons_succ]
      exact immBytes_getElem? moffs hj)
    (by rw [hlen']; omega) (by omega)
  rw [show pre.length + 1 + 8 = pre.length + 9 by omega,
    show pre.length + 2 + 8 = pre.length + 9 + 1 by omega] at hoff
  rw [mov_m8_al_form _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))) _
    hctx.addr hrex2 hlock _ _ _ hoff (by rw [handleRIPRelativeAddress64_run]; rfl) _
    (SegAccess.ctx hctx.seg false moffs) (memAlu_dataReady h _) (hw.of_external_eq rfl)] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xA2 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode ((hmode (pre.length + 9 + 1)).of_cs_lma_eq rfl rfl)

theorem mov_moffs8_al_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 10)
    (hctx : SegMoffsContext32 (scanContext s.DS (PrefixSegments.ofState s) pre) s.DS)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false) (moffs : BitVec 32)
    (hcode : BytesAt s s.RIP (pre ++ 0xA2 :: immBytes 32 moffs))
    (hlow : s.RIP.toNat + (pre.length + 5) ≤ 2^32)
    (hw : MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (moffs.setWidth 64)) 1) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 5) fun t =>
      writeResult (dataAccess t "store") (.mem (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (moffs.setWidth 64)) : Operand 8)
        (movSpec ((Operand.reg 0 : Operand 8).read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 5))))) := by
  have hlen' : (pre ++ 0xA2 :: immBytes 32 moffs).length = pre.length + 5 := by simp
  have hlow' : s.RIP.toNat + (pre ++ 0xA2 :: immBytes 32 moffs).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_A2_moffs s h _ hrex2 _ pre.length (by omega) (by simp) hcode
    hlow'
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (pre ++ 0xA2 :: immBytes 32 moffs) := hcode
  have hoff := directMemoryOffset32_run_seg (beforeFetch s) (pre.length + 2) h.fetchReady h.cpu.ds _ hctx
    hc hlow' moffs (pre.length + 1)
    (fun j hj => by
      rw [List.getElem?_append_right (by omega),
        show pre.length + 1 + j - pre.length = j + 1 by omega, List.getElem?_cons_succ]
      exact immBytes_getElem? moffs hj)
    (by rw [hlen']; omega) (by omega)
  rw [show pre.length + 1 + 4 = pre.length + 5 by omega,
    show pre.length + 2 + 4 = pre.length + 5 + 1 by omega] at hoff
  rw [mov_m8_al_form _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))) _
    hctx.addr hrex2 hlock _ _ _ hoff (handleRIPRelativeAddress32_zext_run _ _) _
    (SegAccess.ctx hctx.seg false (moffs.setWidth 64)) (memAlu_dataReady h _) (hw.of_external_eq rfl)] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xA2 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode ((hmode (pre.length + 5 + 1)).of_cs_lma_eq rfl rfl)

end X86Proofs
