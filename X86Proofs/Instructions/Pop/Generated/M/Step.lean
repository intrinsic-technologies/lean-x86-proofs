import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Call.Step
import X86Proofs.Instructions.Pop.Generated.M.Decode
import X86Proofs.Instructions.Pop.Generated.M.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem pop_m64_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x8F :: am.modrm 0 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hr : MemReadable s (stackPtr s) 8)
    (hw : MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (popMemAddr am 64
      (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) s)) 8) :
    let len := pre.length + 2 + am.tail.length
    X86.Machine.step s = some (.next (afterStep s len fun t =>
      popMemAtState t 64 (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)) am (BitVec.add s.RIP (BitVec.ofNat 64 len)))) := by
  intro len
  have hlen' : (pre ++ 0x8F :: am.modrm 0 :: am.tail).length = len := by
    simp [len]; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x8F :: am.modrm 0 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_8F_pop_memory s h _ pre.length (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode
    hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0x8F 0 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = len + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (len + 1)
  let next := BitVec.add s.RIP (BitVec.ofNat 64 len)
  obtain ⟨hd, hss⟩ := call_start h (len + 1)
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s) next
  have hat : popMemAddr am 64 next t = popMemAddr am 64 next s :=
    popMemAddr_of_gpr am 64 next rfl
  have ha : popMemAdjustedAddr (64 : Int).toNat am.baseUsesRsp (am.addr (beforeFetch s) next)
      64 = popMemAddr am 64 next t :=
    (popMemAdjustedAddr_eq_popMemAddr am hv 64 next (beforeFetch s)).trans
      (popMemAddr_of_gpr am 64 next (s := beforeFetch s) rfl).symm
  rw [pop_m_form (Or.inl rfl) _ t _ _ _ _ hctx.mode64 hosz haddr hlock _ _ _ _ _ _ hea hrip
    (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (popMemAddr am 64 next t))
    (by rw [← ha]; exact SegAccess.ctx hctx.seg am.isStack _) hd hss (hr.of_external_eq rfl)
    (hat ▸ hw.of_external_eq rfl)] at hdecode
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x8F _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem pop_m64_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x8F :: am.modrm 0 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hr : MemReadable s (stackPtr s) 8)
    (hw : MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (popMemAddr32 am 64
      (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) s)) 8) :
    let len := pre.length + 2 + am.tail.length
    X86.Machine.step s = some (.next (afterStep s len fun t =>
      popMemAtState t 64 (fun a => segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) ((a.setWidth 32).setWidth 64)) am (BitVec.add s.RIP (BitVec.ofNat 64 len)))) := by
  intro len
  have hlen' : (pre ++ 0x8F :: am.modrm 0 :: am.tail).length = len := by
    simp [len]; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x8F :: am.modrm 0 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_8F_pop_memory s h _ pre.length (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode
    hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h pre 0x8F 0 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = len + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (len + 1)
  let next := BitVec.add s.RIP (BitVec.ofNat 64 len)
  obtain ⟨hd, hss⟩ := call_start h (len + 1)
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s) next
  have hat : popMemAddr32 am 64 next t = popMemAddr32 am 64 next s := by
    simp only [popMemAddr32, popMemAddr_of_gpr am 64 next (s := s) (t := t) rfl]
  have ha : popMemAdjustedAddr (32 : Int).toNat am.baseUsesRsp (am.addr32 (beforeFetch s) next)
      64 = popMemAddr32 am 64 next t := by
    rw [show (32 : Int).toNat = 32 from rfl,
      popMemAdjustedAddr_eq_popMemAddr32 am hv 64 next (beforeFetch s)]
    simp only [popMemAddr32, popMemAddr_of_gpr am 64 next (s := beforeFetch s) (t := t) rfl]
  rw [pop_m_form (Or.inr rfl) _ t _ _ _ _ hctx.mode64 hosz haddr hlock _ _ _ _ _ _ hea hrip
    (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (popMemAddr32 am 64 next t))
    (by rw [← ha]; exact SegAccess.ctx hctx.seg am.isStack _) hd hss (hr.of_external_eq rfl)
    (hat ▸ hw.of_external_eq rfl)] at hdecode
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x8F _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem pop_m16_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw0 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x8F :: am.modrm 0 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hr : MemReadable s (stackPtr s) 2)
    (hw : MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (popMemAddr am 16
      (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) s)) 2) :
    let len := pre.length + 2 + am.tail.length
    X86.Machine.step s = some (.next (afterStep s len fun t =>
      popMemAtState t 16 (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)) am (BitVec.add s.RIP (BitVec.ofNat 64 len)))) := by
  intro len
  have hlen' : (pre ++ 0x8F :: am.modrm 0 :: am.tail).length = len := by
    simp [len]; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x8F :: am.modrm 0 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_8F_pop_memory s h _ pre.length (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode
    hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0x8F 0 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = len + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (len + 1)
  let next := BitVec.add s.RIP (BitVec.ofNat 64 len)
  obtain ⟨hd, hss⟩ := call_start h (len + 1)
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s) next
  have hat : popMemAddr am 16 next t = popMemAddr am 16 next s :=
    popMemAddr_of_gpr am 16 next rfl
  have ha : popMemAdjustedAddr (64 : Int).toNat am.baseUsesRsp (am.addr (beforeFetch s) next)
      16 = popMemAddr am 16 next t :=
    (popMemAdjustedAddr_eq_popMemAddr am hv 16 next (beforeFetch s)).trans
      (popMemAddr_of_gpr am 16 next (s := beforeFetch s) rfl).symm
  rw [pop_m16_form (Or.inl rfl) _ t _ _ _ _ hctx.mode64 hosz hw0 haddr hlock _ _ _ _ _ _ hea hrip
    (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (popMemAddr am 16 next t))
    (by rw [← ha]; exact SegAccess.ctx hctx.seg am.isStack _) hd hss (hr.of_external_eq rfl)
    (hat ▸ hw.of_external_eq rfl)] at hdecode
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x8F _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem pop_m16_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw0 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x8F :: am.modrm 0 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hr : MemReadable s (stackPtr s) 2)
    (hw : MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (popMemAddr32 am 16
      (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) s)) 2) :
    let len := pre.length + 2 + am.tail.length
    X86.Machine.step s = some (.next (afterStep s len fun t =>
      popMemAtState t 16 (fun a => segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) ((a.setWidth 32).setWidth 64)) am (BitVec.add s.RIP (BitVec.ofNat 64 len)))) := by
  intro len
  have hlen' : (pre ++ 0x8F :: am.modrm 0 :: am.tail).length = len := by
    simp [len]; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x8F :: am.modrm 0 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_8F_pop_memory s h _ pre.length (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode
    hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h pre 0x8F 0 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = len + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (len + 1)
  let next := BitVec.add s.RIP (BitVec.ofNat 64 len)
  obtain ⟨hd, hss⟩ := call_start h (len + 1)
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s) next
  have hat : popMemAddr32 am 16 next t = popMemAddr32 am 16 next s := by
    simp only [popMemAddr32, popMemAddr_of_gpr am 16 next (s := s) (t := t) rfl]
  have ha : popMemAdjustedAddr (32 : Int).toNat am.baseUsesRsp (am.addr32 (beforeFetch s) next)
      16 = popMemAddr32 am 16 next t := by
    rw [show (32 : Int).toNat = 32 from rfl,
      popMemAdjustedAddr_eq_popMemAddr32 am hv 16 next (beforeFetch s)]
    simp only [popMemAddr32, popMemAddr_of_gpr am 16 next (s := beforeFetch s) (t := t) rfl]
  rw [pop_m16_form (Or.inr rfl) _ t _ _ _ _ hctx.mode64 hosz hw0 haddr hlock _ _ _ _ _ _ hea hrip
    (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (popMemAddr32 am 16 next t))
    (by rw [← ha]; exact SegAccess.ctx hctx.seg am.isStack _) hd hss (hr.of_external_eq rfl)
    (hat ▸ hw.of_external_eq rfl)] at hdecode
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x8F _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

end X86Proofs
