import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Call.Step
import X86Proofs.Instructions.Push.Generated.M.Decode
import X86Proofs.Instructions.Push.Generated.M.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem push_m64_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0xFF :: am.modrm 6 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 2 + am.tail.length))) 8)
    (hw : MemWritable s (pushAddr s) 8) :
    let len := pre.length + 2 + am.tail.length
    X86.Machine.step s = some (.next (afterStep s len fun t =>
      pushState (callFrom true t (BitVec.add s.RIP (BitVec.ofNat 64 len)))
        ((Operand.mem (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s len)) : Operand 64).read s))) := by
  intro len
  have hlen' : (pre ++ 0xFF :: am.modrm 6 :: am.tail).length = len := by
    simp [len]; omega
  have hlow' : s.RIP.toNat + (pre ++ 0xFF :: am.modrm 6 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_FF_push_memory s h _ pre.length (am.modrm 6)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode
    hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0xFF 6 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = len + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (len + 1)
  obtain ⟨hd, hss⟩ := call_start h (len + 1)
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 len))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [push_m_form _ t _ _ _ _ hctx.mode64 hosz haddr hlock _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) hd hss (hread.of_external_eq rfl)
    (hw.of_external_eq rfl)] at hdecode
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xFF _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem push_m16_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw0 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0xFF :: am.modrm 6 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 2 + am.tail.length))) 2)
    (hw : MemWritable s (pushAddr16 s) 2) :
    let len := pre.length + 2 + am.tail.length
    X86.Machine.step s = some (.next (afterStep s len fun t =>
      pushState16 (callFrom true t (BitVec.add s.RIP (BitVec.ofNat 64 len)))
        ((Operand.mem (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s len)) : Operand 16).read s))) := by
  intro len
  have hlen' : (pre ++ 0xFF :: am.modrm 6 :: am.tail).length = len := by
    simp [len]; omega
  have hlow' : s.RIP.toNat + (pre ++ 0xFF :: am.modrm 6 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_FF_push_memory s h _ pre.length (am.modrm 6)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode
    hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0xFF 6 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = len + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (len + 1)
  obtain ⟨hd, hss⟩ := call_start h (len + 1)
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 len))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [push_m16_form _ t _ _ _ _ hctx.mode64 hosz hw0 haddr hlock _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) hd hss (hread.of_external_eq rfl)
    (hw.of_external_eq rfl)] at hdecode
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xFF _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem push_m64_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0xFF :: am.modrm 6 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 2 + am.tail.length))) 8)
    (hw : MemWritable s (pushAddr s) 8) :
    let len := pre.length + 2 + am.tail.length
    X86.Machine.step s = some (.next (afterStep s len fun t =>
      pushState (callFrom true t (BitVec.add s.RIP (BitVec.ofNat 64 len)))
        ((Operand.mem (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s len)) : Operand 64).read s))) := by
  intro len
  have hlen' : (pre ++ 0xFF :: am.modrm 6 :: am.tail).length = len := by
    simp [len]; omega
  have hlow' : s.RIP.toNat + (pre ++ 0xFF :: am.modrm 6 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_FF_push_memory s h _ pre.length (am.modrm 6)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode
    hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h pre 0xFF 6 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = len + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (len + 1)
  obtain ⟨hd, hss⟩ := call_start h (len + 1)
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 len))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  rw [push_m_form _ t _ _ _ _ hctx.mode64 hosz haddr hlock _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) hd hss (hread.of_external_eq rfl)
    (hw.of_external_eq rfl)] at hdecode
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xFF _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem push_m16_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw0 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0xFF :: am.modrm 6 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 2 + am.tail.length))) 2)
    (hw : MemWritable s (pushAddr16 s) 2) :
    let len := pre.length + 2 + am.tail.length
    X86.Machine.step s = some (.next (afterStep s len fun t =>
      pushState16 (callFrom true t (BitVec.add s.RIP (BitVec.ofNat 64 len)))
        ((Operand.mem (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s len)) : Operand 16).read s))) := by
  intro len
  have hlen' : (pre ++ 0xFF :: am.modrm 6 :: am.tail).length = len := by
    simp [len]; omega
  have hlow' : s.RIP.toNat + (pre ++ 0xFF :: am.modrm 6 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_FF_push_memory s h _ pre.length (am.modrm 6)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode
    hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h pre 0xFF 6 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = len + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (len + 1)
  obtain ⟨hd, hss⟩ := call_start h (len + 1)
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 len))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  rw [push_m16_form _ t _ _ _ _ hctx.mode64 hosz hw0 haddr hlock _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) hd hss (hread.of_external_eq rfl)
    (hw.of_external_eq rfl)] at hdecode
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xFF _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

end X86Proofs
