import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Inc.Generated.MLock.Decode
import X86Proofs.Instructions.Inc.Generated.MLock.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem inc_lock_m_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = true)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0xFF :: am.modrm 0 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 2 + am.tail.length)))
      (n / 8))
    (hlk : LockReady s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 2 + am.tail.length)))
      (n / 8)) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 2 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeRmwOutputs t addr (incSpec (StatusFlags.ofRFLAGS t.RFLAGS)
          ((Operand.mem addr : Operand n).read t)) 0
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro addr
  have hlen' : (pre ++ 0xFF :: am.modrm 0 :: am.tail).length = pre.length + 2 + am.tail.length := by
    simp; omega
  have hlow' :
      s.RIP.toNat + (pre ++ 0xFF :: am.modrm 0 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_FF_inc_memory_lock s h _ pre.length (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _)
    hcode hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2 hlock
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0xFF 0 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [inc_lock_m_form _ _ _ _ _ _ n hn hsize haddr _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem
    (memAlu_lockReady hlk _)]
    at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xFF _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem inc_lock_m16_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = true)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0xFF :: am.modrm 0 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 2 + am.tail.length)))
      2)
    (hlk : LockReady s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 2 + am.tail.length)))
      2) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 2 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeRmwOutputs t addr (incSpec (StatusFlags.ofRFLAGS t.RFLAGS)
          ((Operand.mem addr : Operand 16).read t)) 0
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro addr
  have hlen' : (pre ++ 0xFF :: am.modrm 0 :: am.tail).length = pre.length + 2 + am.tail.length := by
    simp; omega
  have hlow' :
      s.RIP.toNat + (pre ++ 0xFF :: am.modrm 0 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_FF_inc_memory_lock s h _ pre.length (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _)
    hcode hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2 hlock
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0xFF 0 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [inc_lock_m16_form _ _ _ _ _ _ hsize haddr _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem
    (memAlu_lockReady hlk _)]
    at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xFF _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem inc_lock_m_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = true)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0xFF :: am.modrm 0 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 2 + am.tail.length)))
      (n / 8))
    (hlk : LockReady s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 2 + am.tail.length)))
      (n / 8)) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 2 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeRmwOutputs t addr (incSpec (StatusFlags.ofRFLAGS t.RFLAGS)
          ((Operand.mem addr : Operand n).read t)) 0
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro addr
  have hlen' : (pre ++ 0xFF :: am.modrm 0 :: am.tail).length = pre.length + 2 + am.tail.length := by
    simp; omega
  have hlow' :
      s.RIP.toNat + (pre ++ 0xFF :: am.modrm 0 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_FF_inc_memory_lock s h _ pre.length (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _)
    hcode hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2 hlock
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h pre 0xFF 0 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  rw [inc_lock_m_form _ _ _ _ _ _ n hn hsize haddr _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem
    (memAlu_lockReady hlk _)]
    at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xFF _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem inc_lock_m16_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = true)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0xFF :: am.modrm 0 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 2 + am.tail.length)))
      2)
    (hlk : LockReady s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 2 + am.tail.length)))
      2) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 2 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeRmwOutputs t addr (incSpec (StatusFlags.ofRFLAGS t.RFLAGS)
          ((Operand.mem addr : Operand 16).read t)) 0
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro addr
  have hlen' : (pre ++ 0xFF :: am.modrm 0 :: am.tail).length = pre.length + 2 + am.tail.length := by
    simp; omega
  have hlow' :
      s.RIP.toNat + (pre ++ 0xFF :: am.modrm 0 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_FF_inc_memory_lock s h _ pre.length (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _)
    hcode hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2 hlock
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h pre 0xFF 0 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  rw [inc_lock_m16_form _ _ _ _ _ _ hsize haddr _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem
    (memAlu_lockReady hlk _)]
    at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xFF _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

end X86Proofs
