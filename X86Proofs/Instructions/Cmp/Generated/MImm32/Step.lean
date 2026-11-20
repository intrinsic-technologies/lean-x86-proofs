import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Cmp.Generated.MImm32.Decode
import X86Proofs.Instructions.Cmp.Generated.MImm32.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cmp_m_imm32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 4) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (imm : BitVec 32)
    (hcode : BytesAt s s.RIP (pre ++ 0x81 :: am.modrm 7 :: (am.tail ++ immBytes 32 imm)))
    (hlow : s.RIP.toNat + (pre.length + 6 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 6 + am.tail.length))) (n / 8)) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 6 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 6 + am.tail.length) fun t =>
      writeFlagsOutputs (dataAccess t "load")
        (cmpSpec
          ((Operand.mem addr : Operand n).read t) (imm.signExtend n)) 0
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 6 + am.tail.length))))) := by
  intro addr
  have hlen' : (pre ++ 0x81 :: am.modrm 7 :: (am.tail ++ immBytes 32 imm)).length =
      pre.length + 6 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x81 :: am.modrm 7 :: (am.tail ++ immBytes 32 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_81_r7_memory s h _ pre.length (am.modrm 7)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode hlow'
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0x81 7 am hv (immBytes 32 imm) _ hctx hcode hlow' (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0x81 :: am.modrm 7 :: (am.tail ++ immBytes 32 imm)) := hcode
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3 + am.tail.length)
    h.fetchReady hc hlow' 32 (by decide) imm (pre.length + 2 + am.tail.length)
    (getElem?_pre_imm pre 0x81 (am.modrm 7) am.tail imm) (by rw [hlen']; omega) (by omega)
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 6 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  have hrip' : Handle_RIP_Relative_Address 64 am.isRip (am.offset (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) 4#64) =
        .ok (am.addrAt s (pre.length + 6 + am.tail.length)) := by
    rw [add_ofNat_add, show pre.length + 2 + am.tail.length + 4 = pre.length + 6 + am.tail.length by
      omega]
    exact hrip
  rw [cmp_m_imm32_form _ _ _ _ _ _ _ n hn hsize haddr hlock _ _ _ _ _ _ hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem,
    add_ofNat_add,
    show pre.length + 2 + am.tail.length + 4 = pre.length + 6 + am.tail.length by omega,
    show pre.length + 3 + am.tail.length + 32 / 8 = pre.length + 6 + am.tail.length + 1 by omega]
    at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 6 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x81 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem cmp_m_imm32_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 4) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (imm : BitVec 32)
    (hcode : BytesAt s s.RIP (pre ++ 0x81 :: am.modrm 7 :: (am.tail ++ immBytes 32 imm)))
    (hlow : s.RIP.toNat + (pre.length + 6 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 6 + am.tail.length))) (n / 8)) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 6 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 6 + am.tail.length) fun t =>
      writeFlagsOutputs (dataAccess t "load")
        (cmpSpec
          ((Operand.mem addr : Operand n).read t) (imm.signExtend n)) 0
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 6 + am.tail.length))))) := by
  intro addr
  have hlen' : (pre ++ 0x81 :: am.modrm 7 :: (am.tail ++ immBytes 32 imm)).length =
      pre.length + 6 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x81 :: am.modrm 7 :: (am.tail ++ immBytes 32 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_81_r7_memory s h _ pre.length (am.modrm 7)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode hlow'
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h pre 0x81 7 am hv (immBytes 32 imm) _ hctx hcode hlow' (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0x81 :: am.modrm 7 :: (am.tail ++ immBytes 32 imm)) := hcode
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3 + am.tail.length)
    h.fetchReady hc hlow' 32 (by decide) imm (pre.length + 2 + am.tail.length)
    (getElem?_pre_imm pre 0x81 (am.modrm 7) am.tail imm) (by rw [hlen']; omega) (by omega)
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 6 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  have hrip' : Handle_RIP_Relative_Address 32 am.isRip (am.offset32 (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) 4#64) =
        .ok (am.addrAt32 s (pre.length + 6 + am.tail.length)) := by
    rw [add_ofNat_add, show pre.length + 2 + am.tail.length + 4 = pre.length + 6 + am.tail.length by
      omega]
    exact hrip
  rw [cmp_m_imm32_form _ _ _ _ _ _ _ n hn hsize haddr hlock _ _ _ _ _ _ hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem,
    add_ofNat_add,
    show pre.length + 2 + am.tail.length + 4 = pre.length + 6 + am.tail.length by omega,
    show pre.length + 3 + am.tail.length + 32 / 8 = pre.length + 6 + am.tail.length + 1 by omega]
    at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 6 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x81 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem cmp_m16_imm16_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 6)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (imm : BitVec 16)
    (hcode : BytesAt s s.RIP (pre ++ 0x81 :: am.modrm 7 :: (am.tail ++ immBytes 16 imm)))
    (hlow : s.RIP.toNat + (pre.length + 4 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 4 + am.tail.length))) 2) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 4 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 4 + am.tail.length) fun t =>
      writeFlagsOutputs (dataAccess t "load")
        (cmpSpec
          ((Operand.mem addr : Operand 16).read t) (imm.signExtend 16)) 0
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4 + am.tail.length))))) := by
  intro addr
  have hlen' : (pre ++ 0x81 :: am.modrm 7 :: (am.tail ++ immBytes 16 imm)).length =
      pre.length + 4 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x81 :: am.modrm 7 :: (am.tail ++ immBytes 16 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_81_r7_memory s h _ pre.length (am.modrm 7)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode hlow'
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0x81 7 am hv (immBytes 16 imm) _ hctx hcode hlow' (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0x81 :: am.modrm 7 :: (am.tail ++ immBytes 16 imm)) := hcode
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3 + am.tail.length)
    h.fetchReady hc hlow' 16 (by decide) imm (pre.length + 2 + am.tail.length)
    (getElem?_pre_imm pre 0x81 (am.modrm 7) am.tail imm) (by rw [hlen']; omega) (by omega)
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  have hrip' : Handle_RIP_Relative_Address 64 am.isRip (am.offset (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) 2#64) =
        .ok (am.addrAt s (pre.length + 4 + am.tail.length)) := by
    rw [add_ofNat_add, show pre.length + 2 + am.tail.length + 2 = pre.length + 4 + am.tail.length by
      omega]
    exact hrip
  rw [cmp_m16_imm16_form _ _ _ _ _ _ _ hsize haddr hlock _ _ _ _ _ _ hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem,
    add_ofNat_add,
    show pre.length + 2 + am.tail.length + 2 = pre.length + 4 + am.tail.length by omega,
    show pre.length + 3 + am.tail.length + 16 / 8 = pre.length + 4 + am.tail.length + 1 by omega]
    at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 4 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x81 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem cmp_m16_imm16_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 6)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (imm : BitVec 16)
    (hcode : BytesAt s s.RIP (pre ++ 0x81 :: am.modrm 7 :: (am.tail ++ immBytes 16 imm)))
    (hlow : s.RIP.toNat + (pre.length + 4 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 4 + am.tail.length))) 2) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 4 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 4 + am.tail.length) fun t =>
      writeFlagsOutputs (dataAccess t "load")
        (cmpSpec
          ((Operand.mem addr : Operand 16).read t) (imm.signExtend 16)) 0
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4 + am.tail.length))))) := by
  intro addr
  have hlen' : (pre ++ 0x81 :: am.modrm 7 :: (am.tail ++ immBytes 16 imm)).length =
      pre.length + 4 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x81 :: am.modrm 7 :: (am.tail ++ immBytes 16 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_81_r7_memory s h _ pre.length (am.modrm 7)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode hlow'
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h pre 0x81 7 am hv (immBytes 16 imm) _ hctx hcode hlow' (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0x81 :: am.modrm 7 :: (am.tail ++ immBytes 16 imm)) := hcode
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3 + am.tail.length)
    h.fetchReady hc hlow' 16 (by decide) imm (pre.length + 2 + am.tail.length)
    (getElem?_pre_imm pre 0x81 (am.modrm 7) am.tail imm) (by rw [hlen']; omega) (by omega)
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  have hrip' : Handle_RIP_Relative_Address 32 am.isRip (am.offset32 (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) 2#64) =
        .ok (am.addrAt32 s (pre.length + 4 + am.tail.length)) := by
    rw [add_ofNat_add, show pre.length + 2 + am.tail.length + 2 = pre.length + 4 + am.tail.length by
      omega]
    exact hrip
  rw [cmp_m16_imm16_form _ _ _ _ _ _ _ hsize haddr hlock _ _ _ _ _ _ hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem,
    add_ofNat_add,
    show pre.length + 2 + am.tail.length + 2 = pre.length + 4 + am.tail.length by omega,
    show pre.length + 3 + am.tail.length + 16 / 8 = pre.length + 4 + am.tail.length + 1 by omega]
    at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 4 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x81 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

end X86Proofs
