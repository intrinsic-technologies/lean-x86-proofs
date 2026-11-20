import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Ror.Generated.M.Decode
import X86Proofs.Instructions.Ror.Generated.M.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem ror_m_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (imm : BitVec 8)
    (hcode : BytesAt s s.RIP (pre ++ 0xC1 :: am.modrm 1 :: (am.tail ++ immBytes 8 imm)))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 3 + am.tail.length)))
      (n / 8)) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 3 + am.tail.length))
    let c := shiftCount n imm
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeRmwOutputs t addr (rorSpec (StatusFlags.ofRFLAGS t.RFLAGS)
          (oracleBit (dataAccess t "load").oracle) c
          ((Operand.mem addr : Operand n).read t))
        (rorOracleBits c)
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro addr c
  have hlen' : (pre ++ 0xC1 :: am.modrm 1 :: (am.tail ++ immBytes 8 imm)).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' :
      s.RIP.toNat + (pre ++ 0xC1 :: am.modrm 1 :: (am.tail ++ immBytes 8 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_C1_ror_memory s h _ pre.length (am.modrm 1)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _)
    hcode hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0xC1 1 am hv (immBytes 8 imm) _ hctx hcode hlow' (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0xC1 :: am.modrm 1 :: (am.tail ++ immBytes 8 imm)) := hcode
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3 + am.tail.length)
    h.fetchReady hc hlow' 8 (by decide) imm (pre.length + 2 + am.tail.length)
    (getElem?_pre_imm pre 0xC1 (am.modrm 1) am.tail imm) (by rw [hlen']; omega) (by omega)
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  have hrip' : Handle_RIP_Relative_Address 64 am.isRip (am.offset (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) 1#64) =
        .ok (am.addrAt s (pre.length + 3 + am.tail.length)) := by
    rw [add_ofNat_add, show pre.length + 2 + am.tail.length + 1 = pre.length + 3 + am.tail.length by
      omega]
    exact hrip
  rw [ror_m_imm8_form _ _ _ _ _ _ _ n hn hsize haddr hlock _ _ _ _ _ _ hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem,
    add_ofNat_add,
    show pre.length + 2 + am.tail.length + 1 = pre.length + 3 + am.tail.length by omega,
    show pre.length + 3 + am.tail.length + 8 / 8 = pre.length + 3 + am.tail.length + 1 by omega]
    at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 3 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xC1 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem ror_m16_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (imm : BitVec 8)
    (hcode : BytesAt s s.RIP (pre ++ 0xC1 :: am.modrm 1 :: (am.tail ++ immBytes 8 imm)))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 3 + am.tail.length)))
      2) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 3 + am.tail.length))
    let c := shiftCount 16 imm
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeRmwOutputs t addr (rorSpec (StatusFlags.ofRFLAGS t.RFLAGS)
          (oracleBit (dataAccess t "load").oracle) c
          ((Operand.mem addr : Operand 16).read t))
        (rorOracleBits c)
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro addr c
  have hlen' : (pre ++ 0xC1 :: am.modrm 1 :: (am.tail ++ immBytes 8 imm)).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' :
      s.RIP.toNat + (pre ++ 0xC1 :: am.modrm 1 :: (am.tail ++ immBytes 8 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_C1_ror_memory s h _ pre.length (am.modrm 1)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _)
    hcode hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0xC1 1 am hv (immBytes 8 imm) _ hctx hcode hlow' (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0xC1 :: am.modrm 1 :: (am.tail ++ immBytes 8 imm)) := hcode
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3 + am.tail.length)
    h.fetchReady hc hlow' 8 (by decide) imm (pre.length + 2 + am.tail.length)
    (getElem?_pre_imm pre 0xC1 (am.modrm 1) am.tail imm) (by rw [hlen']; omega) (by omega)
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  have hrip' : Handle_RIP_Relative_Address 64 am.isRip (am.offset (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) 1#64) =
        .ok (am.addrAt s (pre.length + 3 + am.tail.length)) := by
    rw [add_ofNat_add, show pre.length + 2 + am.tail.length + 1 = pre.length + 3 + am.tail.length by
      omega]
    exact hrip
  rw [ror_m16_imm8_form _ _ _ _ _ _ _ hsize haddr hlock _ _ _ _ _ _ hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem,
    add_ofNat_add,
    show pre.length + 2 + am.tail.length + 1 = pre.length + 3 + am.tail.length by omega,
    show pre.length + 3 + am.tail.length + 8 / 8 = pre.length + 3 + am.tail.length + 1 by omega]
    at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 3 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xC1 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem ror_m_imm8_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (imm : BitVec 8)
    (hcode : BytesAt s s.RIP (pre ++ 0xC1 :: am.modrm 1 :: (am.tail ++ immBytes 8 imm)))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 3 + am.tail.length)))
      (n / 8)) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 3 + am.tail.length))
    let c := shiftCount n imm
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeRmwOutputs t addr (rorSpec (StatusFlags.ofRFLAGS t.RFLAGS)
          (oracleBit (dataAccess t "load").oracle) c
          ((Operand.mem addr : Operand n).read t))
        (rorOracleBits c)
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro addr c
  have hlen' : (pre ++ 0xC1 :: am.modrm 1 :: (am.tail ++ immBytes 8 imm)).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' :
      s.RIP.toNat + (pre ++ 0xC1 :: am.modrm 1 :: (am.tail ++ immBytes 8 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_C1_ror_memory s h _ pre.length (am.modrm 1)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _)
    hcode hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h pre 0xC1 1 am hv (immBytes 8 imm) _ hctx hcode hlow' (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0xC1 :: am.modrm 1 :: (am.tail ++ immBytes 8 imm)) := hcode
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3 + am.tail.length)
    h.fetchReady hc hlow' 8 (by decide) imm (pre.length + 2 + am.tail.length)
    (getElem?_pre_imm pre 0xC1 (am.modrm 1) am.tail imm) (by rw [hlen']; omega) (by omega)
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  have hrip' : Handle_RIP_Relative_Address 32 am.isRip (am.offset32 (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) 1#64) =
        .ok (am.addrAt32 s (pre.length + 3 + am.tail.length)) := by
    rw [add_ofNat_add, show pre.length + 2 + am.tail.length + 1 = pre.length + 3 + am.tail.length by
      omega]
    exact hrip
  rw [ror_m_imm8_form _ _ _ _ _ _ _ n hn hsize haddr hlock _ _ _ _ _ _ hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem,
    add_ofNat_add,
    show pre.length + 2 + am.tail.length + 1 = pre.length + 3 + am.tail.length by omega,
    show pre.length + 3 + am.tail.length + 8 / 8 = pre.length + 3 + am.tail.length + 1 by omega]
    at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 3 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xC1 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem ror_m16_imm8_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (imm : BitVec 8)
    (hcode : BytesAt s s.RIP (pre ++ 0xC1 :: am.modrm 1 :: (am.tail ++ immBytes 8 imm)))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 3 + am.tail.length)))
      2) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 3 + am.tail.length))
    let c := shiftCount 16 imm
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeRmwOutputs t addr (rorSpec (StatusFlags.ofRFLAGS t.RFLAGS)
          (oracleBit (dataAccess t "load").oracle) c
          ((Operand.mem addr : Operand 16).read t))
        (rorOracleBits c)
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro addr c
  have hlen' : (pre ++ 0xC1 :: am.modrm 1 :: (am.tail ++ immBytes 8 imm)).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' :
      s.RIP.toNat + (pre ++ 0xC1 :: am.modrm 1 :: (am.tail ++ immBytes 8 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_C1_ror_memory s h _ pre.length (am.modrm 1)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _)
    hcode hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h pre 0xC1 1 am hv (immBytes 8 imm) _ hctx hcode hlow' (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0xC1 :: am.modrm 1 :: (am.tail ++ immBytes 8 imm)) := hcode
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3 + am.tail.length)
    h.fetchReady hc hlow' 8 (by decide) imm (pre.length + 2 + am.tail.length)
    (getElem?_pre_imm pre 0xC1 (am.modrm 1) am.tail imm) (by rw [hlen']; omega) (by omega)
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  have hrip' : Handle_RIP_Relative_Address 32 am.isRip (am.offset32 (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) 1#64) =
        .ok (am.addrAt32 s (pre.length + 3 + am.tail.length)) := by
    rw [add_ofNat_add, show pre.length + 2 + am.tail.length + 1 = pre.length + 3 + am.tail.length by
      omega]
    exact hrip
  rw [ror_m16_imm8_form _ _ _ _ _ _ _ hsize haddr hlock _ _ _ _ _ _ hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem,
    add_ofNat_add,
    show pre.length + 2 + am.tail.length + 1 = pre.length + 3 + am.tail.length by omega,
    show pre.length + 3 + am.tail.length + 8 / 8 = pre.length + 3 + am.tail.length + 1 by omega]
    at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 3 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xC1 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem ror_m_one_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0xD1 :: am.modrm 1 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 2 + am.tail.length)))
      (n / 8)) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 2 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeRmwOutputs t addr (rorSpec (StatusFlags.ofRFLAGS t.RFLAGS)
          (oracleBit (dataAccess t "load").oracle) 1
          ((Operand.mem addr : Operand n).read t))
        (rorOracleBits 1)
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro addr
  have hlen' : (pre ++ 0xD1 :: am.modrm 1 :: am.tail).length =
      pre.length + 2 + am.tail.length := by simp; omega
  have hlow' :
      s.RIP.toNat + (pre ++ 0xD1 :: am.modrm 1 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_D1_ror_memory s h _ pre.length (am.modrm 1)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _)
    hcode hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0xD1 1 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [ror_m_one_form _ _ _ _ _ _ n hn hsize haddr hlock _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem]
    at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xD1 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem ror_m16_one_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0xD1 :: am.modrm 1 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 2 + am.tail.length)))
      2) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 2 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeRmwOutputs t addr (rorSpec (StatusFlags.ofRFLAGS t.RFLAGS)
          (oracleBit (dataAccess t "load").oracle) 1
          ((Operand.mem addr : Operand 16).read t))
        (rorOracleBits 1)
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro addr
  have hlen' : (pre ++ 0xD1 :: am.modrm 1 :: am.tail).length =
      pre.length + 2 + am.tail.length := by simp; omega
  have hlow' :
      s.RIP.toNat + (pre ++ 0xD1 :: am.modrm 1 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_D1_ror_memory s h _ pre.length (am.modrm 1)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _)
    hcode hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0xD1 1 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [ror_m16_one_form _ _ _ _ _ _ hsize haddr hlock _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem]
    at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xD1 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem ror_m_one_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0xD1 :: am.modrm 1 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 2 + am.tail.length)))
      (n / 8)) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 2 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeRmwOutputs t addr (rorSpec (StatusFlags.ofRFLAGS t.RFLAGS)
          (oracleBit (dataAccess t "load").oracle) 1
          ((Operand.mem addr : Operand n).read t))
        (rorOracleBits 1)
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro addr
  have hlen' : (pre ++ 0xD1 :: am.modrm 1 :: am.tail).length =
      pre.length + 2 + am.tail.length := by simp; omega
  have hlow' :
      s.RIP.toNat + (pre ++ 0xD1 :: am.modrm 1 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_D1_ror_memory s h _ pre.length (am.modrm 1)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _)
    hcode hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h pre 0xD1 1 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  rw [ror_m_one_form _ _ _ _ _ _ n hn hsize haddr hlock _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem]
    at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xD1 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem ror_m16_one_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0xD1 :: am.modrm 1 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 2 + am.tail.length)))
      2) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 2 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeRmwOutputs t addr (rorSpec (StatusFlags.ofRFLAGS t.RFLAGS)
          (oracleBit (dataAccess t "load").oracle) 1
          ((Operand.mem addr : Operand 16).read t))
        (rorOracleBits 1)
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro addr
  have hlen' : (pre ++ 0xD1 :: am.modrm 1 :: am.tail).length =
      pre.length + 2 + am.tail.length := by simp; omega
  have hlow' :
      s.RIP.toNat + (pre ++ 0xD1 :: am.modrm 1 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_D1_ror_memory s h _ pre.length (am.modrm 1)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _)
    hcode hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h pre 0xD1 1 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  rw [ror_m16_one_form _ _ _ _ _ _ hsize haddr hlock _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem]
    at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xD1 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

end X86Proofs
