import X86Proofs.Step.AfterStep
import X86Proofs.Step.FetchImm
import X86Proofs.Instructions.Bts.Generated.MImm8.Decode
import X86Proofs.Instructions.Bts.Generated.MImm8.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem bts_m_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 6) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (imm : BitVec 8)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)))
    (hlow : s.RIP.toNat + (pre.length + 4 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 4 + am.tail.length))) (n / 8)) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 4 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 4 + am.tail.length) fun t =>
      writeRmwOutputs t addr
        (btsSpec (fun i => oracleBit (oracleSkip (dataAccess t "load").oracle i))
          (StatusFlags.ofRFLAGS t.RFLAGS) ((Operand.mem addr : Operand n).read t) (imm.signExtend n)) 4
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4 + am.tail.length))))) := by
  intro addr
  have h5 := am.tail_length_le
  have hlen' : (pre ++ 0x0F :: 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)).length =
      pre.length + 4 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0x0F :: 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hcode2 : BytesAt s s.RIP
      ((pre ++ [0x0F]) ++ 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)) := by
    simpa using hcode
  have hlen2 : ((pre ++ [0x0F]) ++ 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)).length =
      pre.length + 4 + am.tail.length := by simp; omega
  have hlow2 : s.RIP.toNat +
      ((pre ++ [0x0F]) ++ 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)).length ≤ 2^32 := by
    rw [hlen2]; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy1_run_of_BA_r5_memory s h _ (pre.length + 1) (am.modrm 5)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode hlow'
    (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) (by omega) _ hrex2 hlock
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h (pre ++ [0x0F]) 0xBA 5 am hv (immBytes 8 imm) _ hctx hcode2 hlow2
    (by simp; omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      ((pre ++ [0x0F]) ++ 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)) := hcode2
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s)
    ((pre ++ [0x0F]).length + 3 + am.tail.length) h.fetchReady hc hlow2 8 (by decide) imm ((pre ++ [0x0F]).length + 2 + am.tail.length)
    (getElem?_pre_imm (pre ++ [0x0F]) 0xBA (am.modrm 5) am.tail imm) (by rw [hlen2]; simp; omega)
    (by simp; omega)
  simp only [show (pre ++ [(0x0F : UInt8)]).length = pre.length + 1 by simp] at hea hfetch
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  have hrip' : Handle_RIP_Relative_Address 64 am.isRip (am.offset (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1 + 2 + am.tail.length))) 1#64) =
        .ok (am.addrAt s (pre.length + 4 + am.tail.length)) := by
    rw [add_ofNat_add,
      show pre.length + 1 + 2 + am.tail.length + 1 = pre.length + 4 + am.tail.length by omega]
    exact hrip
  rw [bts_m_imm8_form _ _ _ _ _ _ _ n hn hsize haddr _ _ _ _ _ _ hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem, add_ofNat_add,
    show pre.length + 1 + 2 + am.tail.length + 1 = pre.length + 4 + am.tail.length by omega,
    show pre.length + 1 + 3 + am.tail.length + 8 / 8 = pre.length + 4 + am.tail.length + 1 by omega]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xBA _ hpre ⟨by decide, by decide⟩ (by omega) hcode hlow'
    hdecode ((hmode (pre.length + 4 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

theorem bts_m_imm8_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 6) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (imm : BitVec 8)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)))
    (hlow : s.RIP.toNat + (pre.length + 4 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 4 + am.tail.length))) (n / 8)) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 4 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 4 + am.tail.length) fun t =>
      writeRmwOutputs t addr
        (btsSpec (fun i => oracleBit (oracleSkip (dataAccess t "load").oracle i))
          (StatusFlags.ofRFLAGS t.RFLAGS) ((Operand.mem addr : Operand n).read t) (imm.signExtend n)) 4
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4 + am.tail.length))))) := by
  intro addr
  have h5 := am.tail_length_le
  have hlen' : (pre ++ 0x0F :: 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)).length =
      pre.length + 4 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0x0F :: 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hcode2 : BytesAt s s.RIP
      ((pre ++ [0x0F]) ++ 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)) := by
    simpa using hcode
  have hlen2 : ((pre ++ [0x0F]) ++ 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)).length =
      pre.length + 4 + am.tail.length := by simp; omega
  have hlow2 : s.RIP.toNat +
      ((pre ++ [0x0F]) ++ 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)).length ≤ 2^32 := by
    rw [hlen2]; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy1_run_of_BA_r5_memory s h _ (pre.length + 1) (am.modrm 5)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode hlow'
    (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) (by omega) _ hrex2 hlock
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h (pre ++ [0x0F]) 0xBA 5 am hv (immBytes 8 imm) _ hctx hcode2 hlow2
    (by simp; omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      ((pre ++ [0x0F]) ++ 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)) := hcode2
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s)
    ((pre ++ [0x0F]).length + 3 + am.tail.length) h.fetchReady hc hlow2 8 (by decide) imm ((pre ++ [0x0F]).length + 2 + am.tail.length)
    (getElem?_pre_imm (pre ++ [0x0F]) 0xBA (am.modrm 5) am.tail imm) (by rw [hlen2]; simp; omega)
    (by simp; omega)
  simp only [show (pre ++ [(0x0F : UInt8)]).length = pre.length + 1 by simp] at hea hfetch
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  have hrip' : Handle_RIP_Relative_Address 32 am.isRip (am.offset32 (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1 + 2 + am.tail.length))) 1#64) =
        .ok (am.addrAt32 s (pre.length + 4 + am.tail.length)) := by
    rw [add_ofNat_add,
      show pre.length + 1 + 2 + am.tail.length + 1 = pre.length + 4 + am.tail.length by omega]
    exact hrip
  rw [bts_m_imm8_form _ _ _ _ _ _ _ n hn hsize haddr _ _ _ _ _ _ hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem, add_ofNat_add,
    show pre.length + 1 + 2 + am.tail.length + 1 = pre.length + 4 + am.tail.length by omega,
    show pre.length + 1 + 3 + am.tail.length + 8 / 8 = pre.length + 4 + am.tail.length + 1 by omega]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xBA _ hpre ⟨by decide, by decide⟩ (by omega) hcode hlow'
    hdecode ((hmode (pre.length + 4 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

theorem bts_m16_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 6)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (imm : BitVec 8)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)))
    (hlow : s.RIP.toNat + (pre.length + 4 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 4 + am.tail.length))) 2) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 4 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 4 + am.tail.length) fun t =>
      writeRmwOutputs t addr
        (btsSpec (fun i => oracleBit (oracleSkip (dataAccess t "load").oracle i))
          (StatusFlags.ofRFLAGS t.RFLAGS) ((Operand.mem addr : Operand 16).read t) (imm.signExtend 16)) 4
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4 + am.tail.length))))) := by
  intro addr
  have h5 := am.tail_length_le
  have hlen' : (pre ++ 0x0F :: 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)).length =
      pre.length + 4 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0x0F :: 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hcode2 : BytesAt s s.RIP
      ((pre ++ [0x0F]) ++ 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)) := by
    simpa using hcode
  have hlen2 : ((pre ++ [0x0F]) ++ 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)).length =
      pre.length + 4 + am.tail.length := by simp; omega
  have hlow2 : s.RIP.toNat +
      ((pre ++ [0x0F]) ++ 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)).length ≤ 2^32 := by
    rw [hlen2]; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy1_run_of_BA_r5_memory s h _ (pre.length + 1) (am.modrm 5)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode hlow'
    (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) (by omega) _ hrex2 hlock
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h (pre ++ [0x0F]) 0xBA 5 am hv (immBytes 8 imm) _ hctx hcode2 hlow2
    (by simp; omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      ((pre ++ [0x0F]) ++ 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)) := hcode2
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s)
    ((pre ++ [0x0F]).length + 3 + am.tail.length) h.fetchReady hc hlow2 8 (by decide) imm ((pre ++ [0x0F]).length + 2 + am.tail.length)
    (getElem?_pre_imm (pre ++ [0x0F]) 0xBA (am.modrm 5) am.tail imm) (by rw [hlen2]; simp; omega)
    (by simp; omega)
  simp only [show (pre ++ [(0x0F : UInt8)]).length = pre.length + 1 by simp] at hea hfetch
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  have hrip' : Handle_RIP_Relative_Address 64 am.isRip (am.offset (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1 + 2 + am.tail.length))) 1#64) =
        .ok (am.addrAt s (pre.length + 4 + am.tail.length)) := by
    rw [add_ofNat_add,
      show pre.length + 1 + 2 + am.tail.length + 1 = pre.length + 4 + am.tail.length by omega]
    exact hrip
  rw [bts_m16_imm8_form _ _ _ _ _ _ _ hsize haddr _ _ _ _ _ _ hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem, add_ofNat_add,
    show pre.length + 1 + 2 + am.tail.length + 1 = pre.length + 4 + am.tail.length by omega,
    show pre.length + 1 + 3 + am.tail.length + 8 / 8 = pre.length + 4 + am.tail.length + 1 by omega]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xBA _ hpre ⟨by decide, by decide⟩ (by omega) hcode hlow'
    hdecode ((hmode (pre.length + 4 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

theorem bts_m16_imm8_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 6)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (imm : BitVec 8)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)))
    (hlow : s.RIP.toNat + (pre.length + 4 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 4 + am.tail.length))) 2) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 4 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 4 + am.tail.length) fun t =>
      writeRmwOutputs t addr
        (btsSpec (fun i => oracleBit (oracleSkip (dataAccess t "load").oracle i))
          (StatusFlags.ofRFLAGS t.RFLAGS) ((Operand.mem addr : Operand 16).read t) (imm.signExtend 16)) 4
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4 + am.tail.length))))) := by
  intro addr
  have h5 := am.tail_length_le
  have hlen' : (pre ++ 0x0F :: 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)).length =
      pre.length + 4 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0x0F :: 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hcode2 : BytesAt s s.RIP
      ((pre ++ [0x0F]) ++ 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)) := by
    simpa using hcode
  have hlen2 : ((pre ++ [0x0F]) ++ 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)).length =
      pre.length + 4 + am.tail.length := by simp; omega
  have hlow2 : s.RIP.toNat +
      ((pre ++ [0x0F]) ++ 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)).length ≤ 2^32 := by
    rw [hlen2]; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy1_run_of_BA_r5_memory s h _ (pre.length + 1) (am.modrm 5)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode hlow'
    (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) (by omega) _ hrex2 hlock
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h (pre ++ [0x0F]) 0xBA 5 am hv (immBytes 8 imm) _ hctx hcode2 hlow2
    (by simp; omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      ((pre ++ [0x0F]) ++ 0xBA :: am.modrm 5 :: (am.tail ++ immBytes 8 imm)) := hcode2
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s)
    ((pre ++ [0x0F]).length + 3 + am.tail.length) h.fetchReady hc hlow2 8 (by decide) imm ((pre ++ [0x0F]).length + 2 + am.tail.length)
    (getElem?_pre_imm (pre ++ [0x0F]) 0xBA (am.modrm 5) am.tail imm) (by rw [hlen2]; simp; omega)
    (by simp; omega)
  simp only [show (pre ++ [(0x0F : UInt8)]).length = pre.length + 1 by simp] at hea hfetch
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  have hrip' : Handle_RIP_Relative_Address 32 am.isRip (am.offset32 (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1 + 2 + am.tail.length))) 1#64) =
        .ok (am.addrAt32 s (pre.length + 4 + am.tail.length)) := by
    rw [add_ofNat_add,
      show pre.length + 1 + 2 + am.tail.length + 1 = pre.length + 4 + am.tail.length by omega]
    exact hrip
  rw [bts_m16_imm8_form _ _ _ _ _ _ _ hsize haddr _ _ _ _ _ _ hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem, add_ofNat_add,
    show pre.length + 1 + 2 + am.tail.length + 1 = pre.length + 4 + am.tail.length by omega,
    show pre.length + 1 + 3 + am.tail.length + 8 / 8 = pre.length + 4 + am.tail.length + 1 by omega]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xBA _ hpre ⟨by decide, by decide⟩ (by omega) hcode hlow'
    hdecode ((hmode (pre.length + 4 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

end X86Proofs
