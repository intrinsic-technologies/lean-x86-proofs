import X86Proofs.Step.AfterStep
import X86Proofs.Step.FetchImm
import X86Proofs.Instructions.Imul.Generated.RMImm8.Decode
import X86Proofs.Instructions.Imul.Generated.RMImm8.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem imul_r_m_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am) (imm : BitVec 8)
    (hcode : BytesAt s s.RIP (pre ++ 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 3 + am.tail.length))) (n / 8)) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt s (pre.length + 3 + am.tail.length))
    let dst : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      let v := dataAccess t "load"
      writeOutputs v dst
        (imulSpec (fun i => oracleBit (oracleSkip v.oracle i)) ((Operand.mem addr : Operand n).read t) (imm.signExtend n)) 4
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro ctx addr dst
  have hlen' : (pre ++ 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)).length = pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  have hdecode := decodeLegacy0_run_of_6B_memory s h _ pre.length (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) hcode hlow'
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0x6B reg am hv (immBytes 8 imm) _ hctx hcode hlow'
    (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (pre ++ 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)) := hcode
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3 + am.tail.length)
    h.fetchReady hc hlow' 8 (by decide) imm (pre.length + 2 + am.tail.length)
    (getElem?_pre_imm pre 0x6B (am.modrm reg) am.tail imm) (by rw [hlen']; omega) (by omega)
  have hrip' : Handle_RIP_Relative_Address 64 am.isRip (am.offset (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) 1#64) =
        .ok (am.addrAt s (pre.length + 3 + am.tail.length)) := by
    rw [add_ofNat_add, show pre.length + 2 + am.tail.length + 1 = pre.length + 3 + am.tail.length by
      omega]
    exact hrip
  rw [imul_r_m_imm8_form _ _ _ _ _ _ _ _ n hn hsize haddr hlock _ _ _ _ _ _ hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hmode _) hread.low hread.mem, add_ofNat_add,
    show pre.length + 2 + am.tail.length + 1 = pre.length + 3 + am.tail.length by omega,
    show pre.length + 3 + am.tail.length + 8 / 8 = pre.length + 3 + am.tail.length + 1 by omega]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x6B _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode ((hmode (pre.length + 3 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

theorem imul_r_m_imm8_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am) (imm : BitVec 8)
    (hcode : BytesAt s s.RIP (pre ++ 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 3 + am.tail.length))) (n / 8)) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt32 s (pre.length + 3 + am.tail.length))
    let dst : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      let v := dataAccess t "load"
      writeOutputs v dst
        (imulSpec (fun i => oracleBit (oracleSkip v.oracle i)) ((Operand.mem addr : Operand n).read t) (imm.signExtend n)) 4
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro ctx addr dst
  have hlen' : (pre ++ 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)).length = pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  have hdecode := decodeLegacy0_run_of_6B_memory s h _ pre.length (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) hcode hlow'
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h pre 0x6B reg am hv (immBytes 8 imm) _ hctx hcode hlow'
    (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (pre ++ 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)) := hcode
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3 + am.tail.length)
    h.fetchReady hc hlow' 8 (by decide) imm (pre.length + 2 + am.tail.length)
    (getElem?_pre_imm pre 0x6B (am.modrm reg) am.tail imm) (by rw [hlen']; omega) (by omega)
  have hrip' : Handle_RIP_Relative_Address 32 am.isRip (am.offset32 (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) 1#64) =
        .ok (am.addrAt32 s (pre.length + 3 + am.tail.length)) := by
    rw [add_ofNat_add, show pre.length + 2 + am.tail.length + 1 = pre.length + 3 + am.tail.length by
      omega]
    exact hrip
  rw [imul_r_m_imm8_form _ _ _ _ _ _ _ _ n hn hsize haddr hlock _ _ _ _ _ _ hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hmode _) hread.low hread.mem, add_ofNat_add,
    show pre.length + 2 + am.tail.length + 1 = pre.length + 3 + am.tail.length by omega,
    show pre.length + 3 + am.tail.length + 8 / 8 = pre.length + 3 + am.tail.length + 1 by omega]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x6B _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode ((hmode (pre.length + 3 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

theorem imul_r16_m16_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am) (imm : BitVec 8)
    (hcode : BytesAt s s.RIP (pre ++ 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 3 + am.tail.length))) 2) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt s (pre.length + 3 + am.tail.length))
    let dst : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      let v := dataAccess t "load"
      writeOutputs v dst
        (imulSpec (fun i => oracleBit (oracleSkip v.oracle i)) ((Operand.mem addr : Operand 16).read t) (imm.signExtend 16)) 4
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro ctx addr dst
  have hlen' : (pre ++ 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)).length = pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  have hdecode := decodeLegacy0_run_of_6B_memory s h _ pre.length (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) hcode hlow'
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0x6B reg am hv (immBytes 8 imm) _ hctx hcode hlow'
    (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (pre ++ 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)) := hcode
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3 + am.tail.length)
    h.fetchReady hc hlow' 8 (by decide) imm (pre.length + 2 + am.tail.length)
    (getElem?_pre_imm pre 0x6B (am.modrm reg) am.tail imm) (by rw [hlen']; omega) (by omega)
  have hrip' : Handle_RIP_Relative_Address 64 am.isRip (am.offset (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) 1#64) =
        .ok (am.addrAt s (pre.length + 3 + am.tail.length)) := by
    rw [add_ofNat_add, show pre.length + 2 + am.tail.length + 1 = pre.length + 3 + am.tail.length by
      omega]
    exact hrip
  rw [imul_r16_m16_imm8_form _ _ _ _ _ _ _ _ hsize haddr hlock _ _ _ _ _ _ hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hmode _) hread.low hread.mem, add_ofNat_add,
    show pre.length + 2 + am.tail.length + 1 = pre.length + 3 + am.tail.length by omega,
    show pre.length + 3 + am.tail.length + 8 / 8 = pre.length + 3 + am.tail.length + 1 by omega]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x6B _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode ((hmode (pre.length + 3 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

theorem imul_r16_m16_imm8_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am) (imm : BitVec 8)
    (hcode : BytesAt s s.RIP (pre ++ 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 3 + am.tail.length))) 2) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt32 s (pre.length + 3 + am.tail.length))
    let dst : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      let v := dataAccess t "load"
      writeOutputs v dst
        (imulSpec (fun i => oracleBit (oracleSkip v.oracle i)) ((Operand.mem addr : Operand 16).read t) (imm.signExtend 16)) 4
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro ctx addr dst
  have hlen' : (pre ++ 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)).length = pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  have hdecode := decodeLegacy0_run_of_6B_memory s h _ pre.length (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) hcode hlow'
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h pre 0x6B reg am hv (immBytes 8 imm) _ hctx hcode hlow'
    (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (pre ++ 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)) := hcode
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3 + am.tail.length)
    h.fetchReady hc hlow' 8 (by decide) imm (pre.length + 2 + am.tail.length)
    (getElem?_pre_imm pre 0x6B (am.modrm reg) am.tail imm) (by rw [hlen']; omega) (by omega)
  have hrip' : Handle_RIP_Relative_Address 32 am.isRip (am.offset32 (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) 1#64) =
        .ok (am.addrAt32 s (pre.length + 3 + am.tail.length)) := by
    rw [add_ofNat_add, show pre.length + 2 + am.tail.length + 1 = pre.length + 3 + am.tail.length by
      omega]
    exact hrip
  rw [imul_r16_m16_imm8_form _ _ _ _ _ _ _ _ hsize haddr hlock _ _ _ _ _ _ hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hmode _) hread.low hread.mem, add_ofNat_add,
    show pre.length + 2 + am.tail.length + 1 = pre.length + 3 + am.tail.length by omega,
    show pre.length + 3 + am.tail.length + 8 / 8 = pre.length + 3 + am.tail.length + 1 by omega]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x6B _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode ((hmode (pre.length + 3 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

end X86Proofs
