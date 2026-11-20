import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Btc.Generated.MRLock.Decode
import X86Proofs.Instructions.Btc.Generated.MRLock.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem btc_lock_m_r_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = true)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0xBB :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt s (pre.length + 3 + am.tail.length) + bitStringOffset
        ((Operand.reg (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r4
          (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r3 reg) : Operand n).read s))) (n / 8))
    (hlk : LockReady s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt s (pre.length + 3 + am.tail.length) + bitStringOffset
        ((Operand.reg (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r4
          (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r3 reg) : Operand n).read s))) (n / 8)) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let src : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    let addr := segAddr ctx (am.addrAt s (pre.length + 3 + am.tail.length) + bitStringOffset (src.read s))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeRmwOutputs t addr
        (btcSpec (fun i => oracleBit (oracleSkip (dataAccess t "load").oracle i))
          (StatusFlags.ofRFLAGS t.RFLAGS) ((Operand.mem addr : Operand n).read t) (src.read t)) 4
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro ctx src addr
  have hlen' : (pre ++ 0x0F :: 0xBB :: am.modrm reg :: am.tail).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x0F :: 0xBB :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy1_run_of_BB_memory_lock s h _ hrex2 hlock (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) _ (pre.length + 1) (by omega)
    (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hcode2 : BytesAt s s.RIP
      ((pre ++ [(0x0F : UInt8)]) ++ 0xBB :: am.modrm reg :: (am.tail ++ [])) := by
    simpa using hcode
  have hlow2 : s.RIP.toNat +
      ((pre ++ [(0x0F : UInt8)]) ++ 0xBB :: am.modrm reg :: (am.tail ++ [])).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hea := memAlu_ea_seg s h (pre ++ [0x0F]) 0xBB reg am hv [] _ hctx hcode2 hlow2
    (by simp; omega)
  rw [show (pre ++ [(0x0F : UInt8)]).length = pre.length + 1 by simp,
    show pre.length + 1 + 2 + am.tail.length = pre.length + 3 + am.tail.length by omega,
    show pre.length + 1 + 3 + am.tail.length = pre.length + 3 + am.tail.length + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (pre.length + 3 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode_add_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))) (bitStringOffset (src.read t))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [btc_lock_m_r_form _ t _ _ _ _ _ n hn hsize haddr _ _ _ _ _ hea hrip
    _ (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hmode hread.low
    hread.mem (memAlu_lockReady hlk _)]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xBB _ hpre ⟨by decide, by decide⟩ (by omega) hcode hlow'
    hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem btc_lock_m_r_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = true)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0xBB :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (((am.addrAt s (pre.length + 3 + am.tail.length) + bitStringOffset
        ((Operand.reg (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r4
          (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r3 reg) : Operand n).read s)).setWidth 32).setWidth 64)) (n / 8))
    (hlk : LockReady s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (((am.addrAt s (pre.length + 3 + am.tail.length) + bitStringOffset
        ((Operand.reg (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r4
          (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r3 reg) : Operand n).read s)).setWidth 32).setWidth 64)) (n / 8)) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let src : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    let addr := segAddr ctx (((am.addrAt s (pre.length + 3 + am.tail.length) + bitStringOffset (src.read s)).setWidth 32).setWidth 64)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeRmwOutputs t addr
        (btcSpec (fun i => oracleBit (oracleSkip (dataAccess t "load").oracle i))
          (StatusFlags.ofRFLAGS t.RFLAGS) ((Operand.mem addr : Operand n).read t) (src.read t)) 4
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro ctx src addr
  have hlen' : (pre ++ 0x0F :: 0xBB :: am.modrm reg :: am.tail).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x0F :: 0xBB :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy1_run_of_BB_memory_lock s h _ hrex2 hlock (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) _ (pre.length + 1) (by omega)
    (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hcode2 : BytesAt s s.RIP
      ((pre ++ [(0x0F : UInt8)]) ++ 0xBB :: am.modrm reg :: (am.tail ++ [])) := by
    simpa using hcode
  have hlow2 : s.RIP.toNat +
      ((pre ++ [(0x0F : UInt8)]) ++ 0xBB :: am.modrm reg :: (am.tail ++ [])).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hea := memAlu_ea32_seg s h (pre ++ [0x0F]) 0xBB reg am hv [] _ hctx hcode2 hlow2
    (by simp; omega)
  rw [show (pre ++ [(0x0F : UInt8)]).length = pre.length + 1 by simp,
    show pre.length + 1 + 2 + am.tail.length = pre.length + 3 + am.tail.length by omega,
    show pre.length + 1 + 3 + am.tail.length = pre.length + 3 + am.tail.length + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (pre.length + 3 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode32_add_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))) (bitStringOffset (src.read t))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [btc_lock_m_r_form _ t _ _ _ _ _ n hn hsize haddr _ _ _ _ _ hea hrip
    _ (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hmode hread.low
    hread.mem (memAlu_lockReady hlk _)]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xBB _ hpre ⟨by decide, by decide⟩ (by omega) hcode hlow'
    hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem btc_lock_m16_r16_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = true)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0xBB :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt s (pre.length + 3 + am.tail.length) + bitStringOffset
        ((Operand.reg (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r4
          (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r3 reg) : Operand 16).read s))) 2)
    (hlk : LockReady s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt s (pre.length + 3 + am.tail.length) + bitStringOffset
        ((Operand.reg (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r4
          (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r3 reg) : Operand 16).read s))) 2) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let src : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    let addr := segAddr ctx (am.addrAt s (pre.length + 3 + am.tail.length) + bitStringOffset (src.read s))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeRmwOutputs t addr
        (btcSpec (fun i => oracleBit (oracleSkip (dataAccess t "load").oracle i))
          (StatusFlags.ofRFLAGS t.RFLAGS) ((Operand.mem addr : Operand 16).read t) (src.read t)) 4
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro ctx src addr
  have hlen' : (pre ++ 0x0F :: 0xBB :: am.modrm reg :: am.tail).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x0F :: 0xBB :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy1_run_of_BB_memory_lock s h _ hrex2 hlock (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) _ (pre.length + 1) (by omega)
    (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hcode2 : BytesAt s s.RIP
      ((pre ++ [(0x0F : UInt8)]) ++ 0xBB :: am.modrm reg :: (am.tail ++ [])) := by
    simpa using hcode
  have hlow2 : s.RIP.toNat +
      ((pre ++ [(0x0F : UInt8)]) ++ 0xBB :: am.modrm reg :: (am.tail ++ [])).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hea := memAlu_ea_seg s h (pre ++ [0x0F]) 0xBB reg am hv [] _ hctx hcode2 hlow2
    (by simp; omega)
  rw [show (pre ++ [(0x0F : UInt8)]).length = pre.length + 1 by simp,
    show pre.length + 1 + 2 + am.tail.length = pre.length + 3 + am.tail.length by omega,
    show pre.length + 1 + 3 + am.tail.length = pre.length + 3 + am.tail.length + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (pre.length + 3 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode_add_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))) (bitStringOffset (src.read t))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [btc_lock_m16_r16_form _ t _ _ _ _ _ hsize haddr _ _ _ _ _ hea hrip
    _ (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hmode hread.low
    hread.mem (memAlu_lockReady hlk _)]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xBB _ hpre ⟨by decide, by decide⟩ (by omega) hcode hlow'
    hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem btc_lock_m16_r16_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = true)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0xBB :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (((am.addrAt s (pre.length + 3 + am.tail.length) + bitStringOffset
        ((Operand.reg (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r4
          (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r3 reg) : Operand 16).read s)).setWidth 32).setWidth 64)) 2)
    (hlk : LockReady s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (((am.addrAt s (pre.length + 3 + am.tail.length) + bitStringOffset
        ((Operand.reg (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r4
          (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r3 reg) : Operand 16).read s)).setWidth 32).setWidth 64)) 2) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let src : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    let addr := segAddr ctx (((am.addrAt s (pre.length + 3 + am.tail.length) + bitStringOffset (src.read s)).setWidth 32).setWidth 64)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeRmwOutputs t addr
        (btcSpec (fun i => oracleBit (oracleSkip (dataAccess t "load").oracle i))
          (StatusFlags.ofRFLAGS t.RFLAGS) ((Operand.mem addr : Operand 16).read t) (src.read t)) 4
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro ctx src addr
  have hlen' : (pre ++ 0x0F :: 0xBB :: am.modrm reg :: am.tail).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x0F :: 0xBB :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy1_run_of_BB_memory_lock s h _ hrex2 hlock (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) _ (pre.length + 1) (by omega)
    (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hcode2 : BytesAt s s.RIP
      ((pre ++ [(0x0F : UInt8)]) ++ 0xBB :: am.modrm reg :: (am.tail ++ [])) := by
    simpa using hcode
  have hlow2 : s.RIP.toNat +
      ((pre ++ [(0x0F : UInt8)]) ++ 0xBB :: am.modrm reg :: (am.tail ++ [])).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hea := memAlu_ea32_seg s h (pre ++ [0x0F]) 0xBB reg am hv [] _ hctx hcode2 hlow2
    (by simp; omega)
  rw [show (pre ++ [(0x0F : UInt8)]).length = pre.length + 1 by simp,
    show pre.length + 1 + 2 + am.tail.length = pre.length + 3 + am.tail.length by omega,
    show pre.length + 1 + 3 + am.tail.length = pre.length + 3 + am.tail.length + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (pre.length + 3 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode32_add_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))) (bitStringOffset (src.read t))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [btc_lock_m16_r16_form _ t _ _ _ _ _ hsize haddr _ _ _ _ _ hea hrip
    _ (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hmode hread.low
    hread.mem (memAlu_lockReady hlk _)]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xBB _ hpre ⟨by decide, by decide⟩ (by omega) hcode hlow'
    hdecode (hmode.of_cs_lma_eq rfl rfl)

end X86Proofs
