import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Instructions.Mov.Generated.MR.Decode
import X86Proofs.Instructions.MovStore.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem mov_m_r_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x89 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hw : MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 2 + am.tail.length))) (n / 8)) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt s (pre.length + 2 + am.tail.length))
    let src : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem addr : Operand n) (movSpec (src.read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro ctx addr src
  have hlen' : (pre ++ 0x89 :: am.modrm reg :: am.tail).length =
      pre.length + 2 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0x89 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  have hdecode := decodeLegacy0_run_of_89_memory s h _ hrex2 (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) _ pre.length (by omega)
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hcode2 : BytesAt s s.RIP
      (pre ++ 0x89 :: am.modrm reg :: (am.tail ++ [])) := by
    simpa using hcode
  have hlow2 : s.RIP.toNat +
      (pre ++ 0x89 :: am.modrm reg :: (am.tail ++ [])).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hea := memAlu_ea_seg s h pre 0x89 reg am hv [] _ hctx hcode2 hlow2 (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  rw [mov_m_r_form _ _ _ _ _ _ _ n hn hsize haddr hlock _ _ _ _ _ hea hrip
    _ (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hmode _)
    (hw.of_external_eq rfl)] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x89 _ hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

theorem mov_m16_r16_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x89 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hw : MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 2 + am.tail.length))) 2) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt s (pre.length + 2 + am.tail.length))
    let src : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem addr : Operand 16) (movSpec (src.read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro ctx addr src
  have hlen' : (pre ++ 0x89 :: am.modrm reg :: am.tail).length =
      pre.length + 2 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0x89 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  have hdecode := decodeLegacy0_run_of_89_memory s h _ hrex2 (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) _ pre.length (by omega)
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hcode2 : BytesAt s s.RIP
      (pre ++ 0x89 :: am.modrm reg :: (am.tail ++ [])) := by
    simpa using hcode
  have hlow2 : s.RIP.toNat +
      (pre ++ 0x89 :: am.modrm reg :: (am.tail ++ [])).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hea := memAlu_ea_seg s h pre 0x89 reg am hv [] _ hctx hcode2 hlow2 (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  rw [mov_m16_r16_form _ _ _ _ _ _ _ hsize haddr hlock _ _ _ _ _ hea hrip
    _ (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hmode _)
    (hw.of_external_eq rfl)] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x89 _ hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

theorem mov_m_r_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x89 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hw : MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 2 + am.tail.length))) (n / 8)) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt32 s (pre.length + 2 + am.tail.length))
    let src : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem addr : Operand n) (movSpec (src.read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro ctx addr src
  have hlen' : (pre ++ 0x89 :: am.modrm reg :: am.tail).length =
      pre.length + 2 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0x89 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  have hdecode := decodeLegacy0_run_of_89_memory s h _ hrex2 (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) _ pre.length (by omega)
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hcode2 : BytesAt s s.RIP
      (pre ++ 0x89 :: am.modrm reg :: (am.tail ++ [])) := by
    simpa using hcode
  have hlow2 : s.RIP.toNat +
      (pre ++ 0x89 :: am.modrm reg :: (am.tail ++ [])).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hea := memAlu_ea32_seg s h pre 0x89 reg am hv [] _ hctx hcode2 hlow2 (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  rw [mov_m_r_form _ _ _ _ _ _ _ n hn hsize haddr hlock _ _ _ _ _ hea hrip
    _ (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hmode _)
    (hw.of_external_eq rfl)] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x89 _ hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

theorem mov_m16_r16_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x89 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hw : MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 2 + am.tail.length))) 2) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt32 s (pre.length + 2 + am.tail.length))
    let src : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem addr : Operand 16) (movSpec (src.read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro ctx addr src
  have hlen' : (pre ++ 0x89 :: am.modrm reg :: am.tail).length =
      pre.length + 2 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0x89 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  have hdecode := decodeLegacy0_run_of_89_memory s h _ hrex2 (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) _ pre.length (by omega)
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hcode2 : BytesAt s s.RIP
      (pre ++ 0x89 :: am.modrm reg :: (am.tail ++ [])) := by
    simpa using hcode
  have hlow2 : s.RIP.toNat +
      (pre ++ 0x89 :: am.modrm reg :: (am.tail ++ [])).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hea := memAlu_ea32_seg s h pre 0x89 reg am hv [] _ hctx hcode2 hlow2 (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  rw [mov_m16_r16_form _ _ _ _ _ _ _ hsize haddr hlock _ _ _ _ _ hea hrip
    _ (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hmode _)
    (hw.of_external_eq rfl)] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x89 _ hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

end X86Proofs
