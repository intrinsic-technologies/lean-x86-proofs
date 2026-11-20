import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Sbb.Generated.M8R8.Decode
import X86Proofs.Instructions.Sbb.Generated.M8R8.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem sbb_m8_r8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3)
    (hreg : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_prefix_present = true ∨
      (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r4 (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r3
        reg).toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x18 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt s (pre.length + 2 + am.tail.length))) 1) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt s (pre.length + 2 + am.tail.length))
    let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeRmwOutputs t addr (sbbSpec (StatusFlags.ofRFLAGS t.RFLAGS).CF
          ((Operand.mem addr : Operand 8).read t) (src.read t)) 0
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro ctx addr src
  have hlen' : (pre ++ 0x18 :: am.modrm reg :: am.tail).length =
      pre.length + 2 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x18 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_18_memory s h _ pre.length (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) hcode hlow' (getElem?_pre_op _ _ _ _)
    (getElem?_pre_modrm _ _ _ _) (by omega) ctx hrex2 hlock
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0x18 reg am hv [] ctx hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [sbb_m8_r8_form _ t _ _ _ _ _ haddr hreg _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hmode hread.low hread.mem]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x18 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem sbb_m8_r8_gpr8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x18 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt s (pre.length + 2 + am.tail.length))) 1) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt s (pre.length + 2 + am.tail.length))
    let src : Operand 8 := .gpr8 (gprNumber ctx.rex_r4 ctx.rex_r3 reg) (byteRex ctx)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeRmwOutputs t addr (sbbSpec (StatusFlags.ofRFLAGS t.RFLAGS).CF
          ((Operand.mem addr : Operand 8).read t) (src.read t)) 0
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro ctx addr src
  have hlen' : (pre ++ 0x18 :: am.modrm reg :: am.tail).length =
      pre.length + 2 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x18 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_18_memory s h _ pre.length (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) hcode hlow' (getElem?_pre_op _ _ _ _)
    (getElem?_pre_modrm _ _ _ _) (by omega) ctx hrex2 hlock
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0x18 reg am hv [] ctx hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [sbb_m8_r8_gpr8_form _ t _ _ _ _ _ haddr _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hmode hread.low hread.mem]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x18 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem sbb_m8_r8_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3)
    (hreg : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_prefix_present = true ∨
      (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r4 (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r3
        reg).toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x18 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt32 s (pre.length + 2 + am.tail.length))) 1) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt32 s (pre.length + 2 + am.tail.length))
    let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeRmwOutputs t addr (sbbSpec (StatusFlags.ofRFLAGS t.RFLAGS).CF
          ((Operand.mem addr : Operand 8).read t) (src.read t)) 0
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro ctx addr src
  have hlen' : (pre ++ 0x18 :: am.modrm reg :: am.tail).length =
      pre.length + 2 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x18 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_18_memory s h _ pre.length (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) hcode hlow' (getElem?_pre_op _ _ _ _)
    (getElem?_pre_modrm _ _ _ _) (by omega) ctx hrex2 hlock
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h pre 0x18 reg am hv [] ctx hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  rw [sbb_m8_r8_form _ t _ _ _ _ _ haddr hreg _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hmode hread.low hread.mem]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x18 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem sbb_m8_r8_gpr8_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x18 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt32 s (pre.length + 2 + am.tail.length))) 1) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt32 s (pre.length + 2 + am.tail.length))
    let src : Operand 8 := .gpr8 (gprNumber ctx.rex_r4 ctx.rex_r3 reg) (byteRex ctx)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeRmwOutputs t addr (sbbSpec (StatusFlags.ofRFLAGS t.RFLAGS).CF
          ((Operand.mem addr : Operand 8).read t) (src.read t)) 0
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro ctx addr src
  have hlen' : (pre ++ 0x18 :: am.modrm reg :: am.tail).length =
      pre.length + 2 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x18 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_18_memory s h _ pre.length (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) hcode hlow' (getElem?_pre_op _ _ _ _)
    (getElem?_pre_modrm _ _ _ _) (by omega) ctx hrex2 hlock
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h pre 0x18 reg am hv [] ctx hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  rw [sbb_m8_r8_gpr8_form _ t _ _ _ _ _ haddr _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hmode hread.low hread.mem]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x18 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

end X86Proofs
