import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Ror.Generated.M8Cl.Decode
import X86Proofs.Instructions.Ror.Generated.M8Cl.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem ror_m8_cl_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0xD2 :: am.modrm 1 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 2 + am.tail.length)))
      1) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 2 + am.tail.length))
    let c := shiftCount 8 ((Operand.reg 1 : Operand 8).read s)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeRmwOutputs t addr (rorSpec (StatusFlags.ofRFLAGS t.RFLAGS)
          (oracleBit (dataAccess t "load").oracle) c
          ((Operand.mem addr : Operand 8).read t))
        (rorOracleBits c)
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro addr c
  have hlen' : (pre ++ 0xD2 :: am.modrm 1 :: am.tail).length =
      pre.length + 2 + am.tail.length := by simp; omega
  have hlow' :
      s.RIP.toNat + (pre ++ 0xD2 :: am.modrm 1 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_D2_ror_memory s h _ pre.length (am.modrm 1)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _)
    hcode hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0xD2 1 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [ror_m8_cl_form _ _ _ _ _ _ haddr hlock _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem]
    at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xD2 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem ror_m8_cl_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0xD2 :: am.modrm 1 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 2 + am.tail.length)))
      1) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 2 + am.tail.length))
    let c := shiftCount 8 ((Operand.reg 1 : Operand 8).read s)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeRmwOutputs t addr (rorSpec (StatusFlags.ofRFLAGS t.RFLAGS)
          (oracleBit (dataAccess t "load").oracle) c
          ((Operand.mem addr : Operand 8).read t))
        (rorOracleBits c)
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro addr c
  have hlen' : (pre ++ 0xD2 :: am.modrm 1 :: am.tail).length =
      pre.length + 2 + am.tail.length := by simp; omega
  have hlow' :
      s.RIP.toNat + (pre ++ 0xD2 :: am.modrm 1 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_D2_ror_memory s h _ pre.length (am.modrm 1)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _)
    hcode hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h pre 0xD2 1 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  rw [ror_m8_cl_form _ _ _ _ _ _ haddr hlock _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem]
    at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xD2 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

end X86Proofs
