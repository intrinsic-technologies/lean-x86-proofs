import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.Sse
import X86Proofs.Instructions.Movlpd.Generated.MX.Decode
import X86Proofs.Instructions.Movlpd.Generated.MX.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem movlpd_m64_xmm_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hfeat : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0x13 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hmw : MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 3 + am.tail.length)))
      8) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt s (pre.length + 3 + am.tail.length))
    let src : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem addr : Operand 64)
        (movlpStoreSpec (src.read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro ctx addr src
  have hlen' : (pre ++ 0x0F :: 0x13 :: am.modrm reg :: am.tail).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0x0F :: 0x13 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hsse' (k : Nat) : Prelude.SupportedSSE Bindings.processor (afterFetches (beforeFetch s) k) :=
    SupportedSSE.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      hsse
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  have hdecode := decodeLegacy1_run_of_13_66_memory s h hfeat _ (pre.length + 1) (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) hcode hlow'
    (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) (by omega) _ hrex2 hosz
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hcode2 : BytesAt s s.RIP
      ((pre ++ [(0x0F : UInt8)]) ++ 0x13 :: am.modrm reg :: (am.tail ++ [])) := by
    simpa using hcode
  have hlow2 : s.RIP.toNat +
      ((pre ++ [(0x0F : UInt8)]) ++ 0x13 :: am.modrm reg :: (am.tail ++ [])).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hea := memAlu_ea_seg s h (pre ++ [0x0F]) 0x13 reg am hv [] _ hctx hcode2 hlow2
    (by simp; omega)
  rw [show (pre ++ [(0x0F : UInt8)]).length = pre.length + 1 by simp,
    show pre.length + 1 + 2 + am.tail.length = pre.length + 3 + am.tail.length by omega,
    show pre.length + 1 + 3 + am.tail.length = pre.length + 3 + am.tail.length + 1 by omega] at hea
  rw [movlpd_m64_xmm_form _ _ _ _ _ _ _ haddr hrep hlock _ _ _ _ _ hea hrip
    _ (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hmode _) (hsse' _) (hmw.of_external_eq rfl)]
    at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0x13 _ hpre ⟨by decide, by decide⟩ (by omega) hcode
    hlow' hdecode ((hmode (pre.length + 3 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

theorem movlpd_m64_xmm_a32_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hfeat : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0x13 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hmw : MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 3 + am.tail.length)))
      8) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt32 s (pre.length + 3 + am.tail.length))
    let src : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem addr : Operand 64)
        (movlpStoreSpec (src.read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro ctx addr src
  have hlen' : (pre ++ 0x0F :: 0x13 :: am.modrm reg :: am.tail).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0x0F :: 0x13 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hsse' (k : Nat) : Prelude.SupportedSSE Bindings.processor (afterFetches (beforeFetch s) k) :=
    SupportedSSE.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      hsse
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  have hdecode := decodeLegacy1_run_of_13_66_memory s h hfeat _ (pre.length + 1) (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) hcode hlow'
    (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) (by omega) _ hrex2 hosz
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hcode2 : BytesAt s s.RIP
      ((pre ++ [(0x0F : UInt8)]) ++ 0x13 :: am.modrm reg :: (am.tail ++ [])) := by
    simpa using hcode
  have hlow2 : s.RIP.toNat +
      ((pre ++ [(0x0F : UInt8)]) ++ 0x13 :: am.modrm reg :: (am.tail ++ [])).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hea := memAlu_ea32_seg s h (pre ++ [0x0F]) 0x13 reg am hv [] _ hctx hcode2 hlow2
    (by simp; omega)
  rw [show (pre ++ [(0x0F : UInt8)]).length = pre.length + 1 by simp,
    show pre.length + 1 + 2 + am.tail.length = pre.length + 3 + am.tail.length by omega,
    show pre.length + 1 + 3 + am.tail.length = pre.length + 3 + am.tail.length + 1 by omega] at hea
  rw [movlpd_m64_xmm_form _ _ _ _ _ _ _ haddr hrep hlock _ _ _ _ _ hea hrip
    _ (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hmode _) (hsse' _) (hmw.of_external_eq rfl)]
    at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0x13 _ hpre ⟨by decide, by decide⟩ (by omega) hcode
    hlow' hdecode ((hmode (pre.length + 3 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

end X86Proofs
