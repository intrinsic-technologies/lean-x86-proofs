import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.Float
import X86Proofs.Instructions.Divss.Generated.XM.Decode
import X86Proofs.Instructions.Divss.Generated.XM.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem divss_xmm_m32_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hfeat : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE_Encoding true)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hvex : (scanContext s.DS (PrefixSegments.ofState s) pre).vex_prefix_present = false)
    (hevex : (scanContext s.DS (PrefixSegments.ofState s) pre).evex_prefix_present = false)
    (hevexb : (scanContext s.DS (PrefixSegments.ofState s) pre).evex_b = 0)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0x5E :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 3 + am.tail.length)))
      4)
    (hm : MxcsrPre s)
    (hok : divsOk 32 s.MXCSR
      ((Operand.xmm (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r4 (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r3 reg) : Operand 128).read s)
      ((Operand.mem (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 3 + am.tail.length))) : Operand 32).read s)) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt s (pre.length + 3 + am.tail.length))
    let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeResult ((Operand.mxcsr : Operand 32).write (dataAccess t "load")
          (mxOr t.MXCSR (divsFlags 32 t.MXCSR (dst.read t)
            ((Operand.mem addr : Operand 32).read t))))
        dst (divsSpec 32 t.MXCSR (dst.read t) ((Operand.mem addr : Operand 32).read t))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro ctx addr dst
  have hlen' : (pre ++ 0x0F :: 0x5E :: am.modrm reg :: am.tail).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0x0F :: 0x5E :: am.modrm reg :: am.tail).length ≤ 2^32 := by
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
  have hdecode := decodeLegacy1_run_of_5E_f3_memory s h hfeat _ (pre.length + 1) (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) hcode hlow'
    (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) (by omega) _ hrex2 hrep
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hcode2 : BytesAt s s.RIP
      ((pre ++ [(0x0F : UInt8)]) ++ 0x5E :: am.modrm reg :: (am.tail ++ [])) := by
    simpa using hcode
  have hlow2 : s.RIP.toNat +
      ((pre ++ [(0x0F : UInt8)]) ++ 0x5E :: am.modrm reg :: (am.tail ++ [])).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hea := memAlu_ea_seg s h (pre ++ [0x0F]) 0x5E reg am hv [] _ hctx hcode2 hlow2
    (by simp; omega)
  rw [show (pre ++ [(0x0F : UInt8)]).length = pre.length + 1 by simp,
    show pre.length + 1 + 2 + am.tail.length = pre.length + 3 + am.tail.length by omega,
    show pre.length + 1 + 3 + am.tail.length = pre.length + 3 + am.tail.length + 1 by omega] at hea
  rw [divss_xmm_m32_form _ _ _ _ _ _ _ haddr hlock hvex hevex hevexb _ _ _ _ _ hea hrip
    _ (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hmode _) (hsse' _) hread.low hread.mem hm hok] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0x5E _ hpre ⟨by decide, by decide⟩ (by omega) hcode
    hlow' hdecode ((hmode (pre.length + 3 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

theorem divss_xmm_m32_a32_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hfeat : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE_Encoding true)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hvex : (scanContext s.DS (PrefixSegments.ofState s) pre).vex_prefix_present = false)
    (hevex : (scanContext s.DS (PrefixSegments.ofState s) pre).evex_prefix_present = false)
    (hevexb : (scanContext s.DS (PrefixSegments.ofState s) pre).evex_b = 0)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0x5E :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 3 + am.tail.length)))
      4)
    (hm : MxcsrPre s)
    (hok : divsOk 32 s.MXCSR
      ((Operand.xmm (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r4 (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r3 reg) : Operand 128).read s)
      ((Operand.mem (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 3 + am.tail.length))) : Operand 32).read s)) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt32 s (pre.length + 3 + am.tail.length))
    let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeResult ((Operand.mxcsr : Operand 32).write (dataAccess t "load")
          (mxOr t.MXCSR (divsFlags 32 t.MXCSR (dst.read t)
            ((Operand.mem addr : Operand 32).read t))))
        dst (divsSpec 32 t.MXCSR (dst.read t) ((Operand.mem addr : Operand 32).read t))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro ctx addr dst
  have hlen' : (pre ++ 0x0F :: 0x5E :: am.modrm reg :: am.tail).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0x0F :: 0x5E :: am.modrm reg :: am.tail).length ≤ 2^32 := by
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
  have hdecode := decodeLegacy1_run_of_5E_f3_memory s h hfeat _ (pre.length + 1) (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) hcode hlow'
    (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) (by omega) _ hrex2 hrep
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hcode2 : BytesAt s s.RIP
      ((pre ++ [(0x0F : UInt8)]) ++ 0x5E :: am.modrm reg :: (am.tail ++ [])) := by
    simpa using hcode
  have hlow2 : s.RIP.toNat +
      ((pre ++ [(0x0F : UInt8)]) ++ 0x5E :: am.modrm reg :: (am.tail ++ [])).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hea := memAlu_ea32_seg s h (pre ++ [0x0F]) 0x5E reg am hv [] _ hctx hcode2 hlow2
    (by simp; omega)
  rw [show (pre ++ [(0x0F : UInt8)]).length = pre.length + 1 by simp,
    show pre.length + 1 + 2 + am.tail.length = pre.length + 3 + am.tail.length by omega,
    show pre.length + 1 + 3 + am.tail.length = pre.length + 3 + am.tail.length + 1 by omega] at hea
  rw [divss_xmm_m32_form _ _ _ _ _ _ _ haddr hlock hvex hevex hevexb _ _ _ _ _ hea hrip
    _ (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hmode _) (hsse' _) hread.low hread.mem hm hok] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0x5E _ hpre ⟨by decide, by decide⟩ (by omega) hcode
    hlow' hdecode ((hmode (pre.length + 3 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

end X86Proofs
