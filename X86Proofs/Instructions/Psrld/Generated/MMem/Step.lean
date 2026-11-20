import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.Mmx
import X86Proofs.Instructions.Psrld.Generated.MMem.Decode
import X86Proofs.Instructions.Psrld.Generated.MMem.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem psrld_mm_m64_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0) (hes : fswES s.FP87_Status = 0)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor s CPUID_MMX_Encoding true)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0xD2 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 3 + am.tail.length)))
      8) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt s (pre.length + 3 + am.tail.length))
    let dst : Operand 64 := .mmx reg
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeResult (mmxEnter (dataAccess t "load")) dst
        (psrlMmxSpec 32 (dst.read t) ((Operand.mem addr : Operand 64).read t).toNat)
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro ctx addr dst
  have hlen' : (pre ++ 0x0F :: 0xD2 :: am.modrm reg :: am.tail).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0x0F :: 0xD2 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hcr0' (k : Nat) : Prelude.CR0.SSEEnabled (afterFetches (beforeFetch s) k).CR0 := hcr0
  have hes' (k : Nat) : fswES (afterFetches (beforeFetch s) k).FP87_Status = 0 := hes
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  have hdecode := decodeLegacy1_run_of_D2_mmx_memory s h hmmx _ (pre.length + 1) (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) hcode hlow'
    (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) (by omega) _ hrex2 hosz
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hcode2 : BytesAt s s.RIP
      ((pre ++ [(0x0F : UInt8)]) ++ 0xD2 :: am.modrm reg :: (am.tail ++ [])) := by
    simpa using hcode
  have hlow2 : s.RIP.toNat +
      ((pre ++ [(0x0F : UInt8)]) ++ 0xD2 :: am.modrm reg :: (am.tail ++ [])).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hea := memAlu_ea_seg s h (pre ++ [0x0F]) 0xD2 reg am hv [] _ hctx hcode2 hlow2
    (by simp; omega)
  rw [show (pre ++ [(0x0F : UInt8)]).length = pre.length + 1 by simp,
    show pre.length + 1 + 2 + am.tail.length = pre.length + 3 + am.tail.length by omega,
    show pre.length + 1 + 3 + am.tail.length = pre.length + 3 + am.tail.length + 1 by omega] at hea
  rw [psrld_mm_m_form _ _ _ _ _ _ _ haddr hrep hlock hosz _ _ _ _ _ hea hrip
    _ (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hcr0' _) (hes' _)
    hread.low hread.mem] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xD2 _ hpre ⟨by decide, by decide⟩ (by omega) hcode
    hlow' hdecode ((hmode (pre.length + 3 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

theorem psrld_mm_m64_a32_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0) (hes : fswES s.FP87_Status = 0)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor s CPUID_MMX_Encoding true)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0xD2 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s (pre.length + 3 + am.tail.length)))
      8) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt32 s (pre.length + 3 + am.tail.length))
    let dst : Operand 64 := .mmx reg
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeResult (mmxEnter (dataAccess t "load")) dst
        (psrlMmxSpec 32 (dst.read t) ((Operand.mem addr : Operand 64).read t).toNat)
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro ctx addr dst
  have hlen' : (pre ++ 0x0F :: 0xD2 :: am.modrm reg :: am.tail).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0x0F :: 0xD2 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hcr0' (k : Nat) : Prelude.CR0.SSEEnabled (afterFetches (beforeFetch s) k).CR0 := hcr0
  have hes' (k : Nat) : fswES (afterFetches (beforeFetch s) k).FP87_Status = 0 := hes
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  have hdecode := decodeLegacy1_run_of_D2_mmx_memory s h hmmx _ (pre.length + 1) (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) hcode hlow'
    (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) (by omega) _ hrex2 hosz
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hcode2 : BytesAt s s.RIP
      ((pre ++ [(0x0F : UInt8)]) ++ 0xD2 :: am.modrm reg :: (am.tail ++ [])) := by
    simpa using hcode
  have hlow2 : s.RIP.toNat +
      ((pre ++ [(0x0F : UInt8)]) ++ 0xD2 :: am.modrm reg :: (am.tail ++ [])).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hea := memAlu_ea32_seg s h (pre ++ [0x0F]) 0xD2 reg am hv [] _ hctx hcode2 hlow2
    (by simp; omega)
  rw [show (pre ++ [(0x0F : UInt8)]).length = pre.length + 1 by simp,
    show pre.length + 1 + 2 + am.tail.length = pre.length + 3 + am.tail.length by omega,
    show pre.length + 1 + 3 + am.tail.length = pre.length + 3 + am.tail.length + 1 by omega] at hea
  rw [psrld_mm_m_form _ _ _ _ _ _ _ haddr hrep hlock hosz _ _ _ _ _ hea hrip
    _ (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hcr0' _) (hes' _)
    hread.low hread.mem] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xD2 _ hpre ⟨by decide, by decide⟩ (by omega) hcode
    hlow' hdecode ((hmode (pre.length + 3 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

end X86Proofs
