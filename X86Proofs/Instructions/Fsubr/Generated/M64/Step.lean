
import X86Proofs.Step.AfterStep
import X86Proofs.Step.PrefixScan
import X86Proofs.Instructions.Fsubr.Generated.M64.Decode
import X86Proofs.Instructions.Fsubr.Generated.M64.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem fsubr_m64_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0)
    (hes : fswES s.FP87_Status = 0)
    (hm : FcwMasked s.FP87_Control)
    (hfdp : Prelude.ReportsCPUFeature Bindings.processor s CPUID_FDP_EXCPTN_ONLY_Encoding true)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid)
        (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (hok : X87ArithDOk .sub s.FP87_Control
        (x87FromFloat (size := 64)
        ((Operand.mem
        (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
        (am.addrAt s (pre.length + 2 + am.tail.length))) : Operand 64).read s)).2 false
        (x87FromFloat (size := 64)
        ((Operand.mem
        (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
        (am.addrAt s (pre.length + 2 + am.tail.length))) : Operand 64).read s)).1
        s.FP87[fprIndex (fswTop s.FP87_Status)])
    (hcode : BytesAt s s.RIP (pre ++ 0xDC :: am.modrm 5 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s
        (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
        (am.addrAt s (pre.length + 2 + am.tail.length))) 8) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
        (am.addrAt s (pre.length + 2 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      x87Out (dataAccess t "load")
          (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) 6
        (fprSet t.FP87 (fswTop t.FP87_Status)
            (x87ArithD .sub t.FP87_Control
            (x87FromFloat (size := 64) ((Operand.mem addr : Operand 64).read t)).2 false
            (x87FromFloat (size := 64) ((Operand.mem addr : Operand 64).read t)).1
            t.FP87[fprIndex (fswTop t.FP87_Status)]).1)
        (ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status)
            (x87Tag
            (x87ArithD .sub t.FP87_Control
            (x87FromFloat (size := 64) ((Operand.mem addr : Operand 64).read t)).2 false
            (x87FromFloat (size := 64) ((Operand.mem addr : Operand 64).read t)).1
            t.FP87[fprIndex (fswTop t.FP87_Status)]).1))
        (x87ArithFsw t.FP87_Status t.FP87_Status (dataAccess t "load").oracle
            (x87ArithD .sub t.FP87_Control
            (x87FromFloat (size := 64) ((Operand.mem addr : Operand 64).read t)).2 false
            (x87FromFloat (size := 64) ((Operand.mem addr : Operand 64).read t)).1
            t.FP87[fprIndex (fswTop t.FP87_Status)]).2.1
            (x87ArithD .sub t.FP87_Control
            (x87FromFloat (size := 64) ((Operand.mem addr : Operand 64).read t)).2 false
            (x87FromFloat (size := 64) ((Operand.mem addr : Operand 64).read t)).1
            t.FP87[fprIndex (fswTop t.FP87_Status)]).2.2))) := by
  intro addr
  have hlen' : (pre ++ 0xDC :: am.modrm 5 :: am.tail).length = pre.length + 2 + am.tail.length := by
    simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0xDC :: am.modrm 5 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_fsubr_m64 s h _ pre.length (am.modrm 5)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _)
    hcode hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm, AddrMode.modrmReg_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0xDC 5 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [fsubr_m64_form _ _ _ _ _ _ _ _ haddr hlock _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hcr0 hes hm
    (reportsCPUFeature_of_sameControls (s := s)
      (t := afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1))
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hfdp) hmode h0 hok hread.low
          hread.mem] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xDC _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem fsubr_m64_a32_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0)
    (hes : fswES s.FP87_Status = 0)
    (hm : FcwMasked s.FP87_Control)
    (hfdp : Prelude.ReportsCPUFeature Bindings.processor s CPUID_FDP_EXCPTN_ONLY_Encoding true)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid)
        (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (hok : X87ArithDOk .sub s.FP87_Control
        (x87FromFloat (size := 64)
        ((Operand.mem
        (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
        (am.addrAt32 s (pre.length + 2 + am.tail.length))) : Operand 64).read s)).2 false
        (x87FromFloat (size := 64)
        ((Operand.mem
        (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
        (am.addrAt32 s (pre.length + 2 + am.tail.length))) : Operand 64).read s)).1
        s.FP87[fprIndex (fswTop s.FP87_Status)])
    (hcode : BytesAt s s.RIP (pre ++ 0xDC :: am.modrm 5 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s
        (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
        (am.addrAt32 s (pre.length + 2 + am.tail.length))) 8) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
        (am.addrAt32 s (pre.length + 2 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      x87Out (dataAccess t "load")
          (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) 6
        (fprSet t.FP87 (fswTop t.FP87_Status)
            (x87ArithD .sub t.FP87_Control
            (x87FromFloat (size := 64) ((Operand.mem addr : Operand 64).read t)).2 false
            (x87FromFloat (size := 64) ((Operand.mem addr : Operand 64).read t)).1
            t.FP87[fprIndex (fswTop t.FP87_Status)]).1)
        (ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status)
            (x87Tag
            (x87ArithD .sub t.FP87_Control
            (x87FromFloat (size := 64) ((Operand.mem addr : Operand 64).read t)).2 false
            (x87FromFloat (size := 64) ((Operand.mem addr : Operand 64).read t)).1
            t.FP87[fprIndex (fswTop t.FP87_Status)]).1))
        (x87ArithFsw t.FP87_Status t.FP87_Status (dataAccess t "load").oracle
            (x87ArithD .sub t.FP87_Control
            (x87FromFloat (size := 64) ((Operand.mem addr : Operand 64).read t)).2 false
            (x87FromFloat (size := 64) ((Operand.mem addr : Operand 64).read t)).1
            t.FP87[fprIndex (fswTop t.FP87_Status)]).2.1
            (x87ArithD .sub t.FP87_Control
            (x87FromFloat (size := 64) ((Operand.mem addr : Operand 64).read t)).2 false
            (x87FromFloat (size := 64) ((Operand.mem addr : Operand 64).read t)).1
            t.FP87[fprIndex (fswTop t.FP87_Status)]).2.2))) := by
  intro addr
  have hlen' : (pre ++ 0xDC :: am.modrm 5 :: am.tail).length = pre.length + 2 + am.tail.length := by
    simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0xDC :: am.modrm 5 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_fsubr_m64 s h _ pre.length (am.modrm 5)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _)
    hcode hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm, AddrMode.modrmReg_modrm] at hdecode
  have hea := memAlu_ea32_seg s h pre 0xDC 5 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [fsubr_m64_form _ _ _ _ _ _ _ _ haddr hlock _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hcr0 hes hm
    (reportsCPUFeature_of_sameControls (s := s)
      (t := afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1))
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hfdp) hmode h0 hok hread.low
          hread.mem] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xDC _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

end X86Proofs
