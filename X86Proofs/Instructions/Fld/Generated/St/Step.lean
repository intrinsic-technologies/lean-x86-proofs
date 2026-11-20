
import X86Proofs.Step.AfterStep
import X86Proofs.Step.PrefixScan
import X86Proofs.Program.ReadWrite.X87
import X86Proofs.Instructions.Fld.Generated.St.Decode
import X86Proofs.Instructions.Fld.Generated.St.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem fld_st_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0)
    (hes : fswES s.FP87_Status = 0)
    (hm : FcwMasked s.FP87_Control)
    (hfdp : Prelude.ReportsCPUFeature Bindings.processor s CPUID_FDP_EXCPTN_ONLY_Encoding true)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hsrc : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + modrmRm modrm) ≠ 3)
    (hpush : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 7) = 3)
    (hcode : BytesAt s s.RIP (pre ++ [0xD9, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 2) ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2) fun t =>
      x87Out t (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2))) 3
        (fprSet t.FP87 (fswTop t.FP87_Status - 1)
            t.FP87[fprIndex (fswTop t.FP87_Status + modrmRm modrm)])
        (ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status - 1)
            (x87Tag t.FP87[fprIndex (fswTop t.FP87_Status + modrmRm modrm)]))
        (fswSetTop (fldStatus t.FP87_Status t.oracle) (fswTop t.FP87_Status - 1)))) := by
  have hlen' : (pre ++ [0xD9, modrm]).length = pre.length + 2 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xD9, modrm]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hdecode := decodeLegacy0_run_of_fld_st s h _ pre.length modrm hmod hreg hcode
    hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  let t := afterFetches (beforeFetch s) (pre.length + 3)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [fld_st_form t _ _ _ _ _ _ hlock hcr0 hes hm
    (reportsCPUFeature_of_sameControls (s := s) (t := t)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hfdp) hmode hsrc hpush] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xD9 _ hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    (hmode.of_cs_lma_eq rfl rfl)

end X86Proofs
