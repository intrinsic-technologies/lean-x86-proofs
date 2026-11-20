
import X86Proofs.Step.AfterStep
import X86Proofs.Step.PrefixScan
import X86Proofs.Program.ReadWrite.X87
import X86Proofs.Instructions.Fsincos.Generated.Fsincos.Decode
import X86Proofs.Instructions.Fsincos.Generated.Fsincos.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem fsincos_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0)
    (hes : fswES s.FP87_Status = 0)
    (hm : FcwMasked s.FP87_Control)
    (hfdp : Prelude.ReportsCPUFeature Bindings.processor s CPUID_FDP_EXCPTN_ONLY_Encoding true)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7)
    (hrm : modrmRm modrm = 3)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (hpush : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 7) = 3)
    (hok : X87BindOk (FP87.Sin_Cos s.FP87[fprIndex (fswTop s.FP87_Status)]) s.FP87_Control)
    (hcode : BytesAt s s.RIP (pre ++ [0xD9, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 2) ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2) fun t =>
      x87Out t (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2)))
          (if
          (x87BindVal (FP87.Sin_Cos t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).2.2.2.1
          = true then 3 else 2)
        (if
            (x87BindVal (FP87.Sin_Cos t.FP87[fprIndex (fswTop t.FP87_Status)])
            t.FP87_Control).2.2.2.1 then t.FP87 else fprSet
            (fprSet t.FP87 (fswTop t.FP87_Status)
            (x87BindVal (FP87.Sin_Cos t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).2.1)
            (fswTop t.FP87_Status - 1)
            (x87BindVal (FP87.Sin_Cos t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).1)
        (if
            (x87BindVal (FP87.Sin_Cos t.FP87[fprIndex (fswTop t.FP87_Status)])
            t.FP87_Control).2.2.2.1 then t.FP87_Tag_Word else ftwSet
            (ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status)
            (x87Tag
            (x87BindVal (FP87.Sin_Cos t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).2.1))
            (fswTop t.FP87_Status - 1)
            (x87Tag
            (x87BindVal (FP87.Sin_Cos t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).1))
        (if
            (x87BindVal (FP87.Sin_Cos t.FP87[fprIndex (fswTop t.FP87_Status)])
            t.FP87_Control).2.2.2.1 then x87CosFsw t.FP87_Status t.oracle
            (x87BindVal (FP87.Sin_Cos t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).2.2.1
            (x87BindVal (FP87.Sin_Cos t.FP87[fprIndex (fswTop t.FP87_Status)])
            t.FP87_Control).2.2.2.1
            (x87BindVal (FP87.Sin_Cos t.FP87[fprIndex (fswTop t.FP87_Status)])
            t.FP87_Control).2.2.2.2 else fswSetTop
            (x87CosFsw t.FP87_Status t.oracle
            (x87BindVal (FP87.Sin_Cos t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).2.2.1
            (x87BindVal (FP87.Sin_Cos t.FP87[fprIndex (fswTop t.FP87_Status)])
            t.FP87_Control).2.2.2.1
            (x87BindVal (FP87.Sin_Cos t.FP87[fprIndex (fswTop t.FP87_Status)])
            t.FP87_Control).2.2.2.2) (fswTop t.FP87_Status - 1)))) := by
  have hlen' : (pre ++ [0xD9, modrm]).length = pre.length + 2 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xD9, modrm]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hdecode := decodeLegacy0_run_of_fsincos s h _ pre.length modrm hmod hreg hrm hcode
    hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  let t := afterFetches (beforeFetch s) (pre.length + 3)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [fsincos_form t _ _ _ _ _ _ hlock hcr0 hes hm
    (reportsCPUFeature_of_sameControls (s := s) (t := t)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hfdp) hmode h0 hpush hok] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xD9 _ hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    (hmode.of_cs_lma_eq rfl rfl)

end X86Proofs
