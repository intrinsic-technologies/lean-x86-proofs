import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.Mmx
import X86Proofs.Instructions.Maskmovq.Generated.MM.Decode
import X86Proofs.Instructions.Maskmovq.Generated.MM.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem maskmovq_mm_mm_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0) (hes : fswES s.FP87_Status = 0)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor s CPUID_MMX_Encoding true)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hsr : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true →
      SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP (pre ++ [0x0F, 0xF7, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 3) ≤ 2^32)
    (hw : MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (rdi.read s)) 8) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let src : Operand 64 := .mmx (modrmReg modrm)
    let mask : Operand 64 := .mmx (modrmRm modrm)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3)
      (maskmovqState (segAddr ctx (rdi.read s)) (src.read s) (mask.read s)
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3)))))) := by
  intro ctx src mask
  have hlen' : (pre ++ [0x0F, 0xF7, modrm]).length = pre.length + 3 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x0F, 0xF7, modrm]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hcr0' (k : Nat) : Prelude.CR0.SSEEnabled (afterFetches (beforeFetch s) k).CR0 := hcr0
  have hes' (k : Nat) : fswES (afterFetches (beforeFetch s) k).FP87_Status = 0 := hes
  have hdecode := decodeLegacy1_run_of_F7_mmx_register s h hmmx _ (pre.length + 1) modrm hmod
    hcode hlow' (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) (by omega) _ hrex2
    hosz
  rw [maskmovq_mm_mm_form _ _ _ _ _ (hcr0' _) (hes' _) hrep hlock hosz haddr hm64 hsr
      (memAlu_dataReady h _) h.cpu.ds h.cpu.ss (hw.of_external_eq rfl),
    show pre.length + 1 + 2 = pre.length + 3 by omega] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xF7 [modrm] hpre ⟨by decide, by decide⟩ (by omega)
    hcode hlow' hdecode ((hmode (pre.length + 1 + 3)).of_cs_lma_eq rfl rfl)

end X86Proofs
