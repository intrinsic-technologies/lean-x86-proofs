import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.Mmx
import X86Proofs.Instructions.Movq.Generated.RM64.Decode
import X86Proofs.Instructions.Movq.Generated.RM64.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem movq_r64_mm_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0) (hes : fswES s.FP87_Status = 0)
    (hfeat : Prelude.ReportsCPUFeature Bindings.processor s CPUID_MMX_Encoding true)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP (pre ++ [0x0F, 0x7E, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 3) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm))
    let src : Operand 64 := .mmx (modrmReg modrm)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3) fun t =>
      writeResult (mmxEnter t) dst (movdSpec 64 64 (src.read t))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3))))) := by
  intro ctx dst src
  have hlen' : (pre ++ [0x0F, 0x7E, modrm]).length = pre.length + 3 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x0F, 0x7E, modrm]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hcr0' (k : Nat) : Prelude.CR0.SSEEnabled (afterFetches (beforeFetch s) k).CR0 := hcr0
  have hes' (k : Nat) : fswES (afterFetches (beforeFetch s) k).FP87_Status = 0 := hes
  have hdecode := decodeLegacy1_run_of_7E_w1_mmx_register s h hfeat _ (pre.length + 1) modrm hmod hcode
    hlow' (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) (by omega) _ hrex2
    hosz hw hrep
  rw [movq_r64_mm_form _ _ _ _ _ (hmode _) (hcr0' _) (hes' _) hlock hw hosz hrep,
    show pre.length + 1 + 2 = pre.length + 3 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0x7E [modrm] hpre ⟨by decide, by decide⟩ (by omega)
    hcode hlow' hdecode ((hmode (pre.length + 1 + 3)).of_cs_lma_eq rfl rfl)

end X86Proofs
