import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.Sse
import X86Proofs.Instructions.Pmovmskb.Generated.RX.Decode
import X86Proofs.Instructions.Pmovmskb.Generated.RX.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem pmovmskb_r32_xmm_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hfeat : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hevex : (scanContext s.DS (PrefixSegments.ofState s) pre).evex_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP (pre ++ [0x0F, 0xD7, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 3) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand 32 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 (modrmReg modrm))
    let src : Operand 128 := .xmm (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3) fun t =>
      writeResult t dst (movmskSpec 8 (src.read t))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3))))) := by
  intro ctx dst src
  have hlen' : (pre ++ [0x0F, 0xD7, modrm]).length = pre.length + 3 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x0F, 0xD7, modrm]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hsse' (k : Nat) : Prelude.SupportedSSE Bindings.processor (afterFetches (beforeFetch s) k) :=
    SupportedSSE.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      hsse
  have hdecode := decodeLegacy1_run_of_D7_66_register s h hfeat _ (pre.length + 1) modrm hmod
    hcode hlow' (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) (by omega) _
    hrex2 hosz
  rw [show modrmMod modrm = 3 from hmod,
    pmovmskb_r32_xmm_form _ _ _ _ _ (hmode _) (hsse' _) hrep hlock hevex,
    show pre.length + 1 + 2 = pre.length + 3 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xD7 [modrm] hpre ⟨by decide, by decide⟩ (by omega)
    hcode hlow' hdecode ((hmode (pre.length + 1 + 3)).of_cs_lma_eq rfl rfl)

end X86Proofs
