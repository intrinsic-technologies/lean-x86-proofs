import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.Float
import X86Proofs.Instructions.Cvtss2si.Generated.R64X.Decode
import X86Proofs.Instructions.Cvtss2si.Generated.R64X.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cvtss2si_r64_xmm_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hfeat : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE_Encoding true)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hevex : (scanContext s.DS (PrefixSegments.ofState s) pre).evex_prefix_present = false)
    (hevexb : (scanContext s.DS (PrefixSegments.ofState s) pre).evex_b = 0)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP (pre ++ [0x0F, 0x2D, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 3) ≤ 2^32)
    (hm : MxcsrPre s)
    (hok : cvts2siOk 32 64 s.MXCSR
      ((Operand.xmm (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_b4 (scanContext s.DS (PrefixSegments.ofState s) pre).rex_b3 (modrmRm modrm)) :
        Operand 128).read s)) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand 64 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 (modrmReg modrm))
    let src : Operand 128 := .xmm (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3) fun t =>
      writeResult ((Operand.mxcsr : Operand 32).write t
          (mxOr t.MXCSR (cvts2siFlags 32 64 t.MXCSR (src.read t))))
        dst (cvts2siSpec 32 64 t.MXCSR (src.read t))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3))))) := by
  intro ctx dst src
  have hlen' : (pre ++ [0x0F, 0x2D, modrm]).length = pre.length + 3 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x0F, 0x2D, modrm]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hsse' (k : Nat) : Prelude.SupportedSSE Bindings.processor (afterFetches (beforeFetch s) k) :=
    SupportedSSE.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      hsse
  have hdecode := decodeLegacy1_run_of_2D_f3_w1_register s h hfeat _ (pre.length + 1) modrm hmod hcode
    hlow' (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) (by omega) _
    hrex2 hrep hw
  rw [show modrmMod modrm = 3 from hmod,
    cvtss2si_r64_xmm_form _ _ _ _ _ (hmode _) (hsse' _) hlock hw hevex hevexb hm hok,
    show pre.length + 1 + 2 = pre.length + 3 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0x2D [modrm] hpre ⟨by decide, by decide⟩ (by omega)
    hcode hlow' hdecode ((hmode (pre.length + 1 + 3)).of_cs_lma_eq rfl rfl)

end X86Proofs
