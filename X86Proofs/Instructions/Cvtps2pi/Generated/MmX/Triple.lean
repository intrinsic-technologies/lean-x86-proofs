import X86Proofs.Instructions.Cvtps2pi.Generated.MmX.Step
import X86Proofs.Instructions.Cvtps2pi.Generated.MmX.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cvtps2piMmXmmEffect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (src : BitVec 5)
    (s : RamState) : Effect :=
  let b := (Operand.xmm src : Operand 128).read s
  mmxMxcsrEffect s (p + BitVec.ofNat 64 len) dst (cvtps2piSpec s.MXCSR b)
    (mxOr s.MXCSR (cvtps2piFlags s.MXCSR b))

def cvtps2piMmXmmOk (src : BitVec 5) (s : RamState) : Prop :=
  cvtps2piOk s.MXCSR ((Operand.xmm src : Operand 128).read s)

@[simp] theorem cvtps2piMmXmmEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (src : BitVec 5) (s : RamState) :
    (cvtps2piMmXmmEffect p len dst src s).components = [.fpr dst, .mxcsr, .fsw, .ftw, .rip] := rfl

theorem cvtps2pi_mm_xmm_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (FpPre (MmxEnterPre (SsePre p))
        (cvtps2piMmXmmOk (gprNumber 0 0 (modrmRm modrm))))
      (codeRange p ([0x0F, 0x2D, modrm]))
      (cvtps2piMmXmmEffect p 3 (modrmReg modrm)
        (gprNumber 0 0 (modrmRm modrm))) := by
  intro s h hcode ⟨⟨hpre, hes⟩, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cvtps2pi_mm_xmm_step s h hpre.sse hes hpre.sse.feature []
    (by simp) (by simp)
    rfl rfl rfl rfl
    rfl rfl
    modrm hmod hcode.bytesAt hlow hm
    hok
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx_mxcsr h _ _ _ _ _, ?_⟩
  exact mmxMxcsrEffect_holds h _ _ _ _ _ rfl

theorem cvtps2pi_mm_xmm_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (FpPre (MmxEnterPre (SsePre p))
        (cvtps2piMmXmmOk (gprNumber 0 0 (modrmRm modrm))))
      (codeRange p ([0x0F, 0x2D, modrm]))
      (Effect.post (cvtps2piMmXmmEffect p 3 (modrmReg modrm)
        (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvtps2piMmXmmEffect_components]; simp [Component.Covers]) _)
    (cvtps2pi_mm_xmm_effect_step p modrm hmod)

theorem cvtps2pi_mm_xmm_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (FpPre (MmxEnterPre (SsePre p))
        (cvtps2piMmXmmOk (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))))
      (codeRange p ([rex, 0x0F, 0x2D, modrm]))
      (cvtps2piMmXmmEffect p 4 (modrmReg modrm)
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  intro s h hcode ⟨⟨hpre, hes⟩, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := cvtps2pi_mm_xmm_step s h hpre.sse hes hpre.sse.feature [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl)
    modrm hmod hcode.bytesAt hlow hm
    (by rw [hc]; exact hok)
  simp only [hc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx_mxcsr h _ _ _ _ _, ?_⟩
  exact mmxMxcsrEffect_holds h _ _ _ _ _ rfl

theorem cvtps2pi_mm_xmm_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (FpPre (MmxEnterPre (SsePre p))
        (cvtps2piMmXmmOk (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))))
      (codeRange p ([rex, 0x0F, 0x2D, modrm]))
      (Effect.post (cvtps2piMmXmmEffect p 4 (modrmReg modrm)
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvtps2piMmXmmEffect_components]; simp [Component.Covers]) _)
    (cvtps2pi_mm_xmm_rex_effect_step p rex hr modrm hmod)

theorem cvtps2pi_mm_xmm_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (src : BitVec 4) :
    Triple
      (FpPre (MmxEnterPre (SsePre p))
        (cvtps2piMmXmmOk (src.setWidth 5)))
      (codeRange p (encodeCvtps2piMmXmm dst src))
      (Effect.post (cvtps2piMmXmmEffect p (encodeCvtps2piMmXmm dst src).length dst
        (src.setWidth 5))) := by
  unfold encodeCvtps2piMmXmm
  rcases encodeMmxGpr_spec 0x2D dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact cvtps2pi_mm_xmm_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact cvtps2pi_mm_xmm_rex_triple_of_bytes p rex hrex.rexPrefix modrm hmod

attribute [x86_compose] cvtps2piMmXmmEffect

@[x86_local] theorem cvtps2piMmXmmEffect_local {p : BitVec 64} {len : Nat}
    {dst : BitVec 3} {src : BitVec 5} :
    Effect.Local (cvtps2piMmXmmEffect p len dst src) := by
  effect_local [cvtps2piMmXmmEffect, mmxMxcsrEffect, Effect.withMmx]

end X86Proofs
