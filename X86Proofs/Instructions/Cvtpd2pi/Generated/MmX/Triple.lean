import X86Proofs.Instructions.Cvtpd2pi.Generated.MmX.Step
import X86Proofs.Instructions.Cvtpd2pi.Generated.MmX.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cvtpd2piMmXmmEffect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (src : BitVec 5)
    (s : RamState) : Effect :=
  let b := (Operand.xmm src : Operand 128).read s
  mmxMxcsrEffect s (p + BitVec.ofNat 64 len) dst (cvtpd2piSpec s.MXCSR b)
    (mxOr s.MXCSR (cvtpd2piFlags s.MXCSR b))

def cvtpd2piMmXmmOk (src : BitVec 5) (s : RamState) : Prop :=
  cvtpd2piOk s.MXCSR ((Operand.xmm src : Operand 128).read s)

@[simp] theorem cvtpd2piMmXmmEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (src : BitVec 5) (s : RamState) :
    (cvtpd2piMmXmmEffect p len dst src s).components = [.fpr dst, .mxcsr, .fsw, .ftw, .rip] := rfl

theorem cvtpd2pi_mm_xmm_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (FpPre (MmxEnterPre (Sse2Pre p))
        (cvtpd2piMmXmmOk (gprNumber 0 0 (modrmRm modrm))))
      (codeRange p ([0x66, 0x0F, 0x2D, modrm]))
      (cvtpd2piMmXmmEffect p 4 (modrmReg modrm)
        (gprNumber 0 0 (modrmRm modrm))) := by
  intro s h hcode ⟨⟨hpre, hes⟩, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cvtpd2pi_mm_xmm_step s h hpre.sse hes hpre.sse2 [0x66]
    (by simpa using scanPrefix_66) (by simp)
    rfl rfl rfl rfl
    rfl rfl
    modrm hmod hcode.bytesAt hlow hm
    hok
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx_mxcsr h _ _ _ _ _, ?_⟩
  exact mmxMxcsrEffect_holds h _ _ _ _ _ rfl

theorem cvtpd2pi_mm_xmm_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (FpPre (MmxEnterPre (Sse2Pre p))
        (cvtpd2piMmXmmOk (gprNumber 0 0 (modrmRm modrm))))
      (codeRange p ([0x66, 0x0F, 0x2D, modrm]))
      (Effect.post (cvtpd2piMmXmmEffect p 4 (modrmReg modrm)
        (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvtpd2piMmXmmEffect_components]; simp [Component.Covers]) _)
    (cvtpd2pi_mm_xmm_effect_step p modrm hmod)

theorem cvtpd2pi_mm_xmm_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (FpPre (MmxEnterPre (Sse2Pre p))
        (cvtpd2piMmXmmOk (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))))
      (codeRange p ([0x66, rex, 0x0F, 0x2D, modrm]))
      (cvtpd2piMmXmmEffect p 5 (modrmReg modrm)
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  intro s h hcode ⟨⟨hpre, hes⟩, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_66_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := cvtpd2pi_mm_xmm_step s h hpre.sse hes hpre.sse2 [0x66, rex]
    (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl)
    modrm hmod hcode.bytesAt hlow hm
    (by rw [hc]; exact hok)
  simp only [hc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx_mxcsr h _ _ _ _ _, ?_⟩
  exact mmxMxcsrEffect_holds h _ _ _ _ _ rfl

theorem cvtpd2pi_mm_xmm_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (FpPre (MmxEnterPre (Sse2Pre p))
        (cvtpd2piMmXmmOk (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))))
      (codeRange p ([0x66, rex, 0x0F, 0x2D, modrm]))
      (Effect.post (cvtpd2piMmXmmEffect p 5 (modrmReg modrm)
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvtpd2piMmXmmEffect_components]; simp [Component.Covers]) _)
    (cvtpd2pi_mm_xmm_rex_effect_step p rex hr modrm hmod)

theorem cvtpd2pi_mm_xmm_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (src : BitVec 4) :
    Triple
      (FpPre (MmxEnterPre (Sse2Pre p))
        (cvtpd2piMmXmmOk (src.setWidth 5)))
      (codeRange p (encodeCvtpd2piMmXmm dst src))
      (Effect.post (cvtpd2piMmXmmEffect p (encodeCvtpd2piMmXmm dst src).length dst
        (src.setWidth 5))) := by
  unfold encodeCvtpd2piMmXmm
  rcases encodeMmxGpr_spec 0x2D dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact cvtpd2pi_mm_xmm_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact cvtpd2pi_mm_xmm_rex_triple_of_bytes p rex hrex.rexPrefix modrm hmod

attribute [x86_compose] cvtpd2piMmXmmEffect

@[x86_local] theorem cvtpd2piMmXmmEffect_local {p : BitVec 64} {len : Nat}
    {dst : BitVec 3} {src : BitVec 5} :
    Effect.Local (cvtpd2piMmXmmEffect p len dst src) := by
  effect_local [cvtpd2piMmXmmEffect, mmxMxcsrEffect, Effect.withMmx]

end X86Proofs
