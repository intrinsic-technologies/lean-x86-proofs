import X86Proofs.Instructions.Cvtpi2ps.Generated.XMm.Step
import X86Proofs.Instructions.Cvtpi2ps.Generated.XMm.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cvtpi2psXmmMmEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 3)
    (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.mmx src : Operand 64).read s
  ({ rip := p + BitVec.ofNat 64 len
     writes := [⟨(Operand.xmm dst : Operand 128), cvtpi2psSpec s.MXCSR a b⟩,
       ⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (cvtpi2psFlags s.MXCSR a b)⟩] } :
    Effect).withMmx s

def cvtpi2psXmmMmOk (dst : BitVec 5) (src : BitVec 3) (s : RamState) : Prop :=
  cvtpi2psOk s.MXCSR ((Operand.xmm dst : Operand 128).read s)
    ((Operand.mmx src : Operand 64).read s)

@[simp] theorem cvtpi2psXmmMmEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (src : BitVec 3) (s : RamState) :
    (cvtpi2psXmmMmEffect p len dst src s).components = [.xmm dst, .mxcsr, .fsw, .ftw, .rip] := rfl

theorem cvtpi2ps_xmm_mm_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (FpPre (MmxEnterPre (SsePre p))
        (cvtpi2psXmmMmOk (gprNumber 0 0 (modrmReg modrm)) (modrmRm modrm)))
      (codeRange p ([0x0F, 0x2A, modrm]))
      (cvtpi2psXmmMmEffect p 3 (gprNumber 0 0 (modrmReg modrm))
        (modrmRm modrm)) := by
  intro s h hcode ⟨⟨hpre, hes⟩, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cvtpi2ps_xmm_mm_step s h hpre.sse hes hpre.sse.feature []
    (by simp) (by simp)
    rfl rfl rfl rfl
    rfl rfl
    modrm hmod hcode.bytesAt hlow hm
    hok
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_xmm_mxcsr_mmx h _ _ _ _ _, ?_⟩
  exact xmmMxcsrMmxEffect_holds h _ _ _ _ _ rfl

theorem cvtpi2ps_xmm_mm_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (FpPre (MmxEnterPre (SsePre p))
        (cvtpi2psXmmMmOk (gprNumber 0 0 (modrmReg modrm)) (modrmRm modrm)))
      (codeRange p ([0x0F, 0x2A, modrm]))
      (Effect.post (cvtpi2psXmmMmEffect p 3 (gprNumber 0 0 (modrmReg modrm))
        (modrmRm modrm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvtpi2psXmmMmEffect_components]; simp [Component.Covers]) _)
    (cvtpi2ps_xmm_mm_effect_step p modrm hmod)

theorem cvtpi2ps_xmm_mm_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (FpPre (MmxEnterPre (SsePre p))
        (cvtpi2psXmmMmOk (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) (modrmRm modrm)))
      (codeRange p ([rex, 0x0F, 0x2A, modrm]))
      (cvtpi2psXmmMmEffect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (modrmRm modrm)) := by
  intro s h hcode ⟨⟨hpre, hes⟩, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := cvtpi2ps_xmm_mm_step s h hpre.sse hes hpre.sse.feature [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl)
    modrm hmod hcode.bytesAt hlow hm
    (by rw [hc]; exact hok)
  simp only [hc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_xmm_mxcsr_mmx h _ _ _ _ _, ?_⟩
  exact xmmMxcsrMmxEffect_holds h _ _ _ _ _ rfl

theorem cvtpi2ps_xmm_mm_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (FpPre (MmxEnterPre (SsePre p))
        (cvtpi2psXmmMmOk (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) (modrmRm modrm)))
      (codeRange p ([rex, 0x0F, 0x2A, modrm]))
      (Effect.post (cvtpi2psXmmMmEffect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (modrmRm modrm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvtpi2psXmmMmEffect_components]; simp [Component.Covers]) _)
    (cvtpi2ps_xmm_mm_rex_effect_step p rex hr modrm hmod)

theorem cvtpi2ps_xmm_mm_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (src : BitVec 3) :
    Triple
      (FpPre (MmxEnterPre (SsePre p))
        (cvtpi2psXmmMmOk (dst.setWidth 5) src))
      (codeRange p (encodeCvtpi2psXmmMm dst src))
      (Effect.post (cvtpi2psXmmMmEffect p (encodeCvtpi2psXmmMm dst src).length (dst.setWidth 5)
        src)) := by
  unfold encodeCvtpi2psXmmMm
  rcases encodeGprMmx_spec 0x2A dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact cvtpi2ps_xmm_mm_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact cvtpi2ps_xmm_mm_rex_triple_of_bytes p rex hrex.rexPrefix modrm hmod

attribute [x86_compose] cvtpi2psXmmMmEffect

@[x86_local] theorem cvtpi2psXmmMmEffect_local {p : BitVec 64} {len : Nat}
    {dst : BitVec 5} {src : BitVec 3} :
    Effect.Local (cvtpi2psXmmMmEffect p len dst src) := by
  effect_local [cvtpi2psXmmMmEffect, Effect.withMmx]

end X86Proofs
