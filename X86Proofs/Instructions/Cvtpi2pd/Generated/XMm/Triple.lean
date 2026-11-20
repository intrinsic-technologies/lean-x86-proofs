import X86Proofs.Instructions.Cvtpi2pd.Generated.XMm.Step
import X86Proofs.Instructions.Cvtpi2pd.Generated.XMm.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cvtpi2pdXmmMmEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 3)
    (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.mmx src : Operand 64).read s
  ({ rip := p + BitVec.ofNat 64 len
     writes := [⟨(Operand.xmm dst : Operand 128), cvtpi2pdSpec s.MXCSR a b⟩,
       ⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (cvtpi2pdFlags s.MXCSR a b)⟩] } :
    Effect).withMmx s

def cvtpi2pdXmmMmOk (dst : BitVec 5) (src : BitVec 3) (s : RamState) : Prop :=
  cvtpi2pdOk s.MXCSR ((Operand.xmm dst : Operand 128).read s)
    ((Operand.mmx src : Operand 64).read s)

@[simp] theorem cvtpi2pdXmmMmEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (src : BitVec 3) (s : RamState) :
    (cvtpi2pdXmmMmEffect p len dst src s).components = [.xmm dst, .mxcsr, .fsw, .ftw, .rip] := rfl

theorem cvtpi2pd_xmm_mm_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (FpPre (MmxEnterPre (Sse2Pre p))
        (cvtpi2pdXmmMmOk (gprNumber 0 0 (modrmReg modrm)) (modrmRm modrm)))
      (codeRange p ([0x66, 0x0F, 0x2A, modrm]))
      (cvtpi2pdXmmMmEffect p 4 (gprNumber 0 0 (modrmReg modrm))
        (modrmRm modrm)) := by
  intro s h hcode ⟨⟨hpre, hes⟩, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cvtpi2pd_xmm_mm_step s h hpre.sse hes hpre.sse2 [0x66]
    (by simpa using scanPrefix_66) (by simp)
    rfl rfl rfl rfl
    rfl rfl rfl
    modrm hmod hcode.bytesAt hlow hm
    hok
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_xmm_mxcsr_mmx h _ _ _ _ _, ?_⟩
  exact xmmMxcsrMmxEffect_holds h _ _ _ _ _ rfl

theorem cvtpi2pd_xmm_mm_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (FpPre (MmxEnterPre (Sse2Pre p))
        (cvtpi2pdXmmMmOk (gprNumber 0 0 (modrmReg modrm)) (modrmRm modrm)))
      (codeRange p ([0x66, 0x0F, 0x2A, modrm]))
      (Effect.post (cvtpi2pdXmmMmEffect p 4 (gprNumber 0 0 (modrmReg modrm))
        (modrmRm modrm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvtpi2pdXmmMmEffect_components]; simp [Component.Covers]) _)
    (cvtpi2pd_xmm_mm_effect_step p modrm hmod)

theorem cvtpi2pd_xmm_mm_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (FpPre (MmxEnterPre (Sse2Pre p))
        (cvtpi2pdXmmMmOk (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) (modrmRm modrm)))
      (codeRange p ([0x66, rex, 0x0F, 0x2A, modrm]))
      (cvtpi2pdXmmMmEffect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (modrmRm modrm)) := by
  intro s h hcode ⟨⟨hpre, hes⟩, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_66_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := cvtpi2pd_xmm_mm_step s h hpre.sse hes hpre.sse2 [0x66, rex]
    (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    modrm hmod hcode.bytesAt hlow hm
    (by rw [hc]; exact hok)
  simp only [hc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_xmm_mxcsr_mmx h _ _ _ _ _, ?_⟩
  exact xmmMxcsrMmxEffect_holds h _ _ _ _ _ rfl

theorem cvtpi2pd_xmm_mm_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (FpPre (MmxEnterPre (Sse2Pre p))
        (cvtpi2pdXmmMmOk (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) (modrmRm modrm)))
      (codeRange p ([0x66, rex, 0x0F, 0x2A, modrm]))
      (Effect.post (cvtpi2pdXmmMmEffect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (modrmRm modrm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvtpi2pdXmmMmEffect_components]; simp [Component.Covers]) _)
    (cvtpi2pd_xmm_mm_rex_effect_step p rex hr modrm hmod)

theorem cvtpi2pd_xmm_mm_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (src : BitVec 3) :
    Triple
      (FpPre (MmxEnterPre (Sse2Pre p))
        (cvtpi2pdXmmMmOk (dst.setWidth 5) src))
      (codeRange p (encodeCvtpi2pdXmmMm dst src))
      (Effect.post (cvtpi2pdXmmMmEffect p (encodeCvtpi2pdXmmMm dst src).length (dst.setWidth 5)
        src)) := by
  unfold encodeCvtpi2pdXmmMm
  rcases encodeGprMmx_spec 0x2A dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact cvtpi2pd_xmm_mm_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact cvtpi2pd_xmm_mm_rex_triple_of_bytes p rex hrex.rexPrefix modrm hmod

attribute [x86_compose] cvtpi2pdXmmMmEffect

@[x86_local] theorem cvtpi2pdXmmMmEffect_local {p : BitVec 64} {len : Nat}
    {dst : BitVec 5} {src : BitVec 3} :
    Effect.Local (cvtpi2pdXmmMmEffect p len dst src) := by
  effect_local [cvtpi2pdXmmMmEffect, Effect.withMmx]

end X86Proofs
