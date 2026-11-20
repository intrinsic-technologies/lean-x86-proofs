import X86Proofs.Instructions.Movq2dq.Generated.XMm.Step
import X86Proofs.Instructions.Movq2dq.Generated.XMm.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movq2dqXmmMmEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 3)
    (s : RamState) : Effect :=
  let b := (Operand.mmx src : Operand 64).read s
  ({ rip := p + BitVec.ofNat 64 len
     writes := [⟨(Operand.xmm dst : Operand 128), b.setWidth 128⟩] } : Effect).withMmx s

@[simp] theorem movq2dqXmmMmEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (src : BitVec 3) (s : RamState) :
    (movq2dqXmmMmEffect p len dst src s).components = [.xmm dst, .fsw, .ftw, .rip] := rfl

theorem movq2dq_xmm_mm_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (MmxEnterPre (Sse2Pre p))
      (codeRange p ([0xF3, 0x0F, 0xD6, modrm]))
      (movq2dqXmmMmEffect p 4 (gprNumber 0 0 (modrmReg modrm))
        (modrmRm modrm)) := by
  rintro s h hcode ⟨⟨⟨hp, hsse⟩, hfeat⟩, hes⟩
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := movq2dq_xmm_mm_step s h hsse hes hfeat [0xF3]
    (by simpa using scanPrefix_f3) (by simp)
    rfl rfl rfl rfl rfl
    modrm hmod hcode.bytesAt hlow
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx_xmm h _ _ _ _, ?_⟩
  exact mmxXmmEffect_holds h _ _ _ _ rfl

theorem movq2dq_xmm_mm_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (MmxEnterPre (Sse2Pre p))
      (codeRange p ([0xF3, 0x0F, 0xD6, modrm]))
      (Effect.post (movq2dqXmmMmEffect p 4 (gprNumber 0 0 (modrmReg modrm))
        (modrmRm modrm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movq2dqXmmMmEffect_components]; simp [Component.Covers]) _)
    (movq2dq_xmm_mm_effect_step p modrm hmod)

theorem movq2dq_xmm_mm_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (MmxEnterPre (Sse2Pre p))
      (codeRange p ([0xF3, rex, 0x0F, 0xD6, modrm]))
      (movq2dqXmmMmEffect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (modrmRm modrm)) := by
  rintro s h hcode ⟨⟨⟨hp, hsse⟩, hfeat⟩, hes⟩
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_f3_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := movq2dq_xmm_mm_step s h hsse hes hfeat [0xF3, rex]
    (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    modrm hmod hcode.bytesAt hlow
  simp only [hc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx_xmm h _ _ _ _, ?_⟩
  exact mmxXmmEffect_holds h _ _ _ _ rfl

theorem movq2dq_xmm_mm_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (MmxEnterPre (Sse2Pre p))
      (codeRange p ([0xF3, rex, 0x0F, 0xD6, modrm]))
      (Effect.post (movq2dqXmmMmEffect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (modrmRm modrm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movq2dqXmmMmEffect_components]; simp [Component.Covers]) _)
    (movq2dq_xmm_mm_rex_effect_step p rex hr modrm hmod)

theorem movq2dq_xmm_mm_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (src : BitVec 3) :
    Triple (MmxEnterPre (Sse2Pre p)) (codeRange p (encodeMovq2dqXmmMm dst src))
      (Effect.post (movq2dqXmmMmEffect p (encodeMovq2dqXmmMm dst src).length (dst.setWidth 5)
        src)) := by
  unfold encodeMovq2dqXmmMm
  rcases encodeGprMmx_spec 0xD6 dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact movq2dq_xmm_mm_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact movq2dq_xmm_mm_rex_triple_of_bytes p rex hrex.rexPrefix modrm hmod

attribute [x86_compose] movq2dqXmmMmEffect

@[x86_local] theorem movq2dqXmmMmEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 3} :
    Effect.Local (movq2dqXmmMmEffect p len dst src) := by
  effect_local [movq2dqXmmMmEffect, Effect.withMmx]

end X86Proofs
