import X86Proofs.Instructions.Movdq2q.Generated.MmX.Step
import X86Proofs.Instructions.Movdq2q.Generated.MmX.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movdq2qMmXmmEffect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (src : BitVec 5)
    (s : RamState) : Effect :=
  mmxEffect s (p + BitVec.ofNat 64 len) dst ((Operand.xmm src : Operand 64).read s)

@[simp] theorem movdq2qMmXmmEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (src : BitVec 5) (s : RamState) :
    (movdq2qMmXmmEffect p len dst src s).components = [.fpr dst, .fsw, .ftw, .rip] := rfl

theorem movdq2q_mm_xmm_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (MmxEnterPre (Sse2Pre p))
      (codeRange p ([0xF2, 0x0F, 0xD6, modrm]))
      (movdq2qMmXmmEffect p 4 (modrmReg modrm)
        (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode ⟨⟨⟨hp, hsse⟩, hfeat⟩, hes⟩
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := movdq2q_mm_xmm_step s h hsse hes hfeat [0xF2]
    (by simpa using scanPrefix_f2) (by simp)
    rfl rfl rfl rfl
    modrm hmod hcode.bytesAt hlow
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds h _ _ _ _ rfl

theorem movdq2q_mm_xmm_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (MmxEnterPre (Sse2Pre p))
      (codeRange p ([0xF2, 0x0F, 0xD6, modrm]))
      (Effect.post (movdq2qMmXmmEffect p 4 (modrmReg modrm)
        (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movdq2qMmXmmEffect_components]; simp [Component.Covers]) _)
    (movdq2q_mm_xmm_effect_step p modrm hmod)

theorem movdq2q_mm_xmm_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (MmxEnterPre (Sse2Pre p))
      (codeRange p ([0xF2, rex, 0x0F, 0xD6, modrm]))
      (movdq2qMmXmmEffect p 5 (modrmReg modrm)
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode ⟨⟨⟨hp, hsse⟩, hfeat⟩, hes⟩
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_f2_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := movdq2q_mm_xmm_step s h hsse hes hfeat [0xF2, rex]
    (by simp [scanPrefix_f2, hr.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    modrm hmod hcode.bytesAt hlow
  simp only [hc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds h _ _ _ _ rfl

theorem movdq2q_mm_xmm_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (MmxEnterPre (Sse2Pre p))
      (codeRange p ([0xF2, rex, 0x0F, 0xD6, modrm]))
      (Effect.post (movdq2qMmXmmEffect p 5 (modrmReg modrm)
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movdq2qMmXmmEffect_components]; simp [Component.Covers]) _)
    (movdq2q_mm_xmm_rex_effect_step p rex hr modrm hmod)

theorem movdq2q_mm_xmm_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (src : BitVec 4) :
    Triple (MmxEnterPre (Sse2Pre p)) (codeRange p (encodeMovdq2qMmXmm dst src))
      (Effect.post (movdq2qMmXmmEffect p (encodeMovdq2qMmXmm dst src).length dst
        (src.setWidth 5))) := by
  unfold encodeMovdq2qMmXmm
  rcases encodeMmxGpr_spec 0xD6 dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact movdq2q_mm_xmm_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact movdq2q_mm_xmm_rex_triple_of_bytes p rex hrex.rexPrefix modrm hmod

attribute [x86_compose] movdq2qMmXmmEffect

@[x86_local] theorem movdq2qMmXmmEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {src : BitVec 5} :
    Effect.Local (movdq2qMmXmmEffect p len dst src) := by
  effect_local [movdq2qMmXmmEffect, mmxEffect]

end X86Proofs
