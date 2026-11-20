import X86Proofs.Instructions.Pmovmskb.Generated.RM.Step
import X86Proofs.Instructions.Pmovmskb.Generated.RM.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def pmovmskbR32MmEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 3) (s : RamState) :
    Effect :=
  let b := (Operand.mmx src : Operand 64).read s
  ({ rip := p + BitVec.ofNat 64 len
     writes := [⟨(Operand.reg dst : Operand 64), (movmskMmxSpec b).setWidth 64⟩] } : Effect).withMmx s

@[simp] theorem pmovmskbR32MmEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (src : BitVec 3) (s : RamState) :
    (pmovmskbR32MmEffect p len dst src s).components = [.reg dst, .fsw, .ftw, .rip] := rfl

theorem pmovmskb_r32_mm_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (MmxSsePre p)
      (codeRange p ([0x0F, 0xD7, modrm]))
      (pmovmskbR32MmEffect p 3 (gprNumber 0 0 (modrmReg modrm)) (modrmRm modrm)) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hmmx⟩, hfeat⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := pmovmskb_r32_mm_step s h hcr0 hes hfeat []
    (by simp) (by simp)
    rfl rfl rfl rfl modrm hmod hcode.bytesAt hlow
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx_reg h _ _ _ _, ?_⟩
  exact mmxRegEffect_holds h _ _ _ _ rfl rfl

theorem pmovmskb_r32_mm_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (MmxSsePre p)
      (codeRange p ([0x0F, 0xD7, modrm]))
      (Effect.post (pmovmskbR32MmEffect p 3 (gprNumber 0 0 (modrmReg modrm)) (modrmRm modrm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [pmovmskbR32MmEffect_components]; simp [Component.Covers]) _)
    (pmovmskb_r32_mm_effect_step p modrm hmod)

theorem pmovmskb_r32_mm_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (MmxSsePre p)
      (codeRange p ([rex, 0x0F, 0xD7, modrm]))
      (pmovmskbR32MmEffect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) (modrmRm modrm)) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hmmx⟩, hfeat⟩
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := pmovmskb_r32_mm_step s h hcr0 hes hfeat [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) modrm hmod hcode.bytesAt hlow
  simp only [hc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx_reg h _ _ _ _, ?_⟩
  exact mmxRegEffect_holds h _ _ _ _ rfl rfl

theorem pmovmskb_r32_mm_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (MmxSsePre p)
      (codeRange p ([rex, 0x0F, 0xD7, modrm]))
      (Effect.post (pmovmskbR32MmEffect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) (modrmRm modrm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [pmovmskbR32MmEffect_components]; simp [Component.Covers]) _)
    (pmovmskb_r32_mm_rex_effect_step p rex hr modrm hmod)

theorem pmovmskb_r32_mm_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (src : BitVec 3) :
    Triple (MmxSsePre p) (codeRange p (encodePmovmskbR32Mm dst src))
      (Effect.post (pmovmskbR32MmEffect p (encodePmovmskbR32Mm dst src).length (dst.setWidth 5) src)) := by
  unfold encodePmovmskbR32Mm
  rcases encodeGprMmx_spec 0xD7 dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact pmovmskb_r32_mm_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact pmovmskb_r32_mm_rex_triple_of_bytes p rex hrex.rexPrefix modrm hmod

attribute [x86_compose] pmovmskbR32MmEffect

@[x86_local] theorem pmovmskbR32MmEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 3} :
    Effect.Local (pmovmskbR32MmEffect p len dst src) := by
  effect_local [pmovmskbR32MmEffect, Effect.withMmx]

end X86Proofs
