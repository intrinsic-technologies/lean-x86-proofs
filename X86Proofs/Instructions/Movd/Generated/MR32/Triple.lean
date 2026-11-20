import X86Proofs.Instructions.Movd.Generated.MR32.Step
import X86Proofs.Instructions.Movd.Generated.MR32.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movdMmR32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (src : BitVec 5) (s : RamState) :
    Effect :=
  let b := (Operand.reg src : Operand 32).read s
  mmxEffect s (p + BitVec.ofNat 64 len) dst (movdSpec 32 64 b)

@[simp] theorem movdMmR32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (src : BitVec 5) (s : RamState) :
    (movdMmR32Effect p len dst src s).components = [.fpr dst, .fsw, .ftw, .rip] := rfl

theorem movd_mm_r32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (MmxPre p)
      (codeRange p ([0x0F, 0x6E, modrm]))
      (movdMmR32Effect p 3 (modrmReg modrm) (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode ⟨hp, hcr0, hes, hmmx⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := movd_mm_r32_step s h hcr0 hes hmmx []
    (by simp) (by simp)
    rfl rfl rfl rfl rfl modrm hmod hcode.bytesAt hlow
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds h _ _ _ _ rfl

theorem movd_mm_r32_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (MmxPre p)
      (codeRange p ([0x0F, 0x6E, modrm]))
      (Effect.post (movdMmR32Effect p 3 (modrmReg modrm) (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movdMmR32Effect_components]; simp [Component.Covers]) _)
    (movd_mm_r32_effect_step p modrm hmod)

theorem movd_mm_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (MmxPre p)
      (codeRange p ([rex, 0x0F, 0x6E, modrm]))
      (movdMmR32Effect p 4 (modrmReg modrm) (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode ⟨hp, hcr0, hes, hmmx⟩
  subst hp
  have hr := hrex.rexPrefix
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := movd_mm_r32_step s h hcr0 hes hmmx [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; exact hrex.rex_w s.DS) modrm hmod hcode.bytesAt hlow
  simp only [hc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds h _ _ _ _ rfl

theorem movd_mm_r32_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (MmxPre p)
      (codeRange p ([rex, 0x0F, 0x6E, modrm]))
      (Effect.post (movdMmR32Effect p 4 (modrmReg modrm) (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movdMmR32Effect_components]; simp [Component.Covers]) _)
    (movd_mm_r32_rex_effect_step p rex hrex modrm hmod)

theorem movd_mm_r32_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (src : BitVec 4) :
    Triple (MmxPre p) (codeRange p (encodeMovdMmR32 dst src))
      (Effect.post (movdMmR32Effect p (encodeMovdMmR32 dst src).length dst (src.setWidth 5))) := by
  unfold encodeMovdMmR32
  rcases encodeMmxGpr_spec 0x6E dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact movd_mm_r32_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact movd_mm_r32_rex_triple_of_bytes p rex hrex modrm hmod

attribute [x86_compose] movdMmR32Effect

@[x86_local] theorem movdMmR32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {src : BitVec 5} :
    Effect.Local (movdMmR32Effect p len dst src) := by
  effect_local [movdMmR32Effect, mmxEffect]

end X86Proofs
