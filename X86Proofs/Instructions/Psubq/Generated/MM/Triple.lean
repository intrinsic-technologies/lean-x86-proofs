import X86Proofs.Instructions.Psubq.Generated.MM.Step
import X86Proofs.Instructions.Psubq.Generated.MM.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def psubqMmMmEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 3) (s : RamState) : Effect :=
  let a := (Operand.mmx dst : Operand 64).read s
  let b := (Operand.mmx src : Operand 64).read s
  mmxEffect s (p + BitVec.ofNat 64 len) dst (psubMmxSpec 64 a b)

@[simp] theorem psubqMmMmEffect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 3)
    (s : RamState) : (psubqMmMmEffect p len dst src s).components = [.fpr dst, .fsw, .ftw, .rip] :=
  rfl

theorem psubq_mm_mm_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (MmxSse2Pre p)
      (codeRange p ([0x0F, 0xFB, modrm]))
      (psubqMmMmEffect p 3 (modrmReg modrm) (modrmRm modrm)) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hmmx⟩, hsse2⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := psubq_mm_mm_step s h hcr0 hes hmmx hsse2 []
    (by simp) (by simp) rfl rfl rfl rfl modrm hmod hcode.bytesAt hlow
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds h _ _ _ _ rfl

theorem psubq_mm_mm_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (MmxSse2Pre p)
      (codeRange p ([0x0F, 0xFB, modrm]))
      (Effect.post (psubqMmMmEffect p 3 (modrmReg modrm) (modrmRm modrm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [psubqMmMmEffect_components]; simp [Component.Covers]) _)
    (psubq_mm_mm_effect_step p modrm hmod)

theorem psubq_mm_mm_triple [Bindings] (p : BitVec 64) (dst src : BitVec 3) :
    Triple (MmxSse2Pre p) (codeRange p (encodePsubqMmMm dst src))
      (Effect.post (psubqMmMmEffect p (encodePsubqMmMm dst src).length dst src)) := by
  unfold encodePsubqMmMm
  obtain ⟨modrm, hbytes, hmod, hdst, hsrc⟩ := encodeMmxRegReg_spec 0xFB dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact psubq_mm_mm_triple_of_bytes p modrm hmod

attribute [x86_compose] psubqMmMmEffect

@[x86_local] theorem psubqMmMmEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {src : BitVec 3} :
    Effect.Local (psubqMmMmEffect p len dst src) := by
  effect_local [psubqMmMmEffect, mmxEffect]

end X86Proofs
