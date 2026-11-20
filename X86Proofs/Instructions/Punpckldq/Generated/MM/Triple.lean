import X86Proofs.Instructions.Punpckldq.Generated.MM.Step
import X86Proofs.Instructions.Punpckldq.Generated.MM.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def punpckldqMmMmEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 3) (s : RamState) : Effect :=
  let a := (Operand.mmx dst : Operand 64).read s
  let b := (Operand.mmx src : Operand 64).read s
  mmxEffect s (p + BitVec.ofNat 64 len) dst (punpcklMmxSpec 32 a b)

@[simp] theorem punpckldqMmMmEffect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 3)
    (s : RamState) : (punpckldqMmMmEffect p len dst src s).components = [.fpr dst, .fsw, .ftw, .rip] :=
  rfl

theorem punpckldq_mm_mm_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (MmxPre p)
      (codeRange p ([0x0F, 0x62, modrm]))
      (punpckldqMmMmEffect p 3 (modrmReg modrm) (modrmRm modrm)) := by
  rintro s h hcode ⟨hp, hcr0, hes, hmmx⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := punpckldq_mm_mm_step s h hcr0 hes hmmx []
    (by simp) (by simp) rfl rfl rfl rfl modrm hmod hcode.bytesAt hlow
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds h _ _ _ _ rfl

theorem punpckldq_mm_mm_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (MmxPre p)
      (codeRange p ([0x0F, 0x62, modrm]))
      (Effect.post (punpckldqMmMmEffect p 3 (modrmReg modrm) (modrmRm modrm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [punpckldqMmMmEffect_components]; simp [Component.Covers]) _)
    (punpckldq_mm_mm_effect_step p modrm hmod)

theorem punpckldq_mm_mm_triple [Bindings] (p : BitVec 64) (dst src : BitVec 3) :
    Triple (MmxPre p) (codeRange p (encodePunpckldqMmMm dst src))
      (Effect.post (punpckldqMmMmEffect p (encodePunpckldqMmMm dst src).length dst src)) := by
  unfold encodePunpckldqMmMm
  obtain ⟨modrm, hbytes, hmod, hdst, hsrc⟩ := encodeMmxRegReg_spec 0x62 dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact punpckldq_mm_mm_triple_of_bytes p modrm hmod

attribute [x86_compose] punpckldqMmMmEffect

@[x86_local] theorem punpckldqMmMmEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {src : BitVec 3} :
    Effect.Local (punpckldqMmMmEffect p len dst src) := by
  effect_local [punpckldqMmMmEffect, mmxEffect]

end X86Proofs
