import X86Proofs.Instructions.Pmulhuw.Generated.MM.Step
import X86Proofs.Instructions.Pmulhuw.Generated.MM.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def pmulhuwMmMmEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 3) (s : RamState) : Effect :=
  let a := (Operand.mmx dst : Operand 64).read s
  let b := (Operand.mmx src : Operand 64).read s
  mmxEffect s (p + BitVec.ofNat 64 len) dst (pmulhuwMmxSpec a b)

@[simp] theorem pmulhuwMmMmEffect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 3)
    (s : RamState) : (pmulhuwMmMmEffect p len dst src s).components = [.fpr dst, .fsw, .ftw, .rip] :=
  rfl

theorem pmulhuw_mm_mm_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (MmxPre p)
      (codeRange p ([0x0F, 0xE4, modrm]))
      (pmulhuwMmMmEffect p 3 (modrmReg modrm) (modrmRm modrm)) := by
  rintro s h hcode ⟨hp, hcr0, hes, hmmx⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := pmulhuw_mm_mm_step s h hcr0 hes hmmx []
    (by simp) (by simp) rfl rfl rfl rfl modrm hmod hcode.bytesAt hlow
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds h _ _ _ _ rfl

theorem pmulhuw_mm_mm_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (MmxPre p)
      (codeRange p ([0x0F, 0xE4, modrm]))
      (Effect.post (pmulhuwMmMmEffect p 3 (modrmReg modrm) (modrmRm modrm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [pmulhuwMmMmEffect_components]; simp [Component.Covers]) _)
    (pmulhuw_mm_mm_effect_step p modrm hmod)

theorem pmulhuw_mm_mm_triple [Bindings] (p : BitVec 64) (dst src : BitVec 3) :
    Triple (MmxPre p) (codeRange p (encodePmulhuwMmMm dst src))
      (Effect.post (pmulhuwMmMmEffect p (encodePmulhuwMmMm dst src).length dst src)) := by
  unfold encodePmulhuwMmMm
  obtain ⟨modrm, hbytes, hmod, hdst, hsrc⟩ := encodeMmxRegReg_spec 0xE4 dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact pmulhuw_mm_mm_triple_of_bytes p modrm hmod

attribute [x86_compose] pmulhuwMmMmEffect

@[x86_local] theorem pmulhuwMmMmEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {src : BitVec 3} :
    Effect.Local (pmulhuwMmMmEffect p len dst src) := by
  effect_local [pmulhuwMmMmEffect, mmxEffect]

end X86Proofs
