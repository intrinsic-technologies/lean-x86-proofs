import X86Proofs.Instructions.Pcmpgtw.Generated.MM.Step
import X86Proofs.Instructions.Pcmpgtw.Generated.MM.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def pcmpgtwMmMmEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 3) (s : RamState) : Effect :=
  let a := (Operand.mmx dst : Operand 64).read s
  let b := (Operand.mmx src : Operand 64).read s
  mmxEffect s (p + BitVec.ofNat 64 len) dst (pcmpgtMmxSpec 16 a b)

@[simp] theorem pcmpgtwMmMmEffect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 3)
    (s : RamState) : (pcmpgtwMmMmEffect p len dst src s).components = [.fpr dst, .fsw, .ftw, .rip] :=
  rfl

theorem pcmpgtw_mm_mm_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (MmxPre p)
      (codeRange p ([0x0F, 0x65, modrm]))
      (pcmpgtwMmMmEffect p 3 (modrmReg modrm) (modrmRm modrm)) := by
  rintro s h hcode ⟨hp, hcr0, hes, hmmx⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := pcmpgtw_mm_mm_step s h hcr0 hes hmmx []
    (by simp) (by simp) rfl rfl rfl rfl modrm hmod hcode.bytesAt hlow
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds h _ _ _ _ rfl

theorem pcmpgtw_mm_mm_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (MmxPre p)
      (codeRange p ([0x0F, 0x65, modrm]))
      (Effect.post (pcmpgtwMmMmEffect p 3 (modrmReg modrm) (modrmRm modrm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [pcmpgtwMmMmEffect_components]; simp [Component.Covers]) _)
    (pcmpgtw_mm_mm_effect_step p modrm hmod)

theorem pcmpgtw_mm_mm_triple [Bindings] (p : BitVec 64) (dst src : BitVec 3) :
    Triple (MmxPre p) (codeRange p (encodePcmpgtwMmMm dst src))
      (Effect.post (pcmpgtwMmMmEffect p (encodePcmpgtwMmMm dst src).length dst src)) := by
  unfold encodePcmpgtwMmMm
  obtain ⟨modrm, hbytes, hmod, hdst, hsrc⟩ := encodeMmxRegReg_spec 0x65 dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact pcmpgtw_mm_mm_triple_of_bytes p modrm hmod

attribute [x86_compose] pcmpgtwMmMmEffect

@[x86_local] theorem pcmpgtwMmMmEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {src : BitVec 3} :
    Effect.Local (pcmpgtwMmMmEffect p len dst src) := by
  effect_local [pcmpgtwMmMmEffect, mmxEffect]

end X86Proofs
