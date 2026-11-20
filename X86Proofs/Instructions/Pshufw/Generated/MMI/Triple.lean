import X86Proofs.Instructions.Pshufw.Generated.MMI.Step
import X86Proofs.Instructions.Pshufw.Generated.MMI.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def pshufwMmMmImm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (src : BitVec 3)
    (imm : BitVec 8) (s : RamState) : Effect :=
  let b := (Operand.mmx src : Operand 64).read s
  mmxEffect s (p + BitVec.ofNat 64 len) dst (pshufwSpec b imm)

@[simp] theorem pshufwMmMmImm8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (src : BitVec 3) (imm : BitVec 8) (s : RamState) :
    (pshufwMmMmImm8Effect p len dst src imm s).components = [.fpr dst, .fsw, .ftw, .rip] := rfl

theorem pshufw_mm_mm_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    StepEffect
      (MmxPre p)
      (codeRange p (0x0F :: 0x70 :: modrm :: immBytes 8 imm))
      (pshufwMmMmImm8Effect p 4 (modrmReg modrm)
        (modrmRm modrm) imm) := by
  rintro s h hcode ⟨hp, hcr0, hes, hmmx⟩
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := pshufw_mm_mm_imm8_step s h hcr0 hes hmmx []
    (by simp) (by simp)
    rfl rfl
    rfl rfl modrm hmod imm hcode.bytesAt hlow
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds h _ _ _ _ rfl

theorem pshufw_mm_mm_imm8_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    Triple
      (MmxPre p)
      (codeRange p (0x0F :: 0x70 :: modrm :: immBytes 8 imm))
      (Effect.post (pshufwMmMmImm8Effect p 4 (modrmReg modrm)
        (modrmRm modrm) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [pshufwMmMmImm8Effect_components]; simp [Component.Covers]) _)
    (pshufw_mm_mm_imm8_effect_step p modrm hmod imm)

theorem pshufw_mm_mm_imm8_triple [Bindings] (p : BitVec 64) (dst src : BitVec 3)
    (imm : BitVec 8) :
    Triple (MmxPre p) (codeRange p (encodePshufwMmMmImm8 dst src imm))
      (Effect.post (pshufwMmMmImm8Effect p (encodePshufwMmMmImm8 dst src imm).length dst src
        imm)) := by
  unfold encodePshufwMmMmImm8
  obtain ⟨modrm, hbytes, hmod, hdst, hsrc⟩ := encodeMmxRegReg_spec 0x70 dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact pshufw_mm_mm_imm8_triple_of_bytes p modrm hmod imm

attribute [x86_compose] pshufwMmMmImm8Effect

@[x86_local] theorem pshufwMmMmImm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {src : BitVec 3} {imm : BitVec 8} :
    Effect.Local (pshufwMmMmImm8Effect p len dst src imm) := by
  effect_local [pshufwMmMmImm8Effect, mmxEffect]

end X86Proofs
