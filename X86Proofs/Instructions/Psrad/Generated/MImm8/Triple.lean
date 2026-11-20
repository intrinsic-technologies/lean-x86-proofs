import X86Proofs.Instructions.Psrad.Generated.MImm8.Step
import X86Proofs.Instructions.Psrad.Generated.MImm8.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def psradMmImm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let a := (Operand.mmx dst : Operand 64).read s
  mmxEffect s (p + BitVec.ofNat 64 len) dst (psraMmxSpec 32 a imm.toNat)

@[simp] theorem psradMmImm8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (imm : BitVec 8) (s : RamState) :
    (psradMmImm8Effect p len dst imm s).components = [.fpr dst, .fsw, .ftw, .rip] := rfl

theorem psrad_mm_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) (imm : BitVec 8) :
    StepEffect
      (MmxPre p)
      (codeRange p (0x0F :: 0x72 :: modrm :: immBytes 8 imm))
      (psradMmImm8Effect p 4 (modrmRm modrm) imm) := by
  rintro s h hcode ⟨hp, hcr0, hes, hmmx⟩
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := psrad_mm_imm8_step s h hcr0 hes hmmx []
    (by simp) (by simp) rfl rfl rfl rfl modrm hmod hreg imm hcode.bytesAt hlow
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds h _ _ _ _ rfl

theorem psrad_mm_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) (imm : BitVec 8) :
    Triple
      (MmxPre p)
      (codeRange p (0x0F :: 0x72 :: modrm :: immBytes 8 imm))
      (Effect.post (psradMmImm8Effect p 4 (modrmRm modrm) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [psradMmImm8Effect_components]; simp [Component.Covers]) _)
    (psrad_mm_imm8_effect_step p modrm hmod hreg imm)

theorem psrad_mm_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (imm : BitVec 8) :
    Triple (MmxPre p) (codeRange p (encodePsradMmImm8 dst imm))
      (Effect.post (psradMmImm8Effect p (encodePsradMmImm8 dst imm).length dst imm)) := by
  unfold encodePsradMmImm8
  obtain ⟨modrm, hbytes, hmod, hreg, hdst⟩ := encodeMmxExtImm_spec 0x72 4 dst imm
  rw [hbytes, ← hdst]
  exact psrad_mm_imm8_triple_of_bytes p modrm hmod hreg imm

attribute [x86_compose] psradMmImm8Effect

@[x86_local] theorem psradMmImm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {imm : BitVec 8} :
    Effect.Local (psradMmImm8Effect p len dst imm) := by
  effect_local [psradMmImm8Effect, mmxEffect]

end X86Proofs
