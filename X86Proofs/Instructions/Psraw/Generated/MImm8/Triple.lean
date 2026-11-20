import X86Proofs.Instructions.Psraw.Generated.MImm8.Step
import X86Proofs.Instructions.Psraw.Generated.MImm8.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def psrawMmImm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let a := (Operand.mmx dst : Operand 64).read s
  mmxEffect s (p + BitVec.ofNat 64 len) dst (psraMmxSpec 16 a imm.toNat)

@[simp] theorem psrawMmImm8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (imm : BitVec 8) (s : RamState) :
    (psrawMmImm8Effect p len dst imm s).components = [.fpr dst, .fsw, .ftw, .rip] := rfl

theorem psraw_mm_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) (imm : BitVec 8) :
    StepEffect
      (MmxPre p)
      (codeRange p (0x0F :: 0x71 :: modrm :: immBytes 8 imm))
      (psrawMmImm8Effect p 4 (modrmRm modrm) imm) := by
  rintro s h hcode ⟨hp, hcr0, hes, hmmx⟩
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := psraw_mm_imm8_step s h hcr0 hes hmmx []
    (by simp) (by simp) rfl rfl rfl rfl modrm hmod hreg imm hcode.bytesAt hlow
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds h _ _ _ _ rfl

theorem psraw_mm_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) (imm : BitVec 8) :
    Triple
      (MmxPre p)
      (codeRange p (0x0F :: 0x71 :: modrm :: immBytes 8 imm))
      (Effect.post (psrawMmImm8Effect p 4 (modrmRm modrm) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [psrawMmImm8Effect_components]; simp [Component.Covers]) _)
    (psraw_mm_imm8_effect_step p modrm hmod hreg imm)

theorem psraw_mm_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (imm : BitVec 8) :
    Triple (MmxPre p) (codeRange p (encodePsrawMmImm8 dst imm))
      (Effect.post (psrawMmImm8Effect p (encodePsrawMmImm8 dst imm).length dst imm)) := by
  unfold encodePsrawMmImm8
  obtain ⟨modrm, hbytes, hmod, hreg, hdst⟩ := encodeMmxExtImm_spec 0x71 4 dst imm
  rw [hbytes, ← hdst]
  exact psraw_mm_imm8_triple_of_bytes p modrm hmod hreg imm

attribute [x86_compose] psrawMmImm8Effect

@[x86_local] theorem psrawMmImm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {imm : BitVec 8} :
    Effect.Local (psrawMmImm8Effect p len dst imm) := by
  effect_local [psrawMmImm8Effect, mmxEffect]

end X86Proofs
