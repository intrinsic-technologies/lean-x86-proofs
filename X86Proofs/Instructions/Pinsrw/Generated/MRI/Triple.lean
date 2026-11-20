import X86Proofs.Instructions.Pinsrw.Generated.MRI.Step
import X86Proofs.Instructions.Pinsrw.Generated.MRI.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def pinsrwMmR32Imm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (src : BitVec 5)
    (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.mmx dst : Operand 64).read s
  let b := (Operand.reg src : Operand 32).read s
  mmxEffect s (p + BitVec.ofNat 64 len) dst (pinsrwMmxSpec a b imm)

@[simp] theorem pinsrwMmR32Imm8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (src : BitVec 5) (imm : BitVec 8) (s : RamState) :
    (pinsrwMmR32Imm8Effect p len dst src imm s).components = [.fpr dst, .fsw, .ftw, .rip] := rfl

theorem pinsrw_mm_r32_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    StepEffect
      (MmxPre p)
      (codeRange p (0x0F :: 0xC4 :: modrm :: immBytes 8 imm))
      (pinsrwMmR32Imm8Effect p 4 (modrmReg modrm)
        (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode ⟨hp, hcr0, hes, hmmx⟩
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := pinsrw_mm_r32_imm8_step s h hcr0 hes hmmx []
    (by simp) (by simp)
    rfl rfl
    rfl rfl modrm hmod imm hcode.bytesAt hlow
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds h _ _ _ _ rfl

theorem pinsrw_mm_r32_imm8_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    Triple
      (MmxPre p)
      (codeRange p (0x0F :: 0xC4 :: modrm :: immBytes 8 imm))
      (Effect.post (pinsrwMmR32Imm8Effect p 4 (modrmReg modrm)
        (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [pinsrwMmR32Imm8Effect_components]; simp [Component.Covers]) _)
    (pinsrw_mm_r32_imm8_effect_step p modrm hmod imm)

theorem pinsrw_mm_r32_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    StepEffect
      (MmxPre p)
      (codeRange p (rex :: 0x0F :: 0xC4 :: modrm :: immBytes 8 imm))
      (pinsrwMmR32Imm8Effect p 5 (modrmReg modrm)
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode ⟨hp, hcr0, hes, hmmx⟩
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := pinsrw_mm_r32_imm8_step s h hcr0 hes hmmx [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl) modrm hmod imm hcode.bytesAt hlow
  simp only [hc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds h _ _ _ _ rfl

theorem pinsrw_mm_r32_imm8_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    Triple
      (MmxPre p)
      (codeRange p (rex :: 0x0F :: 0xC4 :: modrm :: immBytes 8 imm))
      (Effect.post (pinsrwMmR32Imm8Effect p 5 (modrmReg modrm)
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [pinsrwMmR32Imm8Effect_components]; simp [Component.Covers]) _)
    (pinsrw_mm_r32_imm8_rex_effect_step p rex hr modrm hmod imm)

theorem pinsrw_mm_r32_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (src : BitVec 4)
    (imm : BitVec 8) :
    Triple (MmxPre p) (codeRange p (encodePinsrwMmR32Imm8 dst src imm))
      (Effect.post (pinsrwMmR32Imm8Effect p (encodePinsrwMmR32Imm8 dst src imm).length dst
        (src.setWidth 5) imm)) := by
  unfold encodePinsrwMmR32Imm8
  rcases encodeMmxGpr_spec 0xC4 dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact pinsrw_mm_r32_imm8_triple_of_bytes p modrm hmod imm
  · rw [hbytes, ← hdst, ← hsrc]
    exact pinsrw_mm_r32_imm8_rex_triple_of_bytes p rex hrex.rexPrefix modrm hmod imm

attribute [x86_compose] pinsrwMmR32Imm8Effect

@[x86_local] theorem pinsrwMmR32Imm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {src : BitVec 5} {imm : BitVec 8} :
    Effect.Local (pinsrwMmR32Imm8Effect p len dst src imm) := by
  effect_local [pinsrwMmR32Imm8Effect, mmxEffect]

end X86Proofs
