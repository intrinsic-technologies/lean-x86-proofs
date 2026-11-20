import X86Proofs.Instructions.Pextrw.Generated.RMI.Step
import X86Proofs.Instructions.Pextrw.Generated.RMI.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def pextrwR32MmImm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 3)
    (imm : BitVec 8) (s : RamState) : Effect :=
  let b := (Operand.mmx src : Operand 64).read s
  ({ rip := p + BitVec.ofNat 64 len
     writes := [⟨(Operand.reg dst : Operand 64), (pextrwMmxSpec b imm).setWidth 64⟩] } :
    Effect).withMmx s

@[simp] theorem pextrwR32MmImm8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (src : BitVec 3) (imm : BitVec 8) (s : RamState) :
    (pextrwR32MmImm8Effect p len dst src imm s).components = [.reg dst, .fsw, .ftw, .rip] := rfl

theorem pextrw_r32_mm_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    StepEffect
      (MmxPre p)
      (codeRange p (0x0F :: 0xC5 :: modrm :: immBytes 8 imm))
      (pextrwR32MmImm8Effect p 4 (gprNumber 0 0 (modrmReg modrm))
        (modrmRm modrm) imm) := by
  rintro s h hcode ⟨hp, hcr0, hes, hmmx⟩
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := pextrw_r32_mm_imm8_step s h hcr0 hes hmmx []
    (by simp) (by simp)
    rfl rfl
    rfl rfl modrm hmod imm hcode.bytesAt hlow
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx_reg h _ _ _ _, ?_⟩
  exact mmxRegEffect_holds h _ _ _ _ rfl rfl

theorem pextrw_r32_mm_imm8_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    Triple
      (MmxPre p)
      (codeRange p (0x0F :: 0xC5 :: modrm :: immBytes 8 imm))
      (Effect.post (pextrwR32MmImm8Effect p 4 (gprNumber 0 0 (modrmReg modrm))
        (modrmRm modrm) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [pextrwR32MmImm8Effect_components]; simp [Component.Covers]) _)
    (pextrw_r32_mm_imm8_effect_step p modrm hmod imm)

theorem pextrw_r32_mm_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    StepEffect
      (MmxPre p)
      (codeRange p (rex :: 0x0F :: 0xC5 :: modrm :: immBytes 8 imm))
      (pextrwR32MmImm8Effect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (modrmRm modrm) imm) := by
  rintro s h hcode ⟨hp, hcr0, hes, hmmx⟩
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := pextrw_r32_mm_imm8_step s h hcr0 hes hmmx [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl) modrm hmod imm hcode.bytesAt hlow
  simp only [hc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx_reg h _ _ _ _, ?_⟩
  exact mmxRegEffect_holds h _ _ _ _ rfl rfl

theorem pextrw_r32_mm_imm8_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    Triple
      (MmxPre p)
      (codeRange p (rex :: 0x0F :: 0xC5 :: modrm :: immBytes 8 imm))
      (Effect.post (pextrwR32MmImm8Effect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (modrmRm modrm) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [pextrwR32MmImm8Effect_components]; simp [Component.Covers]) _)
    (pextrw_r32_mm_imm8_rex_effect_step p rex hr modrm hmod imm)

theorem pextrw_r32_mm_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (src : BitVec 3)
    (imm : BitVec 8) :
    Triple (MmxPre p) (codeRange p (encodePextrwR32MmImm8 dst src imm))
      (Effect.post (pextrwR32MmImm8Effect p (encodePextrwR32MmImm8 dst src imm).length
        (dst.setWidth 5) src imm)) := by
  unfold encodePextrwR32MmImm8
  rcases encodeGprMmx_spec 0xC5 dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact pextrw_r32_mm_imm8_triple_of_bytes p modrm hmod imm
  · rw [hbytes, ← hdst, ← hsrc]
    exact pextrw_r32_mm_imm8_rex_triple_of_bytes p rex hrex.rexPrefix modrm hmod imm

attribute [x86_compose] pextrwR32MmImm8Effect

@[x86_local] theorem pextrwR32MmImm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 3} {imm : BitVec 8} :
    Effect.Local (pextrwR32MmImm8Effect p len dst src imm) := by
  effect_local [pextrwR32MmImm8Effect, Effect.withMmx]

end X86Proofs
