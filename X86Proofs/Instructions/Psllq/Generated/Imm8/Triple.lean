import X86Proofs.Instructions.Psllq.Generated.Imm8.Step
import X86Proofs.Instructions.Psllq.Generated.Imm8.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def psllqXmmImm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), psllSpec 64 a imm.toNat⟩] }

@[simp] theorem psllqXmmImm8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (imm : BitVec 8) (s : RamState) :
    (psllqXmmImm8Effect p len dst imm s).components = [.xmm dst, .rip] := rfl

theorem psllq_xmm_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) (imm : BitVec 8) :
    StepEffect
      (Sse2Pre p)
      (codeRange p (0x66 :: 0x0F :: 0x73 :: modrm :: immBytes 8 imm))
      (psllqXmmImm8Effect p 5
        (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode ⟨⟨hp, hsse⟩, hfeat⟩
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := psllq_xmm_imm8_step s h hsse hfeat [0x66]
    (by simpa using scanPrefix_66) (by simp)
    rfl rfl rfl
    rfl rfl rfl modrm hmod hreg imm hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult_xmm h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_writeResult_xmm]

theorem psllq_xmm_imm8_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) (imm : BitVec 8) :
    Triple
      (Sse2Pre p)
      (codeRange p (0x66 :: 0x0F :: 0x73 :: modrm :: immBytes 8 imm))
      (Effect.post (psllqXmmImm8Effect p 5
        (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [psllqXmmImm8Effect_components]; simp [Component.Covers]) _)
    (psllq_xmm_imm8_effect_step p modrm hmod hreg imm)

theorem psllq_xmm_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) (imm : BitVec 8) :
    StepEffect
      (Sse2Pre p)
      (codeRange p (0x66 :: rex :: 0x0F :: 0x73 :: modrm :: immBytes 8 imm))
      (psllqXmmImm8Effect p 6
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode ⟨⟨hp, hsse⟩, hfeat⟩
  subst hp
  have hlow : s.RIP.toNat + 6 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hc := scanContext_66_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := psllq_xmm_imm8_step s h hsse hfeat [0x66, rex]
    (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl) modrm hmod hreg imm hcode.bytesAt hlow
  simp only [hc] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_b4
      (oszRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult_xmm h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_writeResult_xmm]

theorem psllq_xmm_imm8_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) (imm : BitVec 8) :
    Triple
      (Sse2Pre p)
      (codeRange p (0x66 :: rex :: 0x0F :: 0x73 :: modrm :: immBytes 8 imm))
      (Effect.post (psllqXmmImm8Effect p 6
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [psllqXmmImm8Effect_components]; simp [Component.Covers]) _)
    (psllq_xmm_imm8_rex_effect_step p rex hr modrm hmod hreg imm)

theorem psllq_xmm_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (Sse2Pre p) (codeRange p (encodePsllqXmmImm8 dst imm))
      (Effect.post (psllqXmmImm8Effect p (encodePsllqXmmImm8 dst imm).length
        (dst.setWidth 5) imm)) := by
  unfold encodePsllqXmmImm8
  rcases encodeSseExtImm_spec 0x73 imm 6 dst with
    ⟨modrm, hbytes, hmod, hreg, hdst⟩ | ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact psllq_xmm_imm8_triple_of_bytes p modrm hmod hreg imm
  · rw [hbytes, ← hdst]
    exact psllq_xmm_imm8_rex_triple_of_bytes p rex hrex modrm hmod hreg imm

attribute [x86_compose] psllqXmmImm8Effect

@[x86_local] theorem psllqXmmImm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {imm : BitVec 8} : Effect.Local (psllqXmmImm8Effect p len dst imm) := by
  effect_local [psllqXmmImm8Effect]

end X86Proofs
