import X86Proofs.Instructions.Psrldq.Generated.Imm8.Step
import X86Proofs.Instructions.Psrldq.Generated.Imm8.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def psrldqXmmImm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), psrldqSpec a imm.toNat⟩] }

@[simp] theorem psrldqXmmImm8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (imm : BitVec 8) (s : RamState) :
    (psrldqXmmImm8Effect p len dst imm s).components = [.xmm dst, .rip] := rfl

theorem psrldq_xmm_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) (imm : BitVec 8) :
    StepEffect
      (Sse2Pre p)
      (codeRange p (0x66 :: 0x0F :: 0x73 :: modrm :: immBytes 8 imm))
      (psrldqXmmImm8Effect p 5
        (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode ⟨⟨hp, hsse⟩, hfeat⟩
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := psrldq_xmm_imm8_step s h hsse hfeat [0x66]
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

theorem psrldq_xmm_imm8_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) (imm : BitVec 8) :
    Triple
      (Sse2Pre p)
      (codeRange p (0x66 :: 0x0F :: 0x73 :: modrm :: immBytes 8 imm))
      (Effect.post (psrldqXmmImm8Effect p 5
        (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [psrldqXmmImm8Effect_components]; simp [Component.Covers]) _)
    (psrldq_xmm_imm8_effect_step p modrm hmod hreg imm)

theorem psrldq_xmm_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) (imm : BitVec 8) :
    StepEffect
      (Sse2Pre p)
      (codeRange p (0x66 :: rex :: 0x0F :: 0x73 :: modrm :: immBytes 8 imm))
      (psrldqXmmImm8Effect p 6
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode ⟨⟨hp, hsse⟩, hfeat⟩
  subst hp
  have hlow : s.RIP.toNat + 6 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hc := scanContext_66_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := psrldq_xmm_imm8_step s h hsse hfeat [0x66, rex]
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

theorem psrldq_xmm_imm8_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) (imm : BitVec 8) :
    Triple
      (Sse2Pre p)
      (codeRange p (0x66 :: rex :: 0x0F :: 0x73 :: modrm :: immBytes 8 imm))
      (Effect.post (psrldqXmmImm8Effect p 6
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [psrldqXmmImm8Effect_components]; simp [Component.Covers]) _)
    (psrldq_xmm_imm8_rex_effect_step p rex hr modrm hmod hreg imm)

theorem psrldq_xmm_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (Sse2Pre p) (codeRange p (encodePsrldqXmmImm8 dst imm))
      (Effect.post (psrldqXmmImm8Effect p (encodePsrldqXmmImm8 dst imm).length
        (dst.setWidth 5) imm)) := by
  unfold encodePsrldqXmmImm8
  rcases encodeSseExtImm_spec 0x73 imm 3 dst with
    ⟨modrm, hbytes, hmod, hreg, hdst⟩ | ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact psrldq_xmm_imm8_triple_of_bytes p modrm hmod hreg imm
  · rw [hbytes, ← hdst]
    exact psrldq_xmm_imm8_rex_triple_of_bytes p rex hrex modrm hmod hreg imm

attribute [x86_compose] psrldqXmmImm8Effect

@[x86_local] theorem psrldqXmmImm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {imm : BitVec 8} : Effect.Local (psrldqXmmImm8Effect p len dst imm) := by
  effect_local [psrldqXmmImm8Effect]

end X86Proofs
