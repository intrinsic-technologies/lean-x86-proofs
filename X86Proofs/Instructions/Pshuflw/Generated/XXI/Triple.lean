import X86Proofs.Instructions.Pshuflw.Generated.XXI.Step
import X86Proofs.Instructions.Pshuflw.Generated.XXI.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def pshuflwXmmXmmImm8Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let b := (Operand.xmm src : Operand 128).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), pshuflwSpec b imm⟩] }

@[simp] theorem pshuflwXmmXmmImm8Effect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (imm : BitVec 8) (s : RamState) :
    (pshuflwXmmXmmImm8Effect p len dst src imm s).components = [.xmm dst, .rip] := rfl

theorem pshuflw_xmm_xmm_imm8_effect_step [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    StepEffect
      (Sse2Pre p)
      (codeRange p (0xF2 :: 0x0F :: 0x70 :: modrm :: immBytes 8 imm))
      (pshuflwXmmXmmImm8Effect p 5 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode ⟨⟨hp, hsse⟩, hfeat⟩
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := pshuflw_xmm_xmm_imm8_step s h hsse hfeat [0xF2]
    (by simpa using scanPrefix_f2) (by simp)
    rfl rfl rfl
    rfl rfl
    modrm hmod imm hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0xF2]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0xF2]).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0xF2]).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) [0xF2]).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult_xmm h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_writeResult_xmm]

theorem pshuflw_xmm_xmm_imm8_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    Triple
      (Sse2Pre p)
      (codeRange p (0xF2 :: 0x0F :: 0x70 :: modrm :: immBytes 8 imm))
      (Effect.post (pshuflwXmmXmmImm8Effect p 5 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [pshuflwXmmXmmImm8Effect_components]; simp [Component.Covers]) _)
    (pshuflw_xmm_xmm_imm8_effect_step p modrm hmod imm)

theorem pshuflw_xmm_xmm_imm8_rex_effect_step [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    StepEffect
      (Sse2Pre p)
      (codeRange p (0xF2 :: rex :: 0x0F :: 0x70 :: modrm :: immBytes 8 imm))
      (pshuflwXmmXmmImm8Effect p 6 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode ⟨⟨hp, hsse⟩, hfeat⟩
  subst hp
  have hlow : s.RIP.toNat + 6 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hc := scanContext_f2_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := pshuflw_xmm_xmm_imm8_step s h hsse hfeat [0xF2, rex]
    (by simp [scanPrefix_f2, hr.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl)
    modrm hmod imm hcode.bytesAt hlow
  simp only [hc] at hstep
  have hdst : gprNumber (repneRexContext s.DS rex.toBitVec).rex_r4
      (repneRexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  have hsrc : gprNumber (repneRexContext s.DS rex.toBitVec).rex_b4
      (repneRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult_xmm h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_writeResult_xmm]

theorem pshuflw_xmm_xmm_imm8_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    Triple
      (Sse2Pre p)
      (codeRange p (0xF2 :: rex :: 0x0F :: 0x70 :: modrm :: immBytes 8 imm))
      (Effect.post (pshuflwXmmXmmImm8Effect p 6 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [pshuflwXmmXmmImm8Effect_components]; simp [Component.Covers]) _)
    (pshuflw_xmm_xmm_imm8_rex_effect_step p rex hr modrm hmod imm)

theorem pshuflw_xmm_xmm_imm8_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4)
    (imm : BitVec 8) :
    Triple (Sse2Pre p) (codeRange p (encodePshuflwXmmXmmImm8 dst src imm))
      (Effect.post (pshuflwXmmXmmImm8Effect p (encodePshuflwXmmXmmImm8 dst src imm).length
        (dst.setWidth 5) (src.setWidth 5) imm)) := by
  unfold encodePshuflwXmmXmmImm8
  rcases encodeSseRegReg_spec 0x70 dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact pshuflw_xmm_xmm_imm8_triple_of_bytes p modrm hmod imm
  · rw [hbytes, ← hdst, ← hsrc]
    exact pshuflw_xmm_xmm_imm8_rex_triple_of_bytes p rex hrex modrm hmod imm

attribute [x86_compose] pshuflwXmmXmmImm8Effect

@[x86_local] theorem pshuflwXmmXmmImm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 5} {imm : BitVec 8} :
    Effect.Local (pshuflwXmmXmmImm8Effect p len dst src imm) := by
  effect_local [pshuflwXmmXmmImm8Effect]

end X86Proofs
