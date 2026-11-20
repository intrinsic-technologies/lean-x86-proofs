import X86Proofs.Instructions.Shufps.Generated.XXI.Step
import X86Proofs.Instructions.Shufps.Generated.XXI.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def shufpsXmmXmmImm8Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.xmm src : Operand 128).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), shufpsSpec a b imm⟩] }

@[simp] theorem shufpsXmmXmmImm8Effect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (imm : BitVec 8) (s : RamState) :
    (shufpsXmmXmmImm8Effect p len dst src imm s).components = [.xmm dst, .rip] := rfl

theorem shufps_xmm_xmm_imm8_effect_step [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    StepEffect
      (SsePre p)
      (codeRange p (0x0F :: 0xC6 :: modrm :: immBytes 8 imm))
      (shufpsXmmXmmImm8Effect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode ⟨hp, hsse⟩
  have hfeat := hsse.feature
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := shufps_xmm_xmm_imm8_step s h hsse hfeat []
    (by simp) (by simp)
    rfl rfl rfl
    rfl rfl rfl
    modrm hmod imm hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult_xmm h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_writeResult_xmm]

theorem shufps_xmm_xmm_imm8_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    Triple
      (SsePre p)
      (codeRange p (0x0F :: 0xC6 :: modrm :: immBytes 8 imm))
      (Effect.post (shufpsXmmXmmImm8Effect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [shufpsXmmXmmImm8Effect_components]; simp [Component.Covers]) _)
    (shufps_xmm_xmm_imm8_effect_step p modrm hmod imm)

theorem shufps_xmm_xmm_imm8_rex_effect_step [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    StepEffect
      (SsePre p)
      (codeRange p (rex :: 0x0F :: 0xC6 :: modrm :: immBytes 8 imm))
      (shufpsXmmXmmImm8Effect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode ⟨hp, hsse⟩
  have hfeat := hsse.feature
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := shufps_xmm_xmm_imm8_step s h hsse hfeat [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    modrm hmod imm hcode.bytesAt hlow
  simp only [hc] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult_xmm h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_writeResult_xmm]

theorem shufps_xmm_xmm_imm8_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    Triple
      (SsePre p)
      (codeRange p (rex :: 0x0F :: 0xC6 :: modrm :: immBytes 8 imm))
      (Effect.post (shufpsXmmXmmImm8Effect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [shufpsXmmXmmImm8Effect_components]; simp [Component.Covers]) _)
    (shufps_xmm_xmm_imm8_rex_effect_step p rex hr modrm hmod imm)

theorem shufps_xmm_xmm_imm8_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4)
    (imm : BitVec 8) :
    Triple (SsePre p) (codeRange p (encodeShufpsXmmXmmImm8 dst src imm))
      (Effect.post (shufpsXmmXmmImm8Effect p (encodeShufpsXmmXmmImm8 dst src imm).length
        (dst.setWidth 5) (src.setWidth 5) imm)) := by
  unfold encodeShufpsXmmXmmImm8
  rcases encodeSseRegReg_spec 0xC6 dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact shufps_xmm_xmm_imm8_triple_of_bytes p modrm hmod imm
  · rw [hbytes, ← hdst, ← hsrc]
    exact shufps_xmm_xmm_imm8_rex_triple_of_bytes p rex hrex modrm hmod imm

attribute [x86_compose] shufpsXmmXmmImm8Effect

@[x86_local] theorem shufpsXmmXmmImm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 5} {imm : BitVec 8} :
    Effect.Local (shufpsXmmXmmImm8Effect p len dst src imm) := by
  effect_local [shufpsXmmXmmImm8Effect]

end X86Proofs
