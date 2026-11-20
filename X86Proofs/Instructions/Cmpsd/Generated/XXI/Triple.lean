import X86Proofs.Instructions.Cmpsd.Generated.XXI.Step
import X86Proofs.Instructions.Cmpsd.Generated.XXI.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cmpsdXmmXmmImm8Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.xmm src : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), cmpfsSpec 64 s.MXCSR a b imm⟩,
      ⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (cmpfsFlags 64 s.MXCSR a b imm)⟩] }

def cmpsdXmmXmmImm8Ok (dst src : BitVec 5) (imm : BitVec 8) (s : RamState) : Prop :=
  cmpfsOk 64 s.MXCSR ((Operand.xmm dst : Operand 128).read s)
    ((Operand.xmm src : Operand 64).read s) imm

@[simp] theorem cmpsdXmmXmmImm8Effect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (imm : BitVec 8) (s : RamState) :
    (cmpsdXmmXmmImm8Effect p len dst src imm s).components = [.xmm dst, .mxcsr, .rip] := rfl

theorem cmpsd_xmm_xmm_imm8_effect_step [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    StepEffect
      (FpPre (Sse2Pre p) (cmpsdXmmXmmImm8Ok (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) imm))
      (codeRange p (0xF2 :: 0x0F :: 0xC2 :: modrm :: immBytes 8 imm))
      (cmpsdXmmXmmImm8Effect p 5 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) imm) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := cmpsd_xmm_xmm_imm8_step s h hpre.sse hpre.sse2 [0xF2]
    (by simpa using scanPrefix_f2) (by simp)
    rfl rfl rfl
    rfl rfl
    modrm hmod imm hcode.bytesAt hlow hm hok
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0xF2]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0xF2]).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0xF2]).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) [0xF2]).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult_xmm_mxcsr h _ _ _ _ _,
    ⟨afterStep_writeResult_xmm_mxcsr_rip h _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult_xmm_mxcsr s _ _ _ _ _⟩⟩
  refine ⟨?_, ?_⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_writeResult_xmm_mxcsr]
    simp only [afterFetches_MXCSR, beforeFetch_MXCSR]
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_writeResult_mxcsr]
    simp only [afterFetches_MXCSR, beforeFetch_MXCSR]

theorem cmpsd_xmm_xmm_imm8_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    Triple
      (FpPre (Sse2Pre p) (cmpsdXmmXmmImm8Ok (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) imm))
      (codeRange p (0xF2 :: 0x0F :: 0xC2 :: modrm :: immBytes 8 imm))
      (Effect.post (cmpsdXmmXmmImm8Effect p 5 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpsdXmmXmmImm8Effect_components]; simp [Component.Covers]) _)
    (cmpsd_xmm_xmm_imm8_effect_step p modrm hmod imm)

theorem cmpsd_xmm_xmm_imm8_rex_effect_step [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    StepEffect
      (FpPre (Sse2Pre p) (cmpsdXmmXmmImm8Ok (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm))
      (codeRange p (0xF2 :: rex :: 0x0F :: 0xC2 :: modrm :: immBytes 8 imm))
      (cmpsdXmmXmmImm8Effect p 6 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 6 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hc := scanContext_f2_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := cmpsd_xmm_xmm_imm8_step s h hpre.sse hpre.sse2 [0xF2, rex]
    (by simp [scanPrefix_f2, hr.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl)
    modrm hmod imm hcode.bytesAt hlow hm (by rw [hc]; exact hok)
  simp only [hc] at hstep
  have hdst : gprNumber (repneRexContext s.DS rex.toBitVec).rex_r4
      (repneRexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  have hsrc : gprNumber (repneRexContext s.DS rex.toBitVec).rex_b4
      (repneRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult_xmm_mxcsr h _ _ _ _ _,
    ⟨afterStep_writeResult_xmm_mxcsr_rip h _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult_xmm_mxcsr s _ _ _ _ _⟩⟩
  refine ⟨?_, ?_⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_writeResult_xmm_mxcsr]
    simp only [afterFetches_MXCSR, beforeFetch_MXCSR]
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_writeResult_mxcsr]
    simp only [afterFetches_MXCSR, beforeFetch_MXCSR]

theorem cmpsd_xmm_xmm_imm8_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    Triple
      (FpPre (Sse2Pre p) (cmpsdXmmXmmImm8Ok (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm))
      (codeRange p (0xF2 :: rex :: 0x0F :: 0xC2 :: modrm :: immBytes 8 imm))
      (Effect.post (cmpsdXmmXmmImm8Effect p 6 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpsdXmmXmmImm8Effect_components]; simp [Component.Covers]) _)
    (cmpsd_xmm_xmm_imm8_rex_effect_step p rex hr modrm hmod imm)

theorem cmpsd_xmm_xmm_imm8_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4)
    (imm : BitVec 8) :
    Triple (FpPre (Sse2Pre p) (cmpsdXmmXmmImm8Ok (dst.setWidth 5) (src.setWidth 5) imm))
      (codeRange p (encodeCmpsdXmmXmmImm8 dst src imm))
      (Effect.post (cmpsdXmmXmmImm8Effect p (encodeCmpsdXmmXmmImm8 dst src imm).length
        (dst.setWidth 5) (src.setWidth 5) imm)) := by
  unfold encodeCmpsdXmmXmmImm8
  rcases encodeSseRegReg_spec 0xC2 dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact cmpsd_xmm_xmm_imm8_triple_of_bytes p modrm hmod imm
  · rw [hbytes, ← hdst, ← hsrc]
    exact cmpsd_xmm_xmm_imm8_rex_triple_of_bytes p rex hrex modrm hmod imm

attribute [x86_compose] cmpsdXmmXmmImm8Effect

@[x86_local] theorem cmpsdXmmXmmImm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 5} {imm : BitVec 8} :
    Effect.Local (cmpsdXmmXmmImm8Effect p len dst src imm) := by
  effect_local [cmpsdXmmXmmImm8Effect]

end X86Proofs
