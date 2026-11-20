import X86Proofs.Instructions.Cvtsi2sd.Generated.XR64.Step
import X86Proofs.Instructions.Cvtsi2sd.Generated.XR64.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cvtsi2sdXmmR64Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) :
    Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.reg src : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), cvtsi2sSpec 64 64 s.MXCSR a b⟩,
      ⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (cvtsi2sFlags 64 64 s.MXCSR a b)⟩] }

def cvtsi2sdXmmR64Ok (dst src : BitVec 5) (s : RamState) : Prop :=
  cvtsi2sOk 64 64 s.MXCSR ((Operand.xmm dst : Operand 128).read s)
    ((Operand.reg src : Operand 64).read s)

@[simp] theorem cvtsi2sdXmmR64Effect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) :
    (cvtsi2sdXmmR64Effect p len dst src s).components = [.xmm dst, .mxcsr, .rip] := rfl

theorem cvtsi2sd_xmm_r64_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (FpPre (Sse2Pre p) (cvtsi2sdXmmR64Ok (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))))
      (codeRange p ([0xF2, rex, 0x0F, 0x2A, modrm]))
      (cvtsi2sdXmmR64Effect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_f2_rex s.DS (PrefixSegments.ofState s) hr.rexPrefix
  have hstep := cvtsi2sd_xmm_r64_step s h hpre.sse hpre.sse2 [0xF2, rex]
    (by simp [scanPrefix_f2, hr.rexPrefix.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; exact hr.rex_w s.DS)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl)
    modrm hmod hcode.bytesAt hlow hm
    (by rw [hc]; exact hok)
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
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_writeResult_mxcsr]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]

theorem cvtsi2sd_xmm_r64_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (FpPre (Sse2Pre p) (cvtsi2sdXmmR64Ok (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))))
      (codeRange p ([0xF2, rex, 0x0F, 0x2A, modrm]))
      (Effect.post (cvtsi2sdXmmR64Effect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvtsi2sdXmmR64Effect_components]; simp [Component.Covers]) _)
    (cvtsi2sd_xmm_r64_rex_effect_step p rex hr modrm hmod)

theorem cvtsi2sd_xmm_r64_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (FpPre (Sse2Pre p) (cvtsi2sdXmmR64Ok (dst.setWidth 5) (src.setWidth 5))) (codeRange p (encodeCvtsi2sdXmmR64 dst src))
      (Effect.post (cvtsi2sdXmmR64Effect p (encodeCvtsi2sdXmmR64 dst src).length
        (dst.setWidth 5) (src.setWidth 5))) := by
  unfold encodeCvtsi2sdXmmR64
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hrm⟩ := encodeSseRegRegW_spec 0x2A dst src
  rw [hbytes, ← hreg, ← hrm]
  exact cvtsi2sd_xmm_r64_rex_triple_of_bytes p rex hrex modrm hmod

attribute [x86_compose] cvtsi2sdXmmR64Effect

@[x86_local] theorem cvtsi2sdXmmR64Effect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5} :
    Effect.Local (cvtsi2sdXmmR64Effect p len dst src) := by
  effect_local [cvtsi2sdXmmR64Effect]

end X86Proofs
