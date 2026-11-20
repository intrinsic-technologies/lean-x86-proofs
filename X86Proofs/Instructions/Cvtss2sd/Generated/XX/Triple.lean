import X86Proofs.Instructions.Cvtss2sd.Generated.XX.Step
import X86Proofs.Instructions.Cvtss2sd.Generated.XX.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cvtss2sdXmmXmmEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) :
    Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.xmm src : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), cvtss2sdSpec s.MXCSR a b⟩,
      ⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (cvtss2sdFlags s.MXCSR a b)⟩] }

def cvtss2sdXmmXmmOk (dst src : BitVec 5) (s : RamState) : Prop :=
  cvtss2sdOk s.MXCSR ((Operand.xmm dst : Operand 128).read s)
    ((Operand.xmm src : Operand 32).read s)

@[simp] theorem cvtss2sdXmmXmmEffect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) :
    (cvtss2sdXmmXmmEffect p len dst src s).components = [.xmm dst, .mxcsr, .rip] := rfl

theorem cvtss2sd_xmm_xmm_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (FpPre (Sse2Pre p) (cvtss2sdXmmXmmOk (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))))
      (codeRange p ([0xF3, 0x0F, 0x5A, modrm]))
      (cvtss2sdXmmXmmEffect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cvtss2sd_xmm_xmm_step s h hpre.sse hpre.sse2 [0xF3]
    (by simpa using scanPrefix_f3) (by simp)
    rfl rfl rfl
    rfl rfl
    modrm hmod hcode.bytesAt hlow hm
    hok
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0xF3]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0xF3]).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0xF3]).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) [0xF3]).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
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

theorem cvtss2sd_xmm_xmm_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (FpPre (Sse2Pre p) (cvtss2sdXmmXmmOk (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))))
      (codeRange p ([0xF3, 0x0F, 0x5A, modrm]))
      (Effect.post (cvtss2sdXmmXmmEffect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvtss2sdXmmXmmEffect_components]; simp [Component.Covers]) _)
    (cvtss2sd_xmm_xmm_effect_step p modrm hmod)

theorem cvtss2sd_xmm_xmm_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (FpPre (Sse2Pre p) (cvtss2sdXmmXmmOk (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))))
      (codeRange p ([0xF3, rex, 0x0F, 0x5A, modrm]))
      (cvtss2sdXmmXmmEffect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_f3_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := cvtss2sd_xmm_xmm_step s h hpre.sse hpre.sse2 [0xF3, rex]
    (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl)
    modrm hmod hcode.bytesAt hlow hm
    (by rw [hc]; exact hok)
  simp only [hc] at hstep
  have hdst : gprNumber (repRexContext s.DS rex.toBitVec).rex_r4
      (repRexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  have hsrc : gprNumber (repRexContext s.DS rex.toBitVec).rex_b4
      (repRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
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

theorem cvtss2sd_xmm_xmm_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (FpPre (Sse2Pre p) (cvtss2sdXmmXmmOk (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))))
      (codeRange p ([0xF3, rex, 0x0F, 0x5A, modrm]))
      (Effect.post (cvtss2sdXmmXmmEffect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvtss2sdXmmXmmEffect_components]; simp [Component.Covers]) _)
    (cvtss2sd_xmm_xmm_rex_effect_step p rex hr modrm hmod)

theorem cvtss2sd_xmm_xmm_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (FpPre (Sse2Pre p) (cvtss2sdXmmXmmOk (dst.setWidth 5) (src.setWidth 5))) (codeRange p (encodeCvtss2sdXmmXmm dst src))
      (Effect.post (cvtss2sdXmmXmmEffect p (encodeCvtss2sdXmmXmm dst src).length
        (dst.setWidth 5) (src.setWidth 5))) := by
  unfold encodeCvtss2sdXmmXmm
  rcases encodeSseRegReg_spec 0x5A dst src with ⟨modrm, hbytes, hmod, hreg, hrm⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hrm⟩
  · rw [hbytes, ← hreg, ← hrm]
    exact cvtss2sd_xmm_xmm_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hreg, ← hrm]
    exact cvtss2sd_xmm_xmm_rex_triple_of_bytes p rex hrex modrm hmod

attribute [x86_compose] cvtss2sdXmmXmmEffect

@[x86_local] theorem cvtss2sdXmmXmmEffect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5} :
    Effect.Local (cvtss2sdXmmXmmEffect p len dst src) := by
  effect_local [cvtss2sdXmmXmmEffect]

end X86Proofs
