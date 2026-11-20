import X86Proofs.Instructions.Mulps.Generated.XX.Step
import X86Proofs.Instructions.Mulps.Generated.XX.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def mulpsXmmXmmEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) :
    Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.xmm src : Operand 128).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), mulpSpec 32 s.MXCSR a b⟩,
      ⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (mulpFlags 32 s.MXCSR a b)⟩] }

def mulpsXmmXmmOk (dst src : BitVec 5) (s : RamState) : Prop :=
  mulpOk 32 s.MXCSR ((Operand.xmm dst : Operand 128).read s)
    ((Operand.xmm src : Operand 128).read s)

@[simp] theorem mulpsXmmXmmEffect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) :
    (mulpsXmmXmmEffect p len dst src s).components = [.xmm dst, .mxcsr, .rip] := rfl

theorem mulps_xmm_xmm_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (FpPre (SsePre p) (mulpsXmmXmmOk (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))))
      (codeRange p ([0x0F, 0x59, modrm]))
      (mulpsXmmXmmEffect p 3 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := mulps_xmm_xmm_step s h hpre.sse hpre.sse.feature []
    (by simp) (by simp)
    rfl rfl rfl
    rfl rfl rfl
    rfl
    modrm hmod hcode.bytesAt hlow hm
    hok
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm) =
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

theorem mulps_xmm_xmm_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (FpPre (SsePre p) (mulpsXmmXmmOk (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))))
      (codeRange p ([0x0F, 0x59, modrm]))
      (Effect.post (mulpsXmmXmmEffect p 3 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [mulpsXmmXmmEffect_components]; simp [Component.Covers]) _)
    (mulps_xmm_xmm_effect_step p modrm hmod)

theorem mulps_xmm_xmm_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (FpPre (SsePre p) (mulpsXmmXmmOk (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))))
      (codeRange p ([rex, 0x0F, 0x59, modrm]))
      (mulpsXmmXmmEffect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := mulps_xmm_xmm_step s h hpre.sse hpre.sse.feature [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl)
    modrm hmod hcode.bytesAt hlow hm
    (by rw [hc]; exact hok)
  simp only [hc] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
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

theorem mulps_xmm_xmm_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (FpPre (SsePre p) (mulpsXmmXmmOk (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))))
      (codeRange p ([rex, 0x0F, 0x59, modrm]))
      (Effect.post (mulpsXmmXmmEffect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [mulpsXmmXmmEffect_components]; simp [Component.Covers]) _)
    (mulps_xmm_xmm_rex_effect_step p rex hr modrm hmod)

theorem mulps_xmm_xmm_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (FpPre (SsePre p) (mulpsXmmXmmOk (dst.setWidth 5) (src.setWidth 5))) (codeRange p (encodeMulpsXmmXmm dst src))
      (Effect.post (mulpsXmmXmmEffect p (encodeMulpsXmmXmm dst src).length
        (dst.setWidth 5) (src.setWidth 5))) := by
  unfold encodeMulpsXmmXmm
  rcases encodeSseRegReg_spec 0x59 dst src with ⟨modrm, hbytes, hmod, hreg, hrm⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hrm⟩
  · rw [hbytes, ← hreg, ← hrm]
    exact mulps_xmm_xmm_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hreg, ← hrm]
    exact mulps_xmm_xmm_rex_triple_of_bytes p rex hrex modrm hmod

attribute [x86_compose] mulpsXmmXmmEffect

@[x86_local] theorem mulpsXmmXmmEffect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5} :
    Effect.Local (mulpsXmmXmmEffect p len dst src) := by
  effect_local [mulpsXmmXmmEffect]

end X86Proofs
