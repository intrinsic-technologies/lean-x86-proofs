import X86Proofs.Instructions.Ucomiss.Generated.XX.Step
import X86Proofs.Instructions.Ucomiss.Generated.XX.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def ucomissXmmXmmEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) :
    Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.xmm src : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (ucomisExc 32 s.MXCSR a b)⟩]
    flags := some (.ofStatusFlags (ucomisFlags 32 s.MXCSR a b)) }

def ucomissXmmXmmOk (dst src : BitVec 5) (s : RamState) : Prop :=
  ucomisOk 32 s.MXCSR ((Operand.xmm dst : Operand 128).read s)
    ((Operand.xmm src : Operand 32).read s)

@[simp] theorem ucomissXmmXmmEffect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) :
    (ucomissXmmXmmEffect p len dst src s).components = [.mxcsr, .flags, .rip] := rfl

theorem ucomiss_xmm_xmm_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (FpPre (SsePre p) (ucomissXmmXmmOk (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))))
      (codeRange p ([0x0F, 0x2E, modrm]))
      (ucomissXmmXmmEffect p 3 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := ucomiss_xmm_xmm_step s h hpre.sse hpre.sse.feature []
    (by simp) (by simp)
    rfl rfl rfl
    rfl rfl rfl
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
  refine ⟨_, hstep, ReadyToStep.afterStep_writeFpFlags h _ _ _ _,
    ⟨afterStep_writeFpFlags_rip h _ _ _ _, ?_, ?_, AgreesExcept.afterStep_writeFpFlags s _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_writeFpFlags_mxcsr]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
  · show StatusFlagsOutcome.Allows _ _
    rw [ofRFLAGS_afterStep_writeFpFlags]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem ucomiss_xmm_xmm_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (FpPre (SsePre p) (ucomissXmmXmmOk (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))))
      (codeRange p ([0x0F, 0x2E, modrm]))
      (Effect.post (ucomissXmmXmmEffect p 3 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [ucomissXmmXmmEffect_components]; simp [Component.Covers]) _)
    (ucomiss_xmm_xmm_effect_step p modrm hmod)

theorem ucomiss_xmm_xmm_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (FpPre (SsePre p) (ucomissXmmXmmOk (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))))
      (codeRange p ([rex, 0x0F, 0x2E, modrm]))
      (ucomissXmmXmmEffect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := ucomiss_xmm_xmm_step s h hpre.sse hpre.sse.feature [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
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
  refine ⟨_, hstep, ReadyToStep.afterStep_writeFpFlags h _ _ _ _,
    ⟨afterStep_writeFpFlags_rip h _ _ _ _, ?_, ?_, AgreesExcept.afterStep_writeFpFlags s _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_writeFpFlags_mxcsr]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
  · show StatusFlagsOutcome.Allows _ _
    rw [ofRFLAGS_afterStep_writeFpFlags]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem ucomiss_xmm_xmm_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (FpPre (SsePre p) (ucomissXmmXmmOk (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))))
      (codeRange p ([rex, 0x0F, 0x2E, modrm]))
      (Effect.post (ucomissXmmXmmEffect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [ucomissXmmXmmEffect_components]; simp [Component.Covers]) _)
    (ucomiss_xmm_xmm_rex_effect_step p rex hr modrm hmod)

theorem ucomiss_xmm_xmm_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (FpPre (SsePre p) (ucomissXmmXmmOk (dst.setWidth 5) (src.setWidth 5))) (codeRange p (encodeUcomissXmmXmm dst src))
      (Effect.post (ucomissXmmXmmEffect p (encodeUcomissXmmXmm dst src).length
        (dst.setWidth 5) (src.setWidth 5))) := by
  unfold encodeUcomissXmmXmm
  rcases encodeSseRegReg_spec 0x2E dst src with ⟨modrm, hbytes, hmod, hreg, hrm⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hrm⟩
  · rw [hbytes, ← hreg, ← hrm]
    exact ucomiss_xmm_xmm_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hreg, ← hrm]
    exact ucomiss_xmm_xmm_rex_triple_of_bytes p rex hrex modrm hmod

attribute [x86_compose] ucomissXmmXmmEffect

@[x86_local] theorem ucomissXmmXmmEffect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5} :
    Effect.Local (ucomissXmmXmmEffect p len dst src) := by
  effect_local [ucomissXmmXmmEffect]

end X86Proofs
