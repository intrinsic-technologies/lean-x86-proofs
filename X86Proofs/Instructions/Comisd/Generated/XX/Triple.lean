import X86Proofs.Instructions.Comisd.Generated.XX.Step
import X86Proofs.Instructions.Comisd.Generated.XX.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def comisdXmmXmmEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) :
    Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.xmm src : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (comisExc 64 s.MXCSR a b)⟩]
    flags := some (.ofStatusFlags (comisFlags 64 s.MXCSR a b)) }

def comisdXmmXmmOk (dst src : BitVec 5) (s : RamState) : Prop :=
  comisOk 64 s.MXCSR ((Operand.xmm dst : Operand 128).read s)
    ((Operand.xmm src : Operand 64).read s)

@[simp] theorem comisdXmmXmmEffect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) :
    (comisdXmmXmmEffect p len dst src s).components = [.mxcsr, .flags, .rip] := rfl

theorem comisd_xmm_xmm_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (FpPre (Sse2Pre p) (comisdXmmXmmOk (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))))
      (codeRange p ([0x66, 0x0F, 0x2F, modrm]))
      (comisdXmmXmmEffect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := comisd_xmm_xmm_step s h hpre.sse hpre.sse2 [0x66]
    (by simpa using scanPrefix_66) (by simp)
    rfl rfl rfl
    rfl rfl rfl
    modrm hmod hcode.bytesAt hlow hm
    hok
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b3 (modrmRm modrm) =
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

theorem comisd_xmm_xmm_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (FpPre (Sse2Pre p) (comisdXmmXmmOk (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))))
      (codeRange p ([0x66, 0x0F, 0x2F, modrm]))
      (Effect.post (comisdXmmXmmEffect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [comisdXmmXmmEffect_components]; simp [Component.Covers]) _)
    (comisd_xmm_xmm_effect_step p modrm hmod)

theorem comisd_xmm_xmm_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (FpPre (Sse2Pre p) (comisdXmmXmmOk (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))))
      (codeRange p ([0x66, rex, 0x0F, 0x2F, modrm]))
      (comisdXmmXmmEffect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_66_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := comisd_xmm_xmm_step s h hpre.sse hpre.sse2 [0x66, rex]
    (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    modrm hmod hcode.bytesAt hlow hm
    (by rw [hc]; exact hok)
  simp only [hc] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_r4
      (oszRexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  have hsrc : gprNumber (oszRexContext s.DS rex.toBitVec).rex_b4
      (oszRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
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

theorem comisd_xmm_xmm_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (FpPre (Sse2Pre p) (comisdXmmXmmOk (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))))
      (codeRange p ([0x66, rex, 0x0F, 0x2F, modrm]))
      (Effect.post (comisdXmmXmmEffect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [comisdXmmXmmEffect_components]; simp [Component.Covers]) _)
    (comisd_xmm_xmm_rex_effect_step p rex hr modrm hmod)

theorem comisd_xmm_xmm_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (FpPre (Sse2Pre p) (comisdXmmXmmOk (dst.setWidth 5) (src.setWidth 5))) (codeRange p (encodeComisdXmmXmm dst src))
      (Effect.post (comisdXmmXmmEffect p (encodeComisdXmmXmm dst src).length
        (dst.setWidth 5) (src.setWidth 5))) := by
  unfold encodeComisdXmmXmm
  rcases encodeSseRegReg_spec 0x2F dst src with ⟨modrm, hbytes, hmod, hreg, hrm⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hrm⟩
  · rw [hbytes, ← hreg, ← hrm]
    exact comisd_xmm_xmm_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hreg, ← hrm]
    exact comisd_xmm_xmm_rex_triple_of_bytes p rex hrex modrm hmod

attribute [x86_compose] comisdXmmXmmEffect

@[x86_local] theorem comisdXmmXmmEffect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5} :
    Effect.Local (comisdXmmXmmEffect p len dst src) := by
  effect_local [comisdXmmXmmEffect]

end X86Proofs
