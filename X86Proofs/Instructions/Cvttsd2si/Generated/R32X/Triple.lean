import X86Proofs.Instructions.Cvttsd2si.Generated.R32X.Step
import X86Proofs.Instructions.Cvttsd2si.Generated.R32X.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cvttsd2siR32XmmEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) :
    Effect :=
  let b := (Operand.xmm src : Operand 128).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (cvtts2siSpec 64 32 s.MXCSR b).setWidth 64⟩,
      ⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (cvtts2siFlags 64 32 s.MXCSR b)⟩] }

def cvttsd2siR32XmmOk (src : BitVec 5) (s : RamState) : Prop :=
  cvtts2siOk 64 32 s.MXCSR ((Operand.xmm src : Operand 128).read s)

@[simp] theorem cvttsd2siR32XmmEffect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) :
    (cvttsd2siR32XmmEffect p len dst src s).components = [.reg dst, .mxcsr, .rip] := rfl

theorem cvttsd2si_r32_xmm_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (FpPre (Sse2Pre p) (cvttsd2siR32XmmOk (gprNumber 0 0 (modrmRm modrm))))
      (codeRange p ([0xF2, 0x0F, 0x2C, modrm]))
      (cvttsd2siR32XmmEffect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cvttsd2si_r32_xmm_step s h hpre.sse hpre.sse2 [0xF2]
    (by simpa using scanPrefix_f2) (by simp)
    rfl rfl rfl
    rfl rfl
    modrm hmod hcode.bytesAt hlow hm
    hok
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0xF2]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0xF2]).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0xF2]).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) [0xF2]).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult_reg_mxcsr h _ _ _ _ _,
    ⟨afterStep_writeResult_reg_mxcsr_rip h _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult_reg_mxcsr s _ _ _ _ _⟩⟩
  refine ⟨?_, ?_⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_writeResult_self32]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [writeResult, Operand.write_reg32, Operand.write_mxcsr, Operand.read_mxcsr,
      Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR, beforeFetch_MXCSR]

theorem cvttsd2si_r32_xmm_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (FpPre (Sse2Pre p) (cvttsd2siR32XmmOk (gprNumber 0 0 (modrmRm modrm))))
      (codeRange p ([0xF2, 0x0F, 0x2C, modrm]))
      (Effect.post (cvttsd2siR32XmmEffect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvttsd2siR32XmmEffect_components]; simp [Component.Covers]) _)
    (cvttsd2si_r32_xmm_effect_step p modrm hmod)

theorem cvttsd2si_r32_xmm_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (FpPre (Sse2Pre p) (cvttsd2siR32XmmOk (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))))
      (codeRange p ([0xF2, rex, 0x0F, 0x2C, modrm]))
      (cvttsd2siR32XmmEffect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_f2_rex s.DS (PrefixSegments.ofState s) hr.rexPrefix
  have hstep := cvttsd2si_r32_xmm_step s h hpre.sse hpre.sse2 [0xF2, rex]
    (by simp [scanPrefix_f2, hr.rexPrefix.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; exact hr.rex_w s.DS)
    (by rw [hc]; rfl) (by rw [hc]; rfl)
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
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult_reg_mxcsr h _ _ _ _ _,
    ⟨afterStep_writeResult_reg_mxcsr_rip h _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult_reg_mxcsr s _ _ _ _ _⟩⟩
  refine ⟨?_, ?_⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_writeResult_self32]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [writeResult, Operand.write_reg32, Operand.write_mxcsr, Operand.read_mxcsr,
      Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR, beforeFetch_MXCSR]

theorem cvttsd2si_r32_xmm_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (FpPre (Sse2Pre p) (cvttsd2siR32XmmOk (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))))
      (codeRange p ([0xF2, rex, 0x0F, 0x2C, modrm]))
      (Effect.post (cvttsd2siR32XmmEffect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvttsd2siR32XmmEffect_components]; simp [Component.Covers]) _)
    (cvttsd2si_r32_xmm_rex_effect_step p rex hr modrm hmod)

theorem cvttsd2si_r32_xmm_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (FpPre (Sse2Pre p) (cvttsd2siR32XmmOk (src.setWidth 5))) (codeRange p (encodeCvttsd2siR32Xmm dst src))
      (Effect.post (cvttsd2siR32XmmEffect p (encodeCvttsd2siR32Xmm dst src).length
        (dst.setWidth 5) (src.setWidth 5))) := by
  unfold encodeCvttsd2siR32Xmm
  rcases encodeSseRegReg_spec_noW 0x2C dst src with ⟨modrm, hbytes, hmod, hreg, hrm⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hrm⟩
  · rw [hbytes, ← hreg, ← hrm]
    exact cvttsd2si_r32_xmm_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hreg, ← hrm]
    exact cvttsd2si_r32_xmm_rex_triple_of_bytes p rex hrex modrm hmod

attribute [x86_compose] cvttsd2siR32XmmEffect

@[x86_local] theorem cvttsd2siR32XmmEffect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5} :
    Effect.Local (cvttsd2siR32XmmEffect p len dst src) := by
  effect_local [cvttsd2siR32XmmEffect]

end X86Proofs
