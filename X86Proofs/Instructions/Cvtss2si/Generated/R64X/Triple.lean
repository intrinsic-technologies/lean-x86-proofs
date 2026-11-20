import X86Proofs.Instructions.Cvtss2si.Generated.R64X.Step
import X86Proofs.Instructions.Cvtss2si.Generated.R64X.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cvtss2siR64XmmEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) :
    Effect :=
  let b := (Operand.xmm src : Operand 128).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), cvts2siSpec 32 64 s.MXCSR b⟩,
      ⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (cvts2siFlags 32 64 s.MXCSR b)⟩] }

def cvtss2siR64XmmOk (src : BitVec 5) (s : RamState) : Prop :=
  cvts2siOk 32 64 s.MXCSR ((Operand.xmm src : Operand 128).read s)

@[simp] theorem cvtss2siR64XmmEffect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) :
    (cvtss2siR64XmmEffect p len dst src s).components = [.reg dst, .mxcsr, .rip] := rfl

theorem cvtss2si_r64_xmm_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (FpPre (SsePre p) (cvtss2siR64XmmOk (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))))
      (codeRange p ([0xF3, rex, 0x0F, 0x2D, modrm]))
      (cvtss2siR64XmmEffect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_f3_rex s.DS (PrefixSegments.ofState s) hr.rexPrefix
  have hstep := cvtss2si_r64_xmm_step s h hpre.sse hpre.sse.feature [0xF3, rex]
    (by simp [scanPrefix_f3, hr.rexPrefix.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; exact hr.rex_w s.DS)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
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
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult_reg_mxcsr h _ _ _ _ _,
    ⟨afterStep_writeResult_reg_mxcsr_rip h _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult_reg_mxcsr s _ _ _ _ _⟩⟩
  refine ⟨?_, ?_⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_writeResult_self]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [writeResult, Operand.write_reg64, Operand.write_mxcsr, Operand.read_mxcsr,
      Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR, beforeFetch_MXCSR]

theorem cvtss2si_r64_xmm_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (FpPre (SsePre p) (cvtss2siR64XmmOk (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))))
      (codeRange p ([0xF3, rex, 0x0F, 0x2D, modrm]))
      (Effect.post (cvtss2siR64XmmEffect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvtss2siR64XmmEffect_components]; simp [Component.Covers]) _)
    (cvtss2si_r64_xmm_rex_effect_step p rex hr modrm hmod)

theorem cvtss2si_r64_xmm_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (FpPre (SsePre p) (cvtss2siR64XmmOk (src.setWidth 5))) (codeRange p (encodeCvtss2siR64Xmm dst src))
      (Effect.post (cvtss2siR64XmmEffect p (encodeCvtss2siR64Xmm dst src).length
        (dst.setWidth 5) (src.setWidth 5))) := by
  unfold encodeCvtss2siR64Xmm
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hrm⟩ := encodeSseRegRegW_spec 0x2D dst src
  rw [hbytes, ← hreg, ← hrm]
  exact cvtss2si_r64_xmm_rex_triple_of_bytes p rex hrex modrm hmod

attribute [x86_compose] cvtss2siR64XmmEffect

@[x86_local] theorem cvtss2siR64XmmEffect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5} :
    Effect.Local (cvtss2siR64XmmEffect p len dst src) := by
  effect_local [cvtss2siR64XmmEffect]

end X86Proofs
