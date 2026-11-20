import X86Proofs.Instructions.Adc.Generated.R8Rev.Step
import X86Proofs.Instructions.Adc.Generated.R8Rev.Encode
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Adc.Generated.R8.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem adc_r8_r8_rev_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (c : Bool)
    (hmod : modrmMod modrm = 3)
    (hreg8 : (modrmReg modrm).toNat < 4) (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x12, modrm])
      (adcR8R8Effect p 2 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_r8_r8_rev_step s h modrm hmod hreg8 hrm8 hcode.bytesAt
    (hcode.low (by simp) (by simp)), adc_r8_r8_rev_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r8_r8_rev_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8) (c : Bool)
    (hmod : modrmMod modrm = 3)
    (hreg8 : (modrmReg modrm).toNat < 4) (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x12, modrm])
      (Effect.post (adcR8R8Effect p 2 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) c)) :=
  Triple.of_effect (fun s _ => adcR8R8Effect_avoids p _ _ _ _ s _)
    (adc_r8_r8_rev_effect_step p modrm c hmod hreg8 hrm8)

theorem adc_r8_r8_rev_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8) (c : Bool)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [rex, 0x12, modrm])
      (adcR8R8Effect p 3 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_r8_r8_rev_rex_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), adc_r8_r8_rev_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r8_r8_rev_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8) (c : Bool)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [rex, 0x12, modrm])
      (Effect.post (adcR8R8Effect p 3 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) c)) :=
  Triple.of_effect (fun s _ => adcR8R8Effect_avoids p _ _ _ _ s _)
    (adc_r8_r8_rev_rex_effect_step p rex modrm c hrex hmod)

theorem adc_r8_r8_rev_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcR8R8Rev dst src))
      (Effect.post (adcR8R8Effect p (encodeAdcR8R8Rev dst src).length (dst.setWidth 5)
        (src.setWidth 5) c)) := by
  rcases encodeAdcR8R8Rev_spec dst src with ⟨modrm, hbytes, hmod, hreg8, hrm8, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact adc_r8_r8_rev_triple_of_bytes p modrm c hmod hreg8 hrm8
  · rw [hbytes, ← hdst, ← hsrc]
    exact adc_r8_r8_rev_rex_triple_of_bytes p rex modrm c hrex hmod

theorem adc_r8_r8_rev_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (c : Bool)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x12, modrm])
      (adcR8R8NoRexEffect p 2 (modrmReg modrm) (modrmRm modrm) c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  have hs := adc_r8_r8_rev_norex_step s h modrm hmod hcode.bytesAt (hcode.low (by simp) (by simp))
  have hr := adc_r8_r8_rev_norex_ready h modrm
  simp only [writeOutputs_byteReg] at hs hr
  refine ⟨_, hs, hr,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_RFLAGS,
      beforeFetch_RFLAGS]
    exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r8_r8_rev_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8) (c : Bool)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x12, modrm])
      (Effect.post (adcR8R8NoRexEffect p 2 (modrmReg modrm) (modrmRm modrm) c)) :=
  Triple.of_effect (fun s _ => adcR8R8NoRexEffect_avoids p _ _ _ _ s _)
    (adc_r8_r8_rev_norex_effect_step p modrm c hmod)

theorem adc_r8_r8_rev_norex_triple [Bindings] (p : BitVec 64) (dst src : BitVec 3) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcR8R8RevNoRex dst src))
      (Effect.post (adcR8R8NoRexEffect p 2 dst src c)) := by
  have h := adc_r8_r8_rev_norex_triple_of_bytes p (modrmRegs dst src) c (modrmMod_modrmRegs _ _)
  rwa [modrmRm_modrmRegs, modrmReg_modrmRegs] at h

end X86Proofs
