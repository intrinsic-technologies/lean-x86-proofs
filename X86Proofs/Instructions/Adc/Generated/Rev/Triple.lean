import X86Proofs.Instructions.Adc.Generated.Rev.Step
import X86Proofs.Instructions.Adc.Generated.Rev.Encode
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Adc.Generated.RR.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem adc_r64_r64_rev_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8) (c : Bool)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [rex, 0x13, modrm])
      (adcR64R64Effect p (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_r64_r64_rev_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), adc_r64_r64_rev_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r64_r64_rev_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8) (c : Bool)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [rex, 0x13, modrm])
      (Effect.post (adcR64R64Effect p (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) c)) :=
  Triple.of_effect (fun s _ => adcR64R64Effect_avoids p _ _ _ s _)
    (adc_r64_r64_rev_effect_step p rex modrm c hrex hmod)

theorem adc_r32_r32_rev_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (c : Bool)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x13, modrm])
      (adcR32R32Effect p 2 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_r32_r32_rev_step s h modrm hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), adc_r32_r32_rev_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r32_r32_rev_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8) (c : Bool)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x13, modrm])
      (Effect.post (adcR32R32Effect p 2 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) c)) :=
  Triple.of_effect (fun s _ => adcR32R32Effect_avoids p _ _ _ _ s _)
    (adc_r32_r32_rev_effect_step p modrm c hmod)

theorem adc_r32_r32_rev_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8) (c : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [rex, 0x13, modrm])
      (adcR32R32Effect p 3 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_r32_r32_rev_rex_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), adc_r32_r32_rev_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r32_r32_rev_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8) (c : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [rex, 0x13, modrm])
      (Effect.post (adcR32R32Effect p 3 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) c)) :=
  Triple.of_effect (fun s _ => adcR32R32Effect_avoids p _ _ _ _ s _)
    (adc_r32_r32_rev_rex_effect_step p rex modrm c hrex hmod)

theorem adc_r16_r16_rev_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (c : Bool)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x66, 0x13, modrm])
      (adcR16R16Effect p 3 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_r16_r16_rev_step s h modrm hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), adc_r16_r16_rev_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r16_r16_rev_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8) (c : Bool)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x66, 0x13, modrm])
      (Effect.post (adcR16R16Effect p 3 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) c)) :=
  Triple.of_effect (fun s _ => adcR16R16Effect_avoids p _ _ _ _ s _)
    (adc_r16_r16_rev_effect_step p modrm c hmod)

theorem adc_r16_r16_rev_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8) (c : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x66, rex, 0x13, modrm])
      (adcR16R16Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_r16_r16_rev_rex_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), adc_r16_r16_rev_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r16_r16_rev_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8) (c : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x66, rex, 0x13, modrm])
      (Effect.post (adcR16R16Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) c)) :=
  Triple.of_effect (fun s _ => adcR16R16Effect_avoids p _ _ _ _ s _)
    (adc_r16_r16_rev_rex_effect_step p rex modrm c hrex hmod)

theorem adc_r64_r64_rev_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcR64R64Rev dst src))
      (Effect.post (adcR64R64Effect p (dst.setWidth 5) (src.setWidth 5) c)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeAdcR64R64Rev_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact adc_r64_r64_rev_triple_of_bytes p rex modrm c hrex hmod

theorem adc_r32_r32_rev_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcR32R32Rev dst src))
      (Effect.post (adcR32R32Effect p (encodeAdcR32R32Rev dst src).length (dst.setWidth 5)
        (src.setWidth 5) c)) := by
  rcases encodeAdcR32R32Rev_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact adc_r32_r32_rev_triple_of_bytes p modrm c hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact adc_r32_r32_rev_rex_triple_of_bytes p rex modrm c hrex hmod

theorem adc_r16_r16_rev_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcR16R16Rev dst src))
      (Effect.post (adcR16R16Effect p (encodeAdcR16R16Rev dst src).length (dst.setWidth 5)
        (src.setWidth 5) c)) := by
  rcases encodeAdcR16R16Rev_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact adc_r16_r16_rev_triple_of_bytes p modrm c hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact adc_r16_r16_rev_rex_triple_of_bytes p rex modrm c hrex hmod

end X86Proofs
