import X86Proofs.Instructions.Adc.Generated.R8Imm8.Step
import X86Proofs.Instructions.Adc.Generated.R8Imm8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def adcR8Imm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  let b := imm.signExtend 8
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (a + b + BitVec.ofNat 8 c.toNat) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR8Imm8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8)
    (c : Bool) (s : RamState) :
    (adcR8Imm8Effect p len dst imm c s).components = [.reg dst, .flags, .rip] := rfl

theorem adcR8Imm8Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8)
    (c : Bool) (s : RamState) (code : CodeMap) : (adcR8Imm8Effect p len dst imm c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem adc_r8_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (c : Bool) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 2) (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x80 :: modrm :: immBytes 8 imm))
      (adcR8Imm8Effect p 3 (gprNumber 0 0 (modrmRm modrm)) imm c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_r8_imm8_step s h modrm imm hmod hreg hrm8 hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), adc_r8_imm8_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r8_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (c : Bool) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 2) (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x80 :: modrm :: immBytes 8 imm))
      (Effect.post (adcR8Imm8Effect p 3 (gprNumber 0 0 (modrmRm modrm)) imm c)) :=
  Triple.of_effect (fun s _ => adcR8Imm8Effect_avoids p _ _ _ _ s _)
    (adc_r8_imm8_effect_step p modrm imm c hmod hreg hrm8)

theorem adc_r8_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (c : Bool) (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x80 :: modrm :: immBytes 8 imm))
      (adcR8Imm8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_r8_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), adc_r8_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r8_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (c : Bool) (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x80 :: modrm :: immBytes 8 imm))
      (Effect.post (adcR8Imm8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm c)) :=
  Triple.of_effect (fun s _ => adcR8Imm8Effect_avoids p _ _ _ _ s _)
    (adc_r8_imm8_rex_effect_step p rex modrm imm c hrex hmod hreg)

theorem adc_r8_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8)
    (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcR8Imm8 dst imm))
      (Effect.post (adcR8Imm8Effect p (encodeAdcR8Imm8 dst imm).length (dst.setWidth 5) imm c)) := by
  rcases encodeAdcR8Imm8_spec dst imm with ⟨modrm, hbytes, hmod, hreg, hrm8, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    simpa using adc_r8_imm8_triple_of_bytes p modrm imm c hmod hreg hrm8
  · rw [hbytes, ← hdst]
    simpa using adc_r8_imm8_rex_triple_of_bytes p rex modrm imm c hrex hmod hreg

def adcR8Imm8NoRexEffect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (imm : BitVec 8) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.byteReg dst).read s
  let b := imm.signExtend 8
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (byteRegGpr dst) : Operand 64),
      mergeByteReg dst (a + b + BitVec.ofNat 8 c.toNat)
        ((Operand.reg (byteRegGpr dst) : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR8Imm8NoRexEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (imm : BitVec 8) (c : Bool) (s : RamState) :
    (adcR8Imm8NoRexEffect p len dst imm c s).components =
      [.reg (byteRegGpr dst), .flags, .rip] := rfl

theorem adcR8Imm8NoRexEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (imm : BitVec 8) (c : Bool) (s : RamState) (code : CodeMap) :
    (adcR8Imm8NoRexEffect p len dst imm c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem adc_r8_imm8_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (c : Bool) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x80 :: modrm :: immBytes 8 imm))
      (adcR8Imm8NoRexEffect p 3 (modrmRm modrm) imm c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  have hs := adc_r8_imm8_norex_step s h modrm imm hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp))
  have hr := adc_r8_imm8_norex_ready h modrm imm
  simp only [writeOutputs_byteReg] at hs hr
  refine ⟨_, hs, hr,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_RFLAGS,
      beforeFetch_RFLAGS]
    exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r8_imm8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (c : Bool) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x80 :: modrm :: immBytes 8 imm))
      (Effect.post (adcR8Imm8NoRexEffect p 3 (modrmRm modrm) imm c)) :=
  Triple.of_effect (fun s _ => adcR8Imm8NoRexEffect_avoids p _ _ _ _ s _)
    (adc_r8_imm8_norex_effect_step p modrm imm c hmod hreg)

theorem adc_r8_imm8_norex_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (imm : BitVec 8)
    (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcR8Imm8NoRex dst imm))
      (Effect.post (adcR8Imm8NoRexEffect p 3 dst imm c)) := by
  have h := adc_r8_imm8_norex_triple_of_bytes p (modrmRegs 2 dst) imm c
    (modrmMod_modrmRegs _ _) (modrmReg_modrmRegs _ _)
  rwa [modrmRm_modrmRegs] at h

attribute [x86_compose] adcR8Imm8Effect adcR8Imm8NoRexEffect

@[x86_local] theorem adcR8Imm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {imm8 : BitVec 8} {c : Bool} :
    Effect.Local (adcR8Imm8Effect p len dst imm8 c) := by
  effect_local [adcR8Imm8Effect]

@[x86_local] theorem adcR8Imm8NoRexEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {imm8 : BitVec 8} {c : Bool} :
    Effect.Local (adcR8Imm8NoRexEffect p len dst imm8 c) := by
  effect_local [adcR8Imm8NoRexEffect]

end X86Proofs
