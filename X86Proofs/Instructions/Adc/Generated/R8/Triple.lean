import X86Proofs.Instructions.Adc.Generated.R8.Step
import X86Proofs.Instructions.Adc.Generated.R8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def adcR8R8Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  let b := (Operand.reg src : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (a + b + BitVec.ofNat 8 c.toNat) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR8R8Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (c : Bool) (s : RamState) :
    (adcR8R8Effect p len dst src c s).components = [.reg dst, .flags, .rip] := rfl

theorem adcR8R8Effect_avoids (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (c : Bool)
    (s : RamState) (code : CodeMap) : (adcR8R8Effect p len dst src c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def adcR8R8NoRexEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 3) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.byteReg dst).read s
  let b := (Operand.byteReg src).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (byteRegGpr dst) : Operand 64),
      mergeByteReg dst (a + b + BitVec.ofNat 8 c.toNat) ((Operand.reg (byteRegGpr dst) : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR8R8NoRexEffect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 3) (c : Bool) (s : RamState) :
    (adcR8R8NoRexEffect p len dst src c s).components =
      [.reg (byteRegGpr dst), .flags, .rip] := rfl

theorem adcR8R8NoRexEffect_avoids (p : BitVec 64) (len : Nat) (dst src : BitVec 3) (c : Bool)
    (s : RamState) (code : CodeMap) : (adcR8R8NoRexEffect p len dst src c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem adc_r8_r8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (c : Bool)
    (hmod : modrmMod modrm = 3)
    (hreg8 : (modrmReg modrm).toNat < 4) (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x10, modrm])
      (adcR8R8Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)) c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_r8_r8_step s h modrm hmod hreg8 hrm8 hcode.bytesAt
    (hcode.low (by simp) (by simp)), adc_r8_r8_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r8_r8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8) (c : Bool)
    (hmod : modrmMod modrm = 3)
    (hreg8 : (modrmReg modrm).toNat < 4) (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x10, modrm])
      (Effect.post (adcR8R8Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)) c)) :=
  Triple.of_effect (fun s _ => adcR8R8Effect_avoids p _ _ _ _ s _)
    (adc_r8_r8_effect_step p modrm c hmod hreg8 hrm8)

theorem adc_r8_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8) (c : Bool)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [rex, 0x10, modrm])
      (adcR8R8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_r8_r8_rex_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), adc_r8_r8_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r8_r8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8) (c : Bool)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [rex, 0x10, modrm])
      (Effect.post (adcR8R8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) c)) :=
  Triple.of_effect (fun s _ => adcR8R8Effect_avoids p _ _ _ _ s _)
    (adc_r8_r8_rex_effect_step p rex modrm c hrex hmod)

theorem adc_r8_r8_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcR8R8 dst src))
      (Effect.post (adcR8R8Effect p (encodeAdcR8R8 dst src).length (dst.setWidth 5)
        (src.setWidth 5) c)) := by
  rcases encodeAdcR8R8_spec dst src with ⟨modrm, hbytes, hmod, hreg8, hrm8, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact adc_r8_r8_triple_of_bytes p modrm c hmod hreg8 hrm8
  · rw [hbytes, ← hdst, ← hsrc]
    exact adc_r8_r8_rex_triple_of_bytes p rex modrm c hrex hmod

theorem adc_r8_r8_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (c : Bool)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x10, modrm])
      (adcR8R8NoRexEffect p 2 (modrmRm modrm) (modrmReg modrm) c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  have hs := adc_r8_r8_norex_step s h modrm hmod hcode.bytesAt (hcode.low (by simp) (by simp))
  have hr := adc_r8_r8_norex_ready h modrm
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

theorem adc_r8_r8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8) (c : Bool)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x10, modrm])
      (Effect.post (adcR8R8NoRexEffect p 2 (modrmRm modrm) (modrmReg modrm) c)) :=
  Triple.of_effect (fun s _ => adcR8R8NoRexEffect_avoids p _ _ _ _ s _)
    (adc_r8_r8_norex_effect_step p modrm c hmod)

theorem adc_r8_r8_norex_triple [Bindings] (p : BitVec 64) (dst src : BitVec 3) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcR8R8NoRex dst src))
      (Effect.post (adcR8R8NoRexEffect p 2 dst src c)) := by
  have h := adc_r8_r8_norex_triple_of_bytes p (modrmRegs src dst) c (modrmMod_modrmRegs _ _)
  rwa [modrmRm_modrmRegs, modrmReg_modrmRegs] at h

attribute [x86_compose] adcR8R8Effect adcR8R8NoRexEffect

@[x86_local] theorem adcR8R8Effect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5}
    {c : Bool} :
    Effect.Local (adcR8R8Effect p len dst src c) := by
  effect_local [adcR8R8Effect]

@[x86_local] theorem adcR8R8NoRexEffect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 3}
    {c : Bool} :
    Effect.Local (adcR8R8NoRexEffect p len dst src c) := by
  effect_local [adcR8R8NoRexEffect]

end X86Proofs
