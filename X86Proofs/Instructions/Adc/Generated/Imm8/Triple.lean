import X86Proofs.Instructions.Adc.Generated.Imm8.Step
import X86Proofs.Instructions.Adc.Generated.Imm8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def adcR64Imm8Effect (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64), a + b + BitVec.ofNat 64 c.toNat⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR64Imm8Effect_components (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8)
    (c : Bool) (s : RamState) :
    (adcR64Imm8Effect p dst imm c s).components = [.reg dst, .flags, .rip] := rfl

theorem adcR64Imm8Effect_avoids (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8)
    (c : Bool) (s : RamState) (code : CodeMap) : (adcR64Imm8Effect p dst imm c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem adc_r64_imm8_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (c : Bool) (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x83 :: modrm :: immBytes 8 imm))
      (adcR64Imm8Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_r64_imm8_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), adc_r64_imm8_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r64_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (c : Bool) (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x83 :: modrm :: immBytes 8 imm))
      (Effect.post (adcR64Imm8Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm c)) :=
  Triple.of_effect (fun s _ => adcR64Imm8Effect_avoids p _ _ _ s _)
    (adc_r64_imm8_effect_step p rex modrm imm c hrex hmod hreg)

theorem adc_r64_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8)
    (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcR64Imm8 dst imm))
      (Effect.post (adcR64Imm8Effect p (dst.setWidth 5) imm c)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeAdcR64Imm8_spec dst imm
  rw [hbytes, ← hdst]
  exact adc_r64_imm8_triple_of_bytes p rex modrm imm c hrex hmod hreg

def adcR32Imm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (a + b + BitVec.ofNat 32 c.toNat).setWidth 64⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR32Imm8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8)
    (c : Bool) (s : RamState) :
    (adcR32Imm8Effect p len dst imm c s).components = [.reg dst, .flags, .rip] := rfl

theorem adcR32Imm8Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8)
    (c : Bool) (s : RamState) (code : CodeMap) : (adcR32Imm8Effect p len dst imm c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem adc_r32_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (c : Bool) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x83 :: modrm :: immBytes 8 imm))
      (adcR32Imm8Effect p 3 (gprNumber 0 0 (modrmRm modrm)) imm c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_r32_imm8_step s h modrm imm hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), adc_r32_imm8_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r32_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (c : Bool) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x83 :: modrm :: immBytes 8 imm))
      (Effect.post (adcR32Imm8Effect p 3 (gprNumber 0 0 (modrmRm modrm)) imm c)) :=
  Triple.of_effect (fun s _ => adcR32Imm8Effect_avoids p _ _ _ _ s _)
    (adc_r32_imm8_effect_step p modrm imm c hmod hreg)

theorem adc_r32_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (c : Bool) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x83 :: modrm :: immBytes 8 imm))
      (adcR32Imm8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_r32_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), adc_r32_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r32_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (c : Bool) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x83 :: modrm :: immBytes 8 imm))
      (Effect.post (adcR32Imm8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm c)) :=
  Triple.of_effect (fun s _ => adcR32Imm8Effect_avoids p _ _ _ _ s _)
    (adc_r32_imm8_rex_effect_step p rex modrm imm c hrex hmod hreg)

theorem adc_r32_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8)
    (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcR32Imm8 dst imm))
      (Effect.post (adcR32Imm8Effect p (encodeAdcR32Imm8 dst imm).length (dst.setWidth 5) imm c)) := by
  rcases encodeAdcR32Imm8_spec dst imm with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    simpa using adc_r32_imm8_triple_of_bytes p modrm imm c hmod hreg
  · rw [hbytes, ← hdst]
    simpa using adc_r32_imm8_rex_triple_of_bytes p rex modrm imm c hrex hmod hreg

def adcR16Imm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (a + b + BitVec.ofNat 16 c.toNat) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR16Imm8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8)
    (c : Bool) (s : RamState) :
    (adcR16Imm8Effect p len dst imm c s).components = [.reg dst, .flags, .rip] := rfl

theorem adcR16Imm8Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8)
    (c : Bool) (s : RamState) (code : CodeMap) : (adcR16Imm8Effect p len dst imm c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem adc_r16_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (c : Bool) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x66 :: 0x83 :: modrm :: immBytes 8 imm))
      (adcR16Imm8Effect p 4 (gprNumber 0 0 (modrmRm modrm)) imm c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_r16_imm8_step s h modrm imm hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), adc_r16_imm8_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r16_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (c : Bool) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x66 :: 0x83 :: modrm :: immBytes 8 imm))
      (Effect.post (adcR16Imm8Effect p 4 (gprNumber 0 0 (modrmRm modrm)) imm c)) :=
  Triple.of_effect (fun s _ => adcR16Imm8Effect_avoids p _ _ _ _ s _)
    (adc_r16_imm8_effect_step p modrm imm c hmod hreg)

theorem adc_r16_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (c : Bool) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x66 :: rex :: 0x83 :: modrm :: immBytes 8 imm))
      (adcR16Imm8Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_r16_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), adc_r16_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 5 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 5 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r16_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (c : Bool) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x66 :: rex :: 0x83 :: modrm :: immBytes 8 imm))
      (Effect.post (adcR16Imm8Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm c)) :=
  Triple.of_effect (fun s _ => adcR16Imm8Effect_avoids p _ _ _ _ s _)
    (adc_r16_imm8_rex_effect_step p rex modrm imm c hrex hmod hreg)

theorem adc_r16_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8)
    (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcR16Imm8 dst imm))
      (Effect.post (adcR16Imm8Effect p (encodeAdcR16Imm8 dst imm).length (dst.setWidth 5) imm c)) := by
  rcases encodeAdcR16Imm8_spec dst imm with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    simpa using adc_r16_imm8_triple_of_bytes p modrm imm c hmod hreg
  · rw [hbytes, ← hdst]
    simpa using adc_r16_imm8_rex_triple_of_bytes p rex modrm imm c hrex hmod hreg

attribute [x86_compose] adcR64Imm8Effect adcR32Imm8Effect adcR16Imm8Effect

@[x86_local] theorem adcR64Imm8Effect_local {p : BitVec 64} {dst : BitVec 5}
    {imm8 : BitVec 8} {c : Bool} :
    Effect.Local (adcR64Imm8Effect p dst imm8 c) := by
  effect_local [adcR64Imm8Effect]

@[x86_local] theorem adcR32Imm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {imm8 : BitVec 8} {c : Bool} :
    Effect.Local (adcR32Imm8Effect p len dst imm8 c) := by
  effect_local [adcR32Imm8Effect]

@[x86_local] theorem adcR16Imm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {imm8 : BitVec 8} {c : Bool} :
    Effect.Local (adcR16Imm8Effect p len dst imm8 c) := by
  effect_local [adcR16Imm8Effect]

end X86Proofs
