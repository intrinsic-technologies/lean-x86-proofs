import X86Proofs.Instructions.Adc.Generated.RR.Step
import X86Proofs.Instructions.Adc.Generated.RR.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def adcR64R64Effect (p : BitVec 64) (dst src : BitVec 5) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := (Operand.reg src : Operand 64).read s
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64), a + b + BitVec.ofNat 64 c.toNat⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR64R64Effect_components (p : BitVec 64)
    (dst src : BitVec 5) (c : Bool) (s : RamState) :
    (adcR64R64Effect p dst src c s).components = [.reg dst, .flags, .rip] := rfl

theorem adcR64R64Effect_avoids (p : BitVec 64) (dst src : BitVec 5) (c : Bool)
    (s : RamState) (code : CodeMap) : (adcR64R64Effect p dst src c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def adcR32R32Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := (Operand.reg src : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
    (a + b + BitVec.ofNat 32 c.toNat).setWidth 64⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR32R32Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (c : Bool) (s : RamState) :
    (adcR32R32Effect p len dst src c s).components = [.reg dst, .flags, .rip] := rfl

theorem adcR32R32Effect_avoids (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (c : Bool)
    (s : RamState) (code : CodeMap) : (adcR32R32Effect p len dst src c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def adcR16R16Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := (Operand.reg src : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (a + b + BitVec.ofNat 16 c.toNat) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR16R16Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (c : Bool) (s : RamState) :
    (adcR16R16Effect p len dst src c s).components = [.reg dst, .flags, .rip] := rfl

theorem adcR16R16Effect_avoids (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (c : Bool)
    (s : RamState) (code : CodeMap) : (adcR16R16Effect p len dst src c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem adc_r64_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8) (c : Bool)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [rex, 0x11, modrm])
      (adcR64R64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_r64_r64_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), adc_r64_r64_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r64_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8) (c : Bool)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [rex, 0x11, modrm])
      (Effect.post (adcR64R64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) c)) :=
  Triple.of_effect (fun s _ => adcR64R64Effect_avoids p _ _ _ s _)
    (adc_r64_r64_effect_step p rex modrm c hrex hmod)

theorem adc_r32_r32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (c : Bool)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x11, modrm])
      (adcR32R32Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)) c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_r32_r32_step s h modrm hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), adc_r32_r32_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r32_r32_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8) (c : Bool)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x11, modrm])
      (Effect.post (adcR32R32Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)) c)) :=
  Triple.of_effect (fun s _ => adcR32R32Effect_avoids p _ _ _ _ s _)
    (adc_r32_r32_effect_step p modrm c hmod)

theorem adc_r32_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8) (c : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [rex, 0x11, modrm])
      (adcR32R32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_r32_r32_rex_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), adc_r32_r32_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r32_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8) (c : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [rex, 0x11, modrm])
      (Effect.post (adcR32R32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) c)) :=
  Triple.of_effect (fun s _ => adcR32R32Effect_avoids p _ _ _ _ s _)
    (adc_r32_r32_rex_effect_step p rex modrm c hrex hmod)

theorem adc_r16_r16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (c : Bool)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x66, 0x11, modrm])
      (adcR16R16Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)) c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_r16_r16_step s h modrm hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), adc_r16_r16_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r16_r16_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8) (c : Bool)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x66, 0x11, modrm])
      (Effect.post (adcR16R16Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)) c)) :=
  Triple.of_effect (fun s _ => adcR16R16Effect_avoids p _ _ _ _ s _)
    (adc_r16_r16_effect_step p modrm c hmod)

theorem adc_r16_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8) (c : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x66, rex, 0x11, modrm])
      (adcR16R16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_r16_r16_rex_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), adc_r16_r16_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r16_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8) (c : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x66, rex, 0x11, modrm])
      (Effect.post (adcR16R16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) c)) :=
  Triple.of_effect (fun s _ => adcR16R16Effect_avoids p _ _ _ _ s _)
    (adc_r16_r16_rex_effect_step p rex modrm c hrex hmod)

theorem adc_r64_r64_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcR64R64 dst src))
      (Effect.post (adcR64R64Effect p (dst.setWidth 5) (src.setWidth 5) c)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeAdcR64R64_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact adc_r64_r64_triple_of_bytes p rex modrm c hrex hmod

theorem adc_r32_r32_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcR32R32 dst src))
      (Effect.post (adcR32R32Effect p (encodeAdcR32R32 dst src).length (dst.setWidth 5)
        (src.setWidth 5) c)) := by
  rcases encodeAdcR32R32_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact adc_r32_r32_triple_of_bytes p modrm c hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact adc_r32_r32_rex_triple_of_bytes p rex modrm c hrex hmod

theorem adc_r16_r16_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcR16R16 dst src))
      (Effect.post (adcR16R16Effect p (encodeAdcR16R16 dst src).length (dst.setWidth 5)
        (src.setWidth 5) c)) := by
  rcases encodeAdcR16R16_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact adc_r16_r16_triple_of_bytes p modrm c hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact adc_r16_r16_rex_triple_of_bytes p rex modrm c hrex hmod

attribute [x86_compose] adcR64R64Effect adcR32R32Effect adcR16R16Effect

@[x86_local] theorem adcR64R64Effect_local {p : BitVec 64} {dst src : BitVec 5}
    {c : Bool} :
    Effect.Local (adcR64R64Effect p dst src c) := by
  effect_local [adcR64R64Effect]

@[x86_local] theorem adcR32R32Effect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5}
    {c : Bool} :
    Effect.Local (adcR32R32Effect p len dst src c) := by
  effect_local [adcR32R32Effect]

@[x86_local] theorem adcR16R16Effect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5}
    {c : Bool} :
    Effect.Local (adcR16R16Effect p len dst src c) := by
  effect_local [adcR16R16Effect]

end X86Proofs
