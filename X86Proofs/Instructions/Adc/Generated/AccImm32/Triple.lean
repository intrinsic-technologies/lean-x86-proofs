import X86Proofs.Instructions.Adc.Generated.AccImm32.Step
import X86Proofs.Instructions.Adc.Generated.AccImm32.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def adcRaxImm32Effect (p : BitVec 64) (imm : BitVec 32) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + 6
    writes := [⟨(Operand.reg 0 : Operand 64), a + b + BitVec.ofNat 64 c.toNat⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcRaxImm32Effect_components (p : BitVec 64) (imm : BitVec 32)
    (c : Bool) (s : RamState) :
    (adcRaxImm32Effect p imm c s).components = [.reg 0, .flags, .rip] := rfl

theorem adcRaxImm32Effect_avoids (p : BitVec 64) (imm : BitVec 32)
    (c : Bool) (s : RamState) (code : CodeMap) : (adcRaxImm32Effect p imm c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem adc_rax_imm32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (imm : BitVec 32) (c : Bool) (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x15 :: immBytes 32 imm))
      (adcRaxImm32Effect p imm c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_rax_imm32_step s h rex imm hrex hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), adc_rax_imm32_ready h imm,
    ⟨afterStep_writeOutputs_rip h 6 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 6 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_rax_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (imm : BitVec 32) (c : Bool) (hrex : RexWPrefix rex.toBitVec) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x15 :: immBytes 32 imm))
      (Effect.post (adcRaxImm32Effect p imm c)) :=
  Triple.of_effect (fun s _ => adcRaxImm32Effect_avoids p _ _ s _)
    (adc_rax_imm32_effect_step p rex imm c hrex)

theorem adc_rax_imm32_triple [Bindings] (p : BitVec 64) (imm : BitVec 32) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcRaxImm32 imm)) (Effect.post (adcRaxImm32Effect p imm c)) :=
  adc_rax_imm32_triple_of_bytes p 0x48 imm c (by unfold RexWPrefix; decide)

def adcEaxImm32Effect (p : BitVec 64) (imm : BitVec 32) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + 5
    writes := [⟨(Operand.reg 0 : Operand 64), (a + b + BitVec.ofNat 32 c.toNat).setWidth 64⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcEaxImm32Effect_components (p : BitVec 64) (imm : BitVec 32)
    (c : Bool) (s : RamState) :
    (adcEaxImm32Effect p imm c s).components = [.reg 0, .flags, .rip] := rfl

theorem adcEaxImm32Effect_avoids (p : BitVec 64) (imm : BitVec 32)
    (c : Bool) (s : RamState) (code : CodeMap) : (adcEaxImm32Effect p imm c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem adc_eax_imm32_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 32) (c : Bool) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x15 :: immBytes 32 imm))
      (adcEaxImm32Effect p imm c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_eax_imm32_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), adc_eax_imm32_ready h imm,
    ⟨afterStep_writeOutputs_rip h 5 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 5 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_eax_imm32_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 32) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x15 :: immBytes 32 imm))
      (Effect.post (adcEaxImm32Effect p imm c)) :=
  Triple.of_effect (fun s _ => adcEaxImm32Effect_avoids p _ _ s _)
    (adc_eax_imm32_effect_step p imm c)

theorem adc_eax_imm32_triple [Bindings] (p : BitVec 64) (imm : BitVec 32) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcEaxImm32 imm)) (Effect.post (adcEaxImm32Effect p imm c)) :=
  adc_eax_imm32_triple_of_bytes p imm c

def adcAxImm16Effect (p : BitVec 64) (imm : BitVec 16) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + 4
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 16 (a + b + BitVec.ofNat 16 c.toNat) ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcAxImm16Effect_components (p : BitVec 64) (imm : BitVec 16)
    (c : Bool) (s : RamState) :
    (adcAxImm16Effect p imm c s).components = [.reg 0, .flags, .rip] := rfl

theorem adcAxImm16Effect_avoids (p : BitVec 64) (imm : BitVec 16)
    (c : Bool) (s : RamState) (code : CodeMap) : (adcAxImm16Effect p imm c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem adc_ax_imm16_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 16) (c : Bool) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x66 :: 0x15 :: immBytes 16 imm))
      (adcAxImm16Effect p imm c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, adc_ax_imm16_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), adc_ax_imm16_ready h imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_ax_imm16_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 16) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x66 :: 0x15 :: immBytes 16 imm))
      (Effect.post (adcAxImm16Effect p imm c)) :=
  Triple.of_effect (fun s _ => adcAxImm16Effect_avoids p _ _ s _)
    (adc_ax_imm16_effect_step p imm c)

theorem adc_ax_imm16_triple [Bindings] (p : BitVec 64) (imm : BitVec 16) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcAxImm16 imm)) (Effect.post (adcAxImm16Effect p imm c)) :=
  adc_ax_imm16_triple_of_bytes p imm c

attribute [x86_compose] adcRaxImm32Effect adcEaxImm32Effect adcAxImm16Effect

@[x86_local] theorem adcRaxImm32Effect_local {p : BitVec 64} {imm32 : BitVec 32} {c : Bool} :
    Effect.Local (adcRaxImm32Effect p imm32 c) := by
  effect_local [adcRaxImm32Effect]

@[x86_local] theorem adcEaxImm32Effect_local {p : BitVec 64} {imm32 : BitVec 32} {c : Bool} :
    Effect.Local (adcEaxImm32Effect p imm32 c) := by
  effect_local [adcEaxImm32Effect]

@[x86_local] theorem adcAxImm16Effect_local {p : BitVec 64} {imm16 : BitVec 16} {c : Bool} :
    Effect.Local (adcAxImm16Effect p imm16 c) := by
  effect_local [adcAxImm16Effect]

end X86Proofs
