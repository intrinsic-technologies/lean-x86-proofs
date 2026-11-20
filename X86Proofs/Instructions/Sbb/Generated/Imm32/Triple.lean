import X86Proofs.Instructions.Sbb.Generated.Imm32.Step
import X86Proofs.Instructions.Sbb.Generated.Imm32.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def sbbR64Imm32Effect (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + 7
    writes := [⟨(Operand.reg dst : Operand 64), a - (b + BitVec.ofNat 64 c.toNat)⟩]
    flags := some (.ofStatusFlags (sbbSpec c a b).2) }

@[simp] theorem sbbR64Imm32Effect_components (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32)
    (c : Bool) (s : RamState) :
    (sbbR64Imm32Effect p dst imm c s).components = [.reg dst, .flags, .rip] := rfl

theorem sbbR64Imm32Effect_avoids (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32)
    (c : Bool) (s : RamState) (code : CodeMap) : (sbbR64Imm32Effect p dst imm c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem sbb_r64_imm32_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 32) (c : Bool) (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x81 :: modrm :: immBytes 32 imm))
      (sbbR64Imm32Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, sbb_r64_imm32_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sbb_r64_imm32_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 7 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 7 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, sbbSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sbb_r64_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 32) (c : Bool) (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x81 :: modrm :: immBytes 32 imm))
      (Effect.post (sbbR64Imm32Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm c)) :=
  Triple.of_effect (fun s _ => sbbR64Imm32Effect_avoids p _ _ _ s _)
    (sbb_r64_imm32_effect_step p rex modrm imm c hrex hmod hreg)

theorem sbb_r64_imm32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 32)
    (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeSbbR64Imm32 dst imm))
      (Effect.post (sbbR64Imm32Effect p (dst.setWidth 5) imm c)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeSbbR64Imm32_spec dst imm
  rw [hbytes, ← hdst]
  exact sbb_r64_imm32_triple_of_bytes p rex modrm imm c hrex hmod hreg

def sbbR32Imm32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (a - (b + BitVec.ofNat 32 c.toNat)).setWidth 64⟩]
    flags := some (.ofStatusFlags (sbbSpec c a b).2) }

@[simp] theorem sbbR32Imm32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32)
    (c : Bool) (s : RamState) :
    (sbbR32Imm32Effect p len dst imm c s).components = [.reg dst, .flags, .rip] := rfl

theorem sbbR32Imm32Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32)
    (c : Bool) (s : RamState) (code : CodeMap) : (sbbR32Imm32Effect p len dst imm c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem sbb_r32_imm32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 32) (c : Bool) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x81 :: modrm :: immBytes 32 imm))
      (sbbR32Imm32Effect p 6 (gprNumber 0 0 (modrmRm modrm)) imm c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, sbb_r32_imm32_step s h modrm imm hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sbb_r32_imm32_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 6 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 6 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, sbbSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sbb_r32_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 32) (c : Bool) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x81 :: modrm :: immBytes 32 imm))
      (Effect.post (sbbR32Imm32Effect p 6 (gprNumber 0 0 (modrmRm modrm)) imm c)) :=
  Triple.of_effect (fun s _ => sbbR32Imm32Effect_avoids p _ _ _ _ s _)
    (sbb_r32_imm32_effect_step p modrm imm c hmod hreg)

theorem sbb_r32_imm32_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 32) (c : Bool) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x81 :: modrm :: immBytes 32 imm))
      (sbbR32Imm32Effect p 7 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, sbb_r32_imm32_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sbb_r32_imm32_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 7 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 7 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, sbbSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sbb_r32_imm32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 32) (c : Bool) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x81 :: modrm :: immBytes 32 imm))
      (Effect.post (sbbR32Imm32Effect p 7 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm c)) :=
  Triple.of_effect (fun s _ => sbbR32Imm32Effect_avoids p _ _ _ _ s _)
    (sbb_r32_imm32_rex_effect_step p rex modrm imm c hrex hmod hreg)

theorem sbb_r32_imm32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 32)
    (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeSbbR32Imm32 dst imm))
      (Effect.post (sbbR32Imm32Effect p (encodeSbbR32Imm32 dst imm).length (dst.setWidth 5) imm c)) := by
  rcases encodeSbbR32Imm32_spec dst imm with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    simpa using sbb_r32_imm32_triple_of_bytes p modrm imm c hmod hreg
  · rw [hbytes, ← hdst]
    simpa using sbb_r32_imm32_rex_triple_of_bytes p rex modrm imm c hrex hmod hreg

def sbbR16Imm16Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (a - (b + BitVec.ofNat 16 c.toNat)) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (sbbSpec c a b).2) }

@[simp] theorem sbbR16Imm16Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16)
    (c : Bool) (s : RamState) :
    (sbbR16Imm16Effect p len dst imm c s).components = [.reg dst, .flags, .rip] := rfl

theorem sbbR16Imm16Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16)
    (c : Bool) (s : RamState) (code : CodeMap) : (sbbR16Imm16Effect p len dst imm c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem sbb_r16_imm16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 16) (c : Bool) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x66 :: 0x81 :: modrm :: immBytes 16 imm))
      (sbbR16Imm16Effect p 5 (gprNumber 0 0 (modrmRm modrm)) imm c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, sbb_r16_imm16_step s h modrm imm hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sbb_r16_imm16_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 5 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 5 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, sbbSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sbb_r16_imm16_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 16) (c : Bool) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x66 :: 0x81 :: modrm :: immBytes 16 imm))
      (Effect.post (sbbR16Imm16Effect p 5 (gprNumber 0 0 (modrmRm modrm)) imm c)) :=
  Triple.of_effect (fun s _ => sbbR16Imm16Effect_avoids p _ _ _ _ s _)
    (sbb_r16_imm16_effect_step p modrm imm c hmod hreg)

theorem sbb_r16_imm16_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 16) (c : Bool) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x66 :: rex :: 0x81 :: modrm :: immBytes 16 imm))
      (sbbR16Imm16Effect p 6 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, sbb_r16_imm16_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sbb_r16_imm16_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 6 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 6 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, sbbSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sbb_r16_imm16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 16) (c : Bool) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x66 :: rex :: 0x81 :: modrm :: immBytes 16 imm))
      (Effect.post (sbbR16Imm16Effect p 6 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm c)) :=
  Triple.of_effect (fun s _ => sbbR16Imm16Effect_avoids p _ _ _ _ s _)
    (sbb_r16_imm16_rex_effect_step p rex modrm imm c hrex hmod hreg)

theorem sbb_r16_imm16_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 16)
    (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeSbbR16Imm16 dst imm))
      (Effect.post (sbbR16Imm16Effect p (encodeSbbR16Imm16 dst imm).length (dst.setWidth 5) imm c)) := by
  rcases encodeSbbR16Imm16_spec dst imm with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    simpa using sbb_r16_imm16_triple_of_bytes p modrm imm c hmod hreg
  · rw [hbytes, ← hdst]
    simpa using sbb_r16_imm16_rex_triple_of_bytes p rex modrm imm c hrex hmod hreg

attribute [x86_compose] sbbR64Imm32Effect sbbR32Imm32Effect sbbR16Imm16Effect

@[x86_local] theorem sbbR64Imm32Effect_local {p : BitVec 64} {dst : BitVec 5}
    {imm32 : BitVec 32} {c : Bool} :
    Effect.Local (sbbR64Imm32Effect p dst imm32 c) := by
  effect_local [sbbR64Imm32Effect]

@[x86_local] theorem sbbR32Imm32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {imm32 : BitVec 32} {c : Bool} :
    Effect.Local (sbbR32Imm32Effect p len dst imm32 c) := by
  effect_local [sbbR32Imm32Effect]

@[x86_local] theorem sbbR16Imm16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {imm16 : BitVec 16} {c : Bool} :
    Effect.Local (sbbR16Imm16Effect p len dst imm16 c) := by
  effect_local [sbbR16Imm16Effect]

end X86Proofs
