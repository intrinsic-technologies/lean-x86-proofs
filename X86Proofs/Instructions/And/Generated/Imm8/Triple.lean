import X86Proofs.Instructions.And.Generated.Imm8.Step
import X86Proofs.Instructions.And.Generated.Imm8.Encode
import X86Proofs.Program.Compose
import X86Proofs.Instructions.And.Generated.RR.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def andR64Imm8Effect (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64), a &&& b⟩]
    flags := some (andFlags (a &&& b)) }

@[simp] theorem andR64Imm8Effect_components (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8)
    (s : RamState) :
    (andR64Imm8Effect p dst imm s).components = [.reg dst, .flags, .rip] := rfl

theorem andR64Imm8Effect_avoids (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (s : RamState)
    (code : CodeMap) : (andR64Imm8Effect p dst imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem and_r64_imm8_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0x83 :: modrm :: immBytes 8 imm))
      (andR64Imm8Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, and_r64_imm8_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), and_r64_imm8_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, andSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem and_r64_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 4) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0x83 :: modrm :: immBytes 8 imm))
      (Effect.post (andR64Imm8Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => andR64Imm8Effect_avoids p _ _ s _)
    (and_r64_imm8_effect_step p rex modrm imm hrex hmod hreg)

theorem and_r64_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeAndR64Imm8 dst imm))
      (Effect.post (andR64Imm8Effect p (dst.setWidth 5) imm)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeAndR64Imm8_spec dst imm
  rw [hbytes, ← hdst]
  exact and_r64_imm8_triple_of_bytes p rex modrm imm hrex hmod hreg

def andR32Imm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (a &&& b).setWidth 64⟩]
    flags := some (andFlags (a &&& b)) }

@[simp] theorem andR32Imm8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8)
    (s : RamState) :
    (andR32Imm8Effect p len dst imm s).components = [.reg dst, .flags, .rip] := rfl

theorem andR32Imm8Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (s : RamState)
    (code : CodeMap) : (andR32Imm8Effect p len dst imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem and_r32_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x83 :: modrm :: immBytes 8 imm))
      (andR32Imm8Effect p 3 (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, and_r32_imm8_step s h modrm imm hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), and_r32_imm8_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, andSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem and_r32_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 4) :
    Triple (fun s => s.RIP = p) (codeRange p (0x83 :: modrm :: immBytes 8 imm))
      (Effect.post (andR32Imm8Effect p 3 (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => andR32Imm8Effect_avoids p _ _ _ s _)
    (and_r32_imm8_effect_step p modrm imm hmod hreg)

theorem and_r32_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0x83 :: modrm :: immBytes 8 imm))
      (andR32Imm8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, and_r32_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), and_r32_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, andSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem and_r32_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 4) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0x83 :: modrm :: immBytes 8 imm))
      (Effect.post (andR32Imm8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => andR32Imm8Effect_avoids p _ _ _ s _)
    (and_r32_imm8_rex_effect_step p rex modrm imm hrex hmod hreg)

theorem and_r32_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeAndR32Imm8 dst imm))
      (Effect.post (andR32Imm8Effect p (encodeAndR32Imm8 dst imm).length (dst.setWidth 5) imm)) := by
  rcases encodeAndR32Imm8_spec dst imm with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    simpa using and_r32_imm8_triple_of_bytes p modrm imm hmod hreg
  · rw [hbytes, ← hdst]
    simpa using and_r32_imm8_rex_triple_of_bytes p rex modrm imm hrex hmod hreg

def andR16Imm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (a &&& b) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (andFlags (a &&& b)) }

@[simp] theorem andR16Imm8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8)
    (s : RamState) :
    (andR16Imm8Effect p len dst imm s).components = [.reg dst, .flags, .rip] := rfl

theorem andR16Imm8Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (s : RamState)
    (code : CodeMap) : (andR16Imm8Effect p len dst imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem and_r16_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x66 :: 0x83 :: modrm :: immBytes 8 imm))
      (andR16Imm8Effect p 4 (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, and_r16_imm8_step s h modrm imm hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), and_r16_imm8_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, andSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem and_r16_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 4) :
    Triple (fun s => s.RIP = p) (codeRange p (0x66 :: 0x83 :: modrm :: immBytes 8 imm))
      (Effect.post (andR16Imm8Effect p 4 (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => andR16Imm8Effect_avoids p _ _ _ s _)
    (and_r16_imm8_effect_step p modrm imm hmod hreg)

theorem and_r16_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x66 :: rex :: 0x83 :: modrm :: immBytes 8 imm))
      (andR16Imm8Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, and_r16_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), and_r16_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 5 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 5 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, andSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem and_r16_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 4) :
    Triple (fun s => s.RIP = p) (codeRange p (0x66 :: rex :: 0x83 :: modrm :: immBytes 8 imm))
      (Effect.post (andR16Imm8Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => andR16Imm8Effect_avoids p _ _ _ s _)
    (and_r16_imm8_rex_effect_step p rex modrm imm hrex hmod hreg)

theorem and_r16_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeAndR16Imm8 dst imm))
      (Effect.post (andR16Imm8Effect p (encodeAndR16Imm8 dst imm).length (dst.setWidth 5) imm)) := by
  rcases encodeAndR16Imm8_spec dst imm with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    simpa using and_r16_imm8_triple_of_bytes p modrm imm hmod hreg
  · rw [hbytes, ← hdst]
    simpa using and_r16_imm8_rex_triple_of_bytes p rex modrm imm hrex hmod hreg

attribute [x86_compose] andR64Imm8Effect andR32Imm8Effect andR16Imm8Effect

@[x86_local] theorem andR64Imm8Effect_local {p : BitVec 64} {dst : BitVec 5} {imm8 : BitVec 8} :
    Effect.Local (andR64Imm8Effect p dst imm8) := by
  effect_local [andR64Imm8Effect]

@[x86_local] theorem andR32Imm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {imm8 : BitVec 8} :
    Effect.Local (andR32Imm8Effect p len dst imm8) := by
  effect_local [andR32Imm8Effect]

@[x86_local] theorem andR16Imm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {imm8 : BitVec 8} :
    Effect.Local (andR16Imm8Effect p len dst imm8) := by
  effect_local [andR16Imm8Effect]

end X86Proofs
