import X86Proofs.Instructions.Sub.Generated.Imm8.Step
import X86Proofs.Instructions.Sub.Generated.Imm8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def subR64Imm8Effect (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64), a - b⟩]
    flags := some (.ofStatusFlags (subSpec a b).2) }

@[simp] theorem subR64Imm8Effect_components (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8)
    (s : RamState) :
    (subR64Imm8Effect p dst imm s).components = [.reg dst, .flags, .rip] := rfl

theorem subR64Imm8Effect_avoids (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (s : RamState)
    (code : CodeMap) : (subR64Imm8Effect p dst imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem sub_r64_imm8_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0x83 :: modrm :: immBytes 8 imm))
      (subR64Imm8Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, sub_r64_imm8_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sub_r64_imm8_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, subSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sub_r64_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 5) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0x83 :: modrm :: immBytes 8 imm))
      (Effect.post (subR64Imm8Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => subR64Imm8Effect_avoids p _ _ s _)
    (sub_r64_imm8_effect_step p rex modrm imm hrex hmod hreg)

theorem sub_r64_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSubR64Imm8 dst imm))
      (Effect.post (subR64Imm8Effect p (dst.setWidth 5) imm)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeSubR64Imm8_spec dst imm
  rw [hbytes, ← hdst]
  exact sub_r64_imm8_triple_of_bytes p rex modrm imm hrex hmod hreg

def subR32Imm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (a - b).setWidth 64⟩]
    flags := some (.ofStatusFlags (subSpec a b).2) }

@[simp] theorem subR32Imm8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8)
    (s : RamState) :
    (subR32Imm8Effect p len dst imm s).components = [.reg dst, .flags, .rip] := rfl

theorem subR32Imm8Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (s : RamState)
    (code : CodeMap) : (subR32Imm8Effect p len dst imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem sub_r32_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x83 :: modrm :: immBytes 8 imm))
      (subR32Imm8Effect p 3 (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, sub_r32_imm8_step s h modrm imm hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sub_r32_imm8_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, subSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sub_r32_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 5) :
    Triple (fun s => s.RIP = p) (codeRange p (0x83 :: modrm :: immBytes 8 imm))
      (Effect.post (subR32Imm8Effect p 3 (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => subR32Imm8Effect_avoids p _ _ _ s _)
    (sub_r32_imm8_effect_step p modrm imm hmod hreg)

theorem sub_r32_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0x83 :: modrm :: immBytes 8 imm))
      (subR32Imm8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, sub_r32_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sub_r32_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, subSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sub_r32_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 5) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0x83 :: modrm :: immBytes 8 imm))
      (Effect.post (subR32Imm8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => subR32Imm8Effect_avoids p _ _ _ s _)
    (sub_r32_imm8_rex_effect_step p rex modrm imm hrex hmod hreg)

theorem sub_r32_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSubR32Imm8 dst imm))
      (Effect.post (subR32Imm8Effect p (encodeSubR32Imm8 dst imm).length (dst.setWidth 5) imm)) := by
  rcases encodeSubR32Imm8_spec dst imm with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    simpa using sub_r32_imm8_triple_of_bytes p modrm imm hmod hreg
  · rw [hbytes, ← hdst]
    simpa using sub_r32_imm8_rex_triple_of_bytes p rex modrm imm hrex hmod hreg

def subR16Imm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (a - b) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (subSpec a b).2) }

@[simp] theorem subR16Imm8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8)
    (s : RamState) :
    (subR16Imm8Effect p len dst imm s).components = [.reg dst, .flags, .rip] := rfl

theorem subR16Imm8Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (s : RamState)
    (code : CodeMap) : (subR16Imm8Effect p len dst imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem sub_r16_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x66 :: 0x83 :: modrm :: immBytes 8 imm))
      (subR16Imm8Effect p 4 (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, sub_r16_imm8_step s h modrm imm hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sub_r16_imm8_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, subSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sub_r16_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 5) :
    Triple (fun s => s.RIP = p) (codeRange p (0x66 :: 0x83 :: modrm :: immBytes 8 imm))
      (Effect.post (subR16Imm8Effect p 4 (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => subR16Imm8Effect_avoids p _ _ _ s _)
    (sub_r16_imm8_effect_step p modrm imm hmod hreg)

theorem sub_r16_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x66 :: rex :: 0x83 :: modrm :: immBytes 8 imm))
      (subR16Imm8Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, sub_r16_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sub_r16_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 5 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 5 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, subSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sub_r16_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 5) :
    Triple (fun s => s.RIP = p) (codeRange p (0x66 :: rex :: 0x83 :: modrm :: immBytes 8 imm))
      (Effect.post (subR16Imm8Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => subR16Imm8Effect_avoids p _ _ _ s _)
    (sub_r16_imm8_rex_effect_step p rex modrm imm hrex hmod hreg)

theorem sub_r16_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSubR16Imm8 dst imm))
      (Effect.post (subR16Imm8Effect p (encodeSubR16Imm8 dst imm).length (dst.setWidth 5) imm)) := by
  rcases encodeSubR16Imm8_spec dst imm with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    simpa using sub_r16_imm8_triple_of_bytes p modrm imm hmod hreg
  · rw [hbytes, ← hdst]
    simpa using sub_r16_imm8_rex_triple_of_bytes p rex modrm imm hrex hmod hreg

attribute [x86_compose] subR64Imm8Effect subR32Imm8Effect subR16Imm8Effect

@[x86_local] theorem subR64Imm8Effect_local {p : BitVec 64} {dst : BitVec 5} {imm8 : BitVec 8} :
    Effect.Local (subR64Imm8Effect p dst imm8) := by
  effect_local [subR64Imm8Effect]

@[x86_local] theorem subR32Imm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {imm8 : BitVec 8} :
    Effect.Local (subR32Imm8Effect p len dst imm8) := by
  effect_local [subR32Imm8Effect]

@[x86_local] theorem subR16Imm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {imm8 : BitVec 8} :
    Effect.Local (subR16Imm8Effect p len dst imm8) := by
  effect_local [subR16Imm8Effect]

end X86Proofs
