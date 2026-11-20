import X86Proofs.Instructions.Sub.Generated.R8Imm8.Step
import X86Proofs.Instructions.Sub.Generated.R8Imm8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def subR8Imm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  let b := imm.signExtend 8
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (a - b) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (subSpec a b).2) }

@[simp] theorem subR8Imm8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8)
    (s : RamState) :
    (subR8Imm8Effect p len dst imm s).components = [.reg dst, .flags, .rip] := rfl

theorem subR8Imm8Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (s : RamState)
    (code : CodeMap) : (subR8Imm8Effect p len dst imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem sub_r8_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 5) (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x80 :: modrm :: immBytes 8 imm))
      (subR8Imm8Effect p 3 (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, sub_r8_imm8_step s h modrm imm hmod hreg hrm8 hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sub_r8_imm8_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, subSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sub_r8_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 5) (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p) (codeRange p (0x80 :: modrm :: immBytes 8 imm))
      (Effect.post (subR8Imm8Effect p 3 (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => subR8Imm8Effect_avoids p _ _ _ s _)
    (sub_r8_imm8_effect_step p modrm imm hmod hreg hrm8)

theorem sub_r8_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0x80 :: modrm :: immBytes 8 imm))
      (subR8Imm8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, sub_r8_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sub_r8_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, subSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sub_r8_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 5) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0x80 :: modrm :: immBytes 8 imm))
      (Effect.post (subR8Imm8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => subR8Imm8Effect_avoids p _ _ _ s _)
    (sub_r8_imm8_rex_effect_step p rex modrm imm hrex hmod hreg)

theorem sub_r8_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSubR8Imm8 dst imm))
      (Effect.post (subR8Imm8Effect p (encodeSubR8Imm8 dst imm).length (dst.setWidth 5) imm)) := by
  rcases encodeSubR8Imm8_spec dst imm with ⟨modrm, hbytes, hmod, hreg, hrm8, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    simpa using sub_r8_imm8_triple_of_bytes p modrm imm hmod hreg hrm8
  · rw [hbytes, ← hdst]
    simpa using sub_r8_imm8_rex_triple_of_bytes p rex modrm imm hrex hmod hreg

def subR8Imm8NoRexEffect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let a := (Operand.byteReg dst).read s
  let b := imm.signExtend 8
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (byteRegGpr dst) : Operand 64),
      mergeByteReg dst (a - b)
        ((Operand.reg (byteRegGpr dst) : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (subSpec a b).2) }

@[simp] theorem subR8Imm8NoRexEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (imm : BitVec 8) (s : RamState) :
    (subR8Imm8NoRexEffect p len dst imm s).components =
      [.reg (byteRegGpr dst), .flags, .rip] := rfl

theorem subR8Imm8NoRexEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (imm : BitVec 8) (s : RamState) (code : CodeMap) :
    (subR8Imm8NoRexEffect p len dst imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem sub_r8_imm8_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x80 :: modrm :: immBytes 8 imm))
      (subR8Imm8NoRexEffect p 3 (modrmRm modrm) imm) := by
  rintro s h hcode rfl
  have hs := sub_r8_imm8_norex_step s h modrm imm hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp))
  have hr := sub_r8_imm8_norex_ready h modrm imm
  simp only [writeOutputs_byteReg] at hs hr
  refine ⟨_, hs, hr,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, subSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sub_r8_imm8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    Triple (fun s => s.RIP = p) (codeRange p (0x80 :: modrm :: immBytes 8 imm))
      (Effect.post (subR8Imm8NoRexEffect p 3 (modrmRm modrm) imm)) :=
  Triple.of_effect (fun s _ => subR8Imm8NoRexEffect_avoids p _ _ _ s _)
    (sub_r8_imm8_norex_effect_step p modrm imm hmod hreg)

theorem sub_r8_imm8_norex_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSubR8Imm8NoRex dst imm))
      (Effect.post (subR8Imm8NoRexEffect p 3 dst imm)) := by
  have h := sub_r8_imm8_norex_triple_of_bytes p (modrmRegs 5 dst) imm
    (modrmMod_modrmRegs _ _) (modrmReg_modrmRegs _ _)
  rwa [modrmRm_modrmRegs] at h

attribute [x86_compose] subR8Imm8Effect subR8Imm8NoRexEffect

@[x86_local] theorem subR8Imm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {imm8 : BitVec 8} :
    Effect.Local (subR8Imm8Effect p len dst imm8) := by
  effect_local [subR8Imm8Effect]

@[x86_local] theorem subR8Imm8NoRexEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {imm8 : BitVec 8} :
    Effect.Local (subR8Imm8NoRexEffect p len dst imm8) := by
  effect_local [subR8Imm8NoRexEffect]

end X86Proofs
