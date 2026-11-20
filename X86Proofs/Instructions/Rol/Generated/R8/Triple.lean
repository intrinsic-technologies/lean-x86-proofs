import X86Proofs.Instructions.Rol.Generated.R8.Step
import X86Proofs.Instructions.Rol.Generated.R8.Encode
import X86Proofs.Program.Compose
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def rolR8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (a.rotateLeft c) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (rolFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[simp] theorem rolR8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat)
    (s : RamState) : (rolR8Effect p len dst c s).components = [.reg dst, .flags, .rip] := rfl

theorem rolR8Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState)
    (code : CodeMap) : (rolR8Effect p len dst c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem rol_r8_imm8_effect_step [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xC0, modrm, imm])
      (rolR8Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 8 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, rol_r8_imm8_step s h modrm imm hmod hreg hrm8 hcode.bytesAt
    (hcode.low (by simp) (by simp)), rol_r8_imm8_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rolSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rolFlags_allows

theorem rol_r8_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p) (codeRange p [0xC0, modrm, imm])
      (Effect.post (rolR8Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 8 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => rolR8Effect_avoids p _ _ _ s _)
    (rol_r8_imm8_effect_step p modrm imm hmod hreg hrm8)

theorem rol_r8_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xC0, modrm, imm])
      (rolR8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 8 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, rol_r8_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rol_r8_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rolSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rolFlags_allows

theorem rol_r8_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xC0, modrm, imm])
      (Effect.post (rolR8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 8 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => rolR8Effect_avoids p _ _ _ s _)
    (rol_r8_imm8_rex_effect_step p rex modrm imm hrex hmod hreg)

theorem rol_r8_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRolR8Imm8 dst imm))
      (Effect.post (rolR8Effect p
        (encodeRolR8Imm8 dst imm).length (dst.setWidth 5)
        (shiftCount 8 imm))) := by
  rcases encodeRolR8Imm8_spec imm dst with ⟨modrm, hbytes, hmod, hreg, hrm8, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst, immBytes_eight]
    exact rol_r8_imm8_triple_of_bytes p modrm (UInt8.ofBitVec imm) hmod hreg hrm8
  · rw [hbytes, ← hdst, immBytes_eight]
    exact rol_r8_imm8_rex_triple_of_bytes p rex modrm (UInt8.ofBitVec imm) hrex hmod hreg

theorem rol_r8_one_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xD0, modrm])
      (rolR8Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, rol_r8_one_step s h modrm hmod hreg hrm8 hcode.bytesAt
    (hcode.low (by simp) (by simp)), rol_r8_one_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rolSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rolFlags_allows

theorem rol_r8_one_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p) (codeRange p [0xD0, modrm])
      (Effect.post (rolR8Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => rolR8Effect_avoids p _ _ _ s _)
    (rol_r8_one_effect_step p modrm hmod hreg hrm8)

theorem rol_r8_one_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD0, modrm])
      (rolR8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, rol_r8_one_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rol_r8_one_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rolSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rolFlags_allows

theorem rol_r8_one_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xD0, modrm])
      (Effect.post (rolR8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => rolR8Effect_avoids p _ _ _ s _)
    (rol_r8_one_rex_effect_step p rex modrm hrex hmod hreg)

theorem rol_r8_one_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRolR8One dst))
      (Effect.post (rolR8Effect p
        (encodeRolR8One dst).length (dst.setWidth 5)
        (1))) := by
  rcases encodeRolR8One_spec dst with ⟨modrm, hbytes, hmod, hreg, hrm8, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact rol_r8_one_triple_of_bytes p modrm hmod hreg hrm8
  · rw [hbytes, ← hdst]
    exact rol_r8_one_rex_triple_of_bytes p rex modrm hrex hmod hreg

def rolR8NoRexEffect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (c : Nat)
    (s : RamState) : Effect :=
  let a := (Operand.byteReg dst).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (byteRegGpr dst) : Operand 64),
      mergeByteReg dst (a.rotateLeft c)
        ((Operand.reg (byteRegGpr dst) : Operand 64).read s)⟩]
    flags := some (rolFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[simp] theorem rolR8NoRexEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (c : Nat) (s : RamState) :
    (rolR8NoRexEffect p len dst c s).components = [.reg (byteRegGpr dst), .flags, .rip] :=
  rfl

theorem rolR8NoRexEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 3) (c : Nat)
    (s : RamState) (code : CodeMap) : (rolR8NoRexEffect p len dst c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem rol_r8_imm8_norex_effect_step [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xC0, modrm, imm])
      (rolR8NoRexEffect p 3 (modrmRm modrm) (shiftCount 8 imm.toBitVec)) := by
  rintro s h hcode rfl
  have hs := rol_r8_imm8_norex_step s h modrm imm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp))
  have hr := rol_r8_imm8_norex_ready h modrm imm
  simp only [writeOutputs_byteReg] at hs hr
  refine ⟨_, hs, hr,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, rolSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    apply rolFlags_allows

theorem rol_r8_imm8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [0xC0, modrm, imm])
      (Effect.post (rolR8NoRexEffect p 3 (modrmRm modrm) (shiftCount 8 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => rolR8NoRexEffect_avoids p _ _ _ s _)
    (rol_r8_imm8_norex_effect_step p modrm imm hmod hreg)

theorem rol_r8_imm8_norex_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRolR8Imm8NoRex dst imm))
      (Effect.post (rolR8NoRexEffect p 3 dst (shiftCount 8 imm))) := by
  unfold encodeRolR8Imm8NoRex
  rw [immBytes_eight]
  have h := rol_r8_imm8_norex_triple_of_bytes p (modrmRegs 0 dst) (UInt8.ofBitVec imm)
    (modrmMod_modrmRegs _ _) (modrmReg_modrmRegs _ _)
  rwa [modrmRm_modrmRegs] at h

theorem rol_r8_one_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xD0, modrm])
      (rolR8NoRexEffect p 2 (modrmRm modrm) (1)) := by
  rintro s h hcode rfl
  have hs := rol_r8_one_norex_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp))
  have hr := rol_r8_one_norex_ready h modrm
  simp only [writeOutputs_byteReg] at hs hr
  refine ⟨_, hs, hr,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, rolSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    apply rolFlags_allows

theorem rol_r8_one_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [0xD0, modrm])
      (Effect.post (rolR8NoRexEffect p 2 (modrmRm modrm) (1))) :=
  Triple.of_effect (fun s _ => rolR8NoRexEffect_avoids p _ _ _ s _)
    (rol_r8_one_norex_effect_step p modrm hmod hreg)

theorem rol_r8_one_norex_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRolR8OneNoRex dst))
      (Effect.post (rolR8NoRexEffect p 2 dst (1))) := by
  have h := rol_r8_one_norex_triple_of_bytes p (modrmRegs 0 dst)
    (modrmMod_modrmRegs _ _) (modrmReg_modrmRegs _ _)
  rwa [modrmRm_modrmRegs] at h

attribute [x86_compose] rolR8Effect rolR8NoRexEffect

@[x86_local] theorem rolR8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {c : Nat} :
    Effect.Local (rolR8Effect p len dst c) := by
  effect_local [rolR8Effect, rolFlags]

@[x86_local] theorem rolR8NoRexEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3} {c : Nat} :
    Effect.Local (rolR8NoRexEffect p len dst c) := by
  effect_local [rolR8NoRexEffect, rolFlags]

end X86Proofs
