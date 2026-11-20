import X86Proofs.Instructions.Shl.Generated.R8.Step
import X86Proofs.Instructions.Shl.Generated.R8.Encode
import X86Proofs.Program.Compose
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def shlR8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (a <<< c) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (shlFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[simp] theorem shlR8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat)
    (s : RamState) : (shlR8Effect p len dst c s).components = [.reg dst, .flags, .rip] := rfl

theorem shlR8Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState)
    (code : CodeMap) : (shlR8Effect p len dst c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem shl_r8_imm8_effect_step [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xC0, modrm, imm])
      (shlR8Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 8 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, shl_r8_imm8_step s h modrm imm hmod hreg hrm8 hcode.bytesAt
    (hcode.low (by simp) (by simp)), shl_r8_imm8_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem shl_r8_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p) (codeRange p [0xC0, modrm, imm])
      (Effect.post (shlR8Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 8 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => shlR8Effect_avoids p _ _ _ s _)
    (shl_r8_imm8_effect_step p modrm imm hmod hreg hrm8)

theorem shl_r8_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xC0, modrm, imm])
      (shlR8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 8 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, shl_r8_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), shl_r8_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem shl_r8_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xC0, modrm, imm])
      (Effect.post (shlR8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 8 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => shlR8Effect_avoids p _ _ _ s _)
    (shl_r8_imm8_rex_effect_step p rex modrm imm hrex hmod hreg)

theorem shl_r8_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeShlR8Imm8 dst imm))
      (Effect.post (shlR8Effect p
        (encodeShlR8Imm8 dst imm).length (dst.setWidth 5)
        (shiftCount 8 imm))) := by
  rcases encodeShlR8Imm8_spec imm dst with ⟨modrm, hbytes, hmod, hreg, hrm8, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst, immBytes_eight]
    exact shl_r8_imm8_triple_of_bytes p modrm (UInt8.ofBitVec imm) hmod hreg hrm8
  · rw [hbytes, ← hdst, immBytes_eight]
    exact shl_r8_imm8_rex_triple_of_bytes p rex modrm (UInt8.ofBitVec imm) hrex hmod hreg

theorem shl_r8_one_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xD0, modrm])
      (shlR8Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, shl_r8_one_step s h modrm hmod hreg hrm8 hcode.bytesAt
    (hcode.low (by simp) (by simp)), shl_r8_one_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem shl_r8_one_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p) (codeRange p [0xD0, modrm])
      (Effect.post (shlR8Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => shlR8Effect_avoids p _ _ _ s _)
    (shl_r8_one_effect_step p modrm hmod hreg hrm8)

theorem shl_r8_one_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD0, modrm])
      (shlR8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, shl_r8_one_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), shl_r8_one_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem shl_r8_one_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xD0, modrm])
      (Effect.post (shlR8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => shlR8Effect_avoids p _ _ _ s _)
    (shl_r8_one_rex_effect_step p rex modrm hrex hmod hreg)

theorem shl_r8_one_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeShlR8One dst))
      (Effect.post (shlR8Effect p
        (encodeShlR8One dst).length (dst.setWidth 5)
        (1))) := by
  rcases encodeShlR8One_spec dst with ⟨modrm, hbytes, hmod, hreg, hrm8, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact shl_r8_one_triple_of_bytes p modrm hmod hreg hrm8
  · rw [hbytes, ← hdst]
    exact shl_r8_one_rex_triple_of_bytes p rex modrm hrex hmod hreg

def shlR8NoRexEffect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (c : Nat)
    (s : RamState) : Effect :=
  let a := (Operand.byteReg dst).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (byteRegGpr dst) : Operand 64),
      mergeByteReg dst (a <<< c)
        ((Operand.reg (byteRegGpr dst) : Operand 64).read s)⟩]
    flags := some (shlFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[simp] theorem shlR8NoRexEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (c : Nat) (s : RamState) :
    (shlR8NoRexEffect p len dst c s).components = [.reg (byteRegGpr dst), .flags, .rip] :=
  rfl

theorem shlR8NoRexEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 3) (c : Nat)
    (s : RamState) (code : CodeMap) : (shlR8NoRexEffect p len dst c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem shl_r8_imm8_norex_effect_step [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xC0, modrm, imm])
      (shlR8NoRexEffect p 3 (modrmRm modrm) (shiftCount 8 imm.toBitVec)) := by
  rintro s h hcode rfl
  have hs := shl_r8_imm8_norex_step s h modrm imm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp))
  have hr := shl_r8_imm8_norex_ready h modrm imm
  simp only [writeOutputs_byteReg] at hs hr
  refine ⟨_, hs, hr,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    apply shlFlags_allows

theorem shl_r8_imm8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    Triple (fun s => s.RIP = p) (codeRange p [0xC0, modrm, imm])
      (Effect.post (shlR8NoRexEffect p 3 (modrmRm modrm) (shiftCount 8 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => shlR8NoRexEffect_avoids p _ _ _ s _)
    (shl_r8_imm8_norex_effect_step p modrm imm hmod hreg)

theorem shl_r8_imm8_norex_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeShlR8Imm8NoRex dst imm))
      (Effect.post (shlR8NoRexEffect p 3 dst (shiftCount 8 imm))) := by
  unfold encodeShlR8Imm8NoRex
  rw [immBytes_eight]
  have h := shl_r8_imm8_norex_triple_of_bytes p (modrmRegs 4 dst) (UInt8.ofBitVec imm)
    (modrmMod_modrmRegs _ _) (modrmReg_modrmRegs _ _)
  rwa [modrmRm_modrmRegs] at h

theorem shl_r8_one_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xD0, modrm])
      (shlR8NoRexEffect p 2 (modrmRm modrm) (1)) := by
  rintro s h hcode rfl
  have hs := shl_r8_one_norex_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp))
  have hr := shl_r8_one_norex_ready h modrm
  simp only [writeOutputs_byteReg] at hs hr
  refine ⟨_, hs, hr,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    apply shlFlags_allows

theorem shl_r8_one_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    Triple (fun s => s.RIP = p) (codeRange p [0xD0, modrm])
      (Effect.post (shlR8NoRexEffect p 2 (modrmRm modrm) (1))) :=
  Triple.of_effect (fun s _ => shlR8NoRexEffect_avoids p _ _ _ s _)
    (shl_r8_one_norex_effect_step p modrm hmod hreg)

theorem shl_r8_one_norex_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeShlR8OneNoRex dst))
      (Effect.post (shlR8NoRexEffect p 2 dst (1))) := by
  have h := shl_r8_one_norex_triple_of_bytes p (modrmRegs 4 dst)
    (modrmMod_modrmRegs _ _) (modrmReg_modrmRegs _ _)
  rwa [modrmRm_modrmRegs] at h

attribute [x86_compose] shlR8Effect shlR8NoRexEffect

@[x86_local] theorem shlR8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {c : Nat} :
    Effect.Local (shlR8Effect p len dst c) := by
  effect_local [shlR8Effect, shlFlags]

@[x86_local] theorem shlR8NoRexEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3} {c : Nat} :
    Effect.Local (shlR8NoRexEffect p len dst c) := by
  effect_local [shlR8NoRexEffect, shlFlags]

end X86Proofs
