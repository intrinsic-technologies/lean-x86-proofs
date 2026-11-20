import X86Proofs.Instructions.Ror.Generated.R8Cl.Step
import X86Proofs.Instructions.Ror.Generated.R8Cl.Encode
import X86Proofs.Instructions.Ror.Generated.R8.Triple
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def rorR8ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  rorR8Effect p len dst (shiftCount 8 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem rorR8ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (rorR8ClEffect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem rorR8ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (rorR8ClEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem ror_r8_cl_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xD2, modrm])
      (rorR8ClEffect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, ror_r8_cl_step s h modrm hmod hreg hrm8 hcode.bytesAt
    (hcode.low (by simp) (by simp)), ror_r8_cl_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rorFlags_allows

theorem ror_r8_cl_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p) (codeRange p [0xD2, modrm])
      (Effect.post (rorR8ClEffect p 2 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => rorR8ClEffect_avoids p _ _ s _)
    (ror_r8_cl_effect_step p modrm hmod hreg hrm8)

theorem ror_r8_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD2, modrm])
      (rorR8ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, ror_r8_cl_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), ror_r8_cl_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rorFlags_allows

theorem ror_r8_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xD2, modrm])
      (Effect.post (rorR8ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => rorR8ClEffect_avoids p _ _ s _)
    (ror_r8_cl_rex_effect_step p rex modrm hrex hmod hreg)

theorem ror_r8_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRorR8Cl dst))
      (Effect.post (rorR8ClEffect p
        (encodeRorR8Cl dst).length (dst.setWidth 5))) := by
  rcases encodeRorR8Cl_spec dst with ⟨modrm, hbytes, hmod, hreg, hrm8, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact ror_r8_cl_triple_of_bytes p modrm hmod hreg hrm8
  · rw [hbytes, ← hdst]
    exact ror_r8_cl_rex_triple_of_bytes p rex modrm hrex hmod hreg

def rorR8ClNoRexEffect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (s : RamState) :
    Effect :=
  rorR8NoRexEffect p len dst (shiftCount 8 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem rorR8ClNoRexEffect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 3) (s : RamState) :
    (rorR8ClNoRexEffect p len dst s).components = [.reg (byteRegGpr dst), .flags, .rip] :=
  rfl

theorem rorR8ClNoRexEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (s : RamState) (code : CodeMap) : (rorR8ClNoRexEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem ror_r8_cl_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xD2, modrm])
      (rorR8ClNoRexEffect p 2 (modrmRm modrm)) := by
  rintro s h hcode rfl
  have hs := ror_r8_cl_norex_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp))
  have hr := ror_r8_cl_norex_ready h modrm
  simp only [writeOutputs_byteReg] at hs hr
  refine ⟨_, hs, hr,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, rorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    apply rorFlags_allows

theorem ror_r8_cl_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [0xD2, modrm])
      (Effect.post (rorR8ClNoRexEffect p 2 (modrmRm modrm))) :=
  Triple.of_effect (fun s _ => rorR8ClNoRexEffect_avoids p _ _ s _)
    (ror_r8_cl_norex_effect_step p modrm hmod hreg)

theorem ror_r8_cl_norex_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRorR8ClNoRex dst))
      (Effect.post (rorR8ClNoRexEffect p 2 dst)) := by
  have h := ror_r8_cl_norex_triple_of_bytes p (modrmRegs 1 dst)
    (modrmMod_modrmRegs _ _) (modrmReg_modrmRegs _ _)
  rwa [modrmRm_modrmRegs] at h

attribute [x86_compose] rorR8ClEffect rorR8ClNoRexEffect

@[x86_local] theorem rorR8ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (rorR8ClEffect p len dst) :=
  Effect.Local.of_param (e := fun c => rorR8Effect p len dst c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => rorR8Effect_local

@[x86_local] theorem rorR8ClNoRexEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3} :
    Effect.Local (rorR8ClNoRexEffect p len dst) :=
  Effect.Local.of_param (e := fun c => rorR8NoRexEffect p len dst c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => rorR8NoRexEffect_local

end X86Proofs
