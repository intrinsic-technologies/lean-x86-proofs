import X86Proofs.Instructions.Shr.Generated.R8Cl.Step
import X86Proofs.Instructions.Shr.Generated.R8Cl.Encode
import X86Proofs.Instructions.Shr.Generated.R8.Triple
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def shrR8ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  shrR8Effect p len dst (shiftCount 8 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem shrR8ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (shrR8ClEffect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem shrR8ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (shrR8ClEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem shr_r8_cl_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xD2, modrm])
      (shrR8ClEffect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, shr_r8_cl_step s h modrm hmod hreg hrm8 hcode.bytesAt
    (hcode.low (by simp) (by simp)), shr_r8_cl_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, shrSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shrFlags_allows

theorem shr_r8_cl_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p) (codeRange p [0xD2, modrm])
      (Effect.post (shrR8ClEffect p 2 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => shrR8ClEffect_avoids p _ _ s _)
    (shr_r8_cl_effect_step p modrm hmod hreg hrm8)

theorem shr_r8_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD2, modrm])
      (shrR8ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, shr_r8_cl_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), shr_r8_cl_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, shrSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shrFlags_allows

theorem shr_r8_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xD2, modrm])
      (Effect.post (shrR8ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => shrR8ClEffect_avoids p _ _ s _)
    (shr_r8_cl_rex_effect_step p rex modrm hrex hmod hreg)

theorem shr_r8_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeShrR8Cl dst))
      (Effect.post (shrR8ClEffect p
        (encodeShrR8Cl dst).length (dst.setWidth 5))) := by
  rcases encodeShrR8Cl_spec dst with ⟨modrm, hbytes, hmod, hreg, hrm8, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact shr_r8_cl_triple_of_bytes p modrm hmod hreg hrm8
  · rw [hbytes, ← hdst]
    exact shr_r8_cl_rex_triple_of_bytes p rex modrm hrex hmod hreg

def shrR8ClNoRexEffect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (s : RamState) :
    Effect :=
  shrR8NoRexEffect p len dst (shiftCount 8 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem shrR8ClNoRexEffect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 3) (s : RamState) :
    (shrR8ClNoRexEffect p len dst s).components = [.reg (byteRegGpr dst), .flags, .rip] :=
  rfl

theorem shrR8ClNoRexEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (s : RamState) (code : CodeMap) : (shrR8ClNoRexEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem shr_r8_cl_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xD2, modrm])
      (shrR8ClNoRexEffect p 2 (modrmRm modrm)) := by
  rintro s h hcode rfl
  have hs := shr_r8_cl_norex_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp))
  have hr := shr_r8_cl_norex_ready h modrm
  simp only [writeOutputs_byteReg] at hs hr
  refine ⟨_, hs, hr,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, shrSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    apply shrFlags_allows

theorem shr_r8_cl_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    Triple (fun s => s.RIP = p) (codeRange p [0xD2, modrm])
      (Effect.post (shrR8ClNoRexEffect p 2 (modrmRm modrm))) :=
  Triple.of_effect (fun s _ => shrR8ClNoRexEffect_avoids p _ _ s _)
    (shr_r8_cl_norex_effect_step p modrm hmod hreg)

theorem shr_r8_cl_norex_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeShrR8ClNoRex dst))
      (Effect.post (shrR8ClNoRexEffect p 2 dst)) := by
  have h := shr_r8_cl_norex_triple_of_bytes p (modrmRegs 5 dst)
    (modrmMod_modrmRegs _ _) (modrmReg_modrmRegs _ _)
  rwa [modrmRm_modrmRegs] at h

attribute [x86_compose] shrR8ClEffect shrR8ClNoRexEffect

@[x86_local] theorem shrR8ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (shrR8ClEffect p len dst) :=
  Effect.Local.of_param (e := fun c => shrR8Effect p len dst c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => shrR8Effect_local

@[x86_local] theorem shrR8ClNoRexEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3} :
    Effect.Local (shrR8ClNoRexEffect p len dst) :=
  Effect.Local.of_param (e := fun c => shrR8NoRexEffect p len dst c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => shrR8NoRexEffect_local

end X86Proofs
