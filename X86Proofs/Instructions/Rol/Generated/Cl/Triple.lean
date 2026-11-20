import X86Proofs.Instructions.Rol.Generated.Cl.Step
import X86Proofs.Instructions.Rol.Generated.Cl.Encode
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def rolR64ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  rolR64Effect p len dst (shiftCount 64 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem rolR64ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (rolR64ClEffect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem rolR64ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (rolR64ClEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def rolR32ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  rolR32Effect p len dst (shiftCount 32 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem rolR32ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (rolR32ClEffect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem rolR32ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (rolR32ClEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def rolR16ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  rolR16Effect p len dst (shiftCount 16 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem rolR16ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (rolR16ClEffect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem rolR16ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (rolR16ClEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem rol_r64_cl_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (rolR64ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, rol_r64_cl_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rol_r64_cl_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, rolSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rolFlags_allows

theorem rol_r64_cl_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (Effect.post (rolR64ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => rolR64ClEffect_avoids p _ _ s _)
    (rol_r64_cl_effect_step p rex modrm hrex hmod hreg)

theorem rol_r32_cl_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xD3, modrm])
      (rolR32ClEffect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, rol_r32_cl_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rol_r32_cl_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, rolSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rolFlags_allows

theorem rol_r32_cl_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [0xD3, modrm])
      (Effect.post (rolR32ClEffect p 2 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => rolR32ClEffect_avoids p _ _ s _)
    (rol_r32_cl_effect_step p modrm hmod hreg)

theorem rol_r32_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (rolR32ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, rol_r32_cl_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rol_r32_cl_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, rolSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rolFlags_allows

theorem rol_r32_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (Effect.post (rolR32ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => rolR32ClEffect_avoids p _ _ s _)
    (rol_r32_cl_rex_effect_step p rex modrm hrex hmod hreg)

theorem rol_r16_cl_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0xD3, modrm])
      (rolR16ClEffect p 3 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, rol_r16_cl_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rol_r16_cl_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rolSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rolFlags_allows

theorem rol_r16_cl_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, 0xD3, modrm])
      (Effect.post (rolR16ClEffect p 3 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => rolR16ClEffect_avoids p _ _ s _)
    (rol_r16_cl_effect_step p modrm hmod hreg)

theorem rol_r16_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xD3, modrm])
      (rolR16ClEffect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, rol_r16_cl_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rol_r16_cl_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rolSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rolFlags_allows

theorem rol_r16_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xD3, modrm])
      (Effect.post (rolR16ClEffect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => rolR16ClEffect_avoids p _ _ s _)
    (rol_r16_cl_rex_effect_step p rex modrm hrex hmod hreg)

theorem rol_r64_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRolR64Cl dst))
      (Effect.post (rolR64ClEffect p
        3 (dst.setWidth 5))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeRolR64Cl_spec dst
  rw [hbytes, ← hdst]
  exact rol_r64_cl_triple_of_bytes p rex modrm hrex hmod hreg

theorem rol_r32_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRolR32Cl dst))
      (Effect.post (rolR32ClEffect p
        (encodeRolR32Cl dst).length (dst.setWidth 5))) := by
  rcases encodeRolR32Cl_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact rol_r32_cl_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact rol_r32_cl_rex_triple_of_bytes p rex modrm hrex hmod hreg

theorem rol_r16_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRolR16Cl dst))
      (Effect.post (rolR16ClEffect p
        (encodeRolR16Cl dst).length (dst.setWidth 5))) := by
  rcases encodeRolR16Cl_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact rol_r16_cl_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact rol_r16_cl_rex_triple_of_bytes p rex modrm hrex hmod hreg

attribute [x86_compose] rolR64ClEffect rolR32ClEffect rolR16ClEffect

@[x86_local] theorem rolR64ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (rolR64ClEffect p len dst) :=
  Effect.Local.of_param (e := fun c => rolR64Effect p len dst c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => rolR64Effect_local

@[x86_local] theorem rolR32ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (rolR32ClEffect p len dst) :=
  Effect.Local.of_param (e := fun c => rolR32Effect p len dst c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => rolR32Effect_local

@[x86_local] theorem rolR16ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (rolR16ClEffect p len dst) :=
  Effect.Local.of_param (e := fun c => rolR16Effect p len dst c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => rolR16Effect_local

end X86Proofs
