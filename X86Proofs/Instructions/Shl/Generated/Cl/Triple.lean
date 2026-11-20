import X86Proofs.Instructions.Shl.Generated.Cl.Step
import X86Proofs.Instructions.Shl.Generated.Cl.Encode
import X86Proofs.Instructions.Shl.Generated.R.Triple
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def shlR64ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  shlR64Effect p len dst (shiftCount 64 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem shlR64ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (shlR64ClEffect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem shlR64ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (shlR64ClEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def shlR32ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  shlR32Effect p len dst (shiftCount 32 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem shlR32ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (shlR32ClEffect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem shlR32ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (shlR32ClEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def shlR16ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  shlR16Effect p len dst (shiftCount 16 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem shlR16ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (shlR16ClEffect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem shlR16ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (shlR16ClEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem shl_r64_cl_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (shlR64ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, shl_r64_cl_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), shl_r64_cl_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem shl_r64_cl_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (Effect.post (shlR64ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => shlR64ClEffect_avoids p _ _ s _)
    (shl_r64_cl_effect_step p rex modrm hrex hmod hreg)

theorem shl_r32_cl_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xD3, modrm])
      (shlR32ClEffect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, shl_r32_cl_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), shl_r32_cl_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem shl_r32_cl_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    Triple (fun s => s.RIP = p) (codeRange p [0xD3, modrm])
      (Effect.post (shlR32ClEffect p 2 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => shlR32ClEffect_avoids p _ _ s _)
    (shl_r32_cl_effect_step p modrm hmod hreg)

theorem shl_r32_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (shlR32ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, shl_r32_cl_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), shl_r32_cl_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem shl_r32_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (Effect.post (shlR32ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => shlR32ClEffect_avoids p _ _ s _)
    (shl_r32_cl_rex_effect_step p rex modrm hrex hmod hreg)

theorem shl_r16_cl_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0xD3, modrm])
      (shlR16ClEffect p 3 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, shl_r16_cl_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), shl_r16_cl_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem shl_r16_cl_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, 0xD3, modrm])
      (Effect.post (shlR16ClEffect p 3 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => shlR16ClEffect_avoids p _ _ s _)
    (shl_r16_cl_effect_step p modrm hmod hreg)

theorem shl_r16_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xD3, modrm])
      (shlR16ClEffect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, shl_r16_cl_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), shl_r16_cl_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem shl_r16_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xD3, modrm])
      (Effect.post (shlR16ClEffect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => shlR16ClEffect_avoids p _ _ s _)
    (shl_r16_cl_rex_effect_step p rex modrm hrex hmod hreg)

theorem shl_r64_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeShlR64Cl dst))
      (Effect.post (shlR64ClEffect p
        3 (dst.setWidth 5))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeShlR64Cl_spec dst
  rw [hbytes, ← hdst]
  exact shl_r64_cl_triple_of_bytes p rex modrm hrex hmod hreg

theorem shl_r32_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeShlR32Cl dst))
      (Effect.post (shlR32ClEffect p
        (encodeShlR32Cl dst).length (dst.setWidth 5))) := by
  rcases encodeShlR32Cl_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact shl_r32_cl_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact shl_r32_cl_rex_triple_of_bytes p rex modrm hrex hmod hreg

theorem shl_r16_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeShlR16Cl dst))
      (Effect.post (shlR16ClEffect p
        (encodeShlR16Cl dst).length (dst.setWidth 5))) := by
  rcases encodeShlR16Cl_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact shl_r16_cl_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact shl_r16_cl_rex_triple_of_bytes p rex modrm hrex hmod hreg

attribute [x86_compose] shlR64ClEffect shlR32ClEffect shlR16ClEffect

@[x86_local] theorem shlR64ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (shlR64ClEffect p len dst) :=
  Effect.Local.of_param (e := fun c => shlR64Effect p len dst c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => shlR64Effect_local

@[x86_local] theorem shlR32ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (shlR32ClEffect p len dst) :=
  Effect.Local.of_param (e := fun c => shlR32Effect p len dst c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => shlR32Effect_local

@[x86_local] theorem shlR16ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (shlR16ClEffect p len dst) :=
  Effect.Local.of_param (e := fun c => shlR16Effect p len dst c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => shlR16Effect_local

end X86Proofs
