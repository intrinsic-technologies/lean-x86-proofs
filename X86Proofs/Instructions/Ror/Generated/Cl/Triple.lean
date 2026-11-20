import X86Proofs.Instructions.Ror.Generated.Cl.Step
import X86Proofs.Instructions.Ror.Generated.Cl.Encode
import X86Proofs.Instructions.Ror.Generated.R.Triple
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def rorR64ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  rorR64Effect p len dst (shiftCount 64 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem rorR64ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (rorR64ClEffect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem rorR64ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (rorR64ClEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def rorR32ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  rorR32Effect p len dst (shiftCount 32 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem rorR32ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (rorR32ClEffect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem rorR32ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (rorR32ClEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def rorR16ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  rorR16Effect p len dst (shiftCount 16 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem rorR16ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (rorR16ClEffect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem rorR16ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (rorR16ClEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem ror_r64_cl_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (rorR64ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, ror_r64_cl_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), ror_r64_cl_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, rorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rorFlags_allows

theorem ror_r64_cl_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (Effect.post (rorR64ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => rorR64ClEffect_avoids p _ _ s _)
    (ror_r64_cl_effect_step p rex modrm hrex hmod hreg)

theorem ror_r32_cl_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xD3, modrm])
      (rorR32ClEffect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, ror_r32_cl_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), ror_r32_cl_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, rorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rorFlags_allows

theorem ror_r32_cl_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [0xD3, modrm])
      (Effect.post (rorR32ClEffect p 2 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => rorR32ClEffect_avoids p _ _ s _)
    (ror_r32_cl_effect_step p modrm hmod hreg)

theorem ror_r32_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (rorR32ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, ror_r32_cl_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), ror_r32_cl_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, rorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rorFlags_allows

theorem ror_r32_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (Effect.post (rorR32ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => rorR32ClEffect_avoids p _ _ s _)
    (ror_r32_cl_rex_effect_step p rex modrm hrex hmod hreg)

theorem ror_r16_cl_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0xD3, modrm])
      (rorR16ClEffect p 3 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, ror_r16_cl_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), ror_r16_cl_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rorFlags_allows

theorem ror_r16_cl_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, 0xD3, modrm])
      (Effect.post (rorR16ClEffect p 3 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => rorR16ClEffect_avoids p _ _ s _)
    (ror_r16_cl_effect_step p modrm hmod hreg)

theorem ror_r16_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xD3, modrm])
      (rorR16ClEffect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, ror_r16_cl_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), ror_r16_cl_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rorFlags_allows

theorem ror_r16_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xD3, modrm])
      (Effect.post (rorR16ClEffect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => rorR16ClEffect_avoids p _ _ s _)
    (ror_r16_cl_rex_effect_step p rex modrm hrex hmod hreg)

theorem ror_r64_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRorR64Cl dst))
      (Effect.post (rorR64ClEffect p
        3 (dst.setWidth 5))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeRorR64Cl_spec dst
  rw [hbytes, ← hdst]
  exact ror_r64_cl_triple_of_bytes p rex modrm hrex hmod hreg

theorem ror_r32_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRorR32Cl dst))
      (Effect.post (rorR32ClEffect p
        (encodeRorR32Cl dst).length (dst.setWidth 5))) := by
  rcases encodeRorR32Cl_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact ror_r32_cl_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact ror_r32_cl_rex_triple_of_bytes p rex modrm hrex hmod hreg

theorem ror_r16_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRorR16Cl dst))
      (Effect.post (rorR16ClEffect p
        (encodeRorR16Cl dst).length (dst.setWidth 5))) := by
  rcases encodeRorR16Cl_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact ror_r16_cl_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact ror_r16_cl_rex_triple_of_bytes p rex modrm hrex hmod hreg

attribute [x86_compose] rorR64ClEffect rorR32ClEffect rorR16ClEffect

@[x86_local] theorem rorR64ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (rorR64ClEffect p len dst) :=
  Effect.Local.of_param (e := fun c => rorR64Effect p len dst c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => rorR64Effect_local

@[x86_local] theorem rorR32ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (rorR32ClEffect p len dst) :=
  Effect.Local.of_param (e := fun c => rorR32Effect p len dst c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => rorR32Effect_local

@[x86_local] theorem rorR16ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (rorR16ClEffect p len dst) :=
  Effect.Local.of_param (e := fun c => rorR16Effect p len dst c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => rorR16Effect_local

end X86Proofs
