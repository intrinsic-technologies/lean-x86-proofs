import X86Proofs.Instructions.Shr.Generated.Cl.Step
import X86Proofs.Instructions.Shr.Generated.Cl.Encode
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def shrR64ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  shrR64Effect p len dst (shiftCount 64 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem shrR64ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (shrR64ClEffect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem shrR64ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (shrR64ClEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def shrR32ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  shrR32Effect p len dst (shiftCount 32 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem shrR32ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (shrR32ClEffect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem shrR32ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (shrR32ClEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def shrR16ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  shrR16Effect p len dst (shiftCount 16 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem shrR16ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (shrR16ClEffect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem shrR16ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (shrR16ClEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem shr_r64_cl_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (shrR64ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, shr_r64_cl_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), shr_r64_cl_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, shrSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shrFlags_allows

theorem shr_r64_cl_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (Effect.post (shrR64ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => shrR64ClEffect_avoids p _ _ s _)
    (shr_r64_cl_effect_step p rex modrm hrex hmod hreg)

theorem shr_r32_cl_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xD3, modrm])
      (shrR32ClEffect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, shr_r32_cl_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), shr_r32_cl_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, shrSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shrFlags_allows

theorem shr_r32_cl_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    Triple (fun s => s.RIP = p) (codeRange p [0xD3, modrm])
      (Effect.post (shrR32ClEffect p 2 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => shrR32ClEffect_avoids p _ _ s _)
    (shr_r32_cl_effect_step p modrm hmod hreg)

theorem shr_r32_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (shrR32ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, shr_r32_cl_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), shr_r32_cl_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, shrSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shrFlags_allows

theorem shr_r32_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (Effect.post (shrR32ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => shrR32ClEffect_avoids p _ _ s _)
    (shr_r32_cl_rex_effect_step p rex modrm hrex hmod hreg)

theorem shr_r16_cl_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0xD3, modrm])
      (shrR16ClEffect p 3 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, shr_r16_cl_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), shr_r16_cl_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, shrSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shrFlags_allows

theorem shr_r16_cl_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, 0xD3, modrm])
      (Effect.post (shrR16ClEffect p 3 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => shrR16ClEffect_avoids p _ _ s _)
    (shr_r16_cl_effect_step p modrm hmod hreg)

theorem shr_r16_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xD3, modrm])
      (shrR16ClEffect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, shr_r16_cl_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), shr_r16_cl_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, shrSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shrFlags_allows

theorem shr_r16_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xD3, modrm])
      (Effect.post (shrR16ClEffect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => shrR16ClEffect_avoids p _ _ s _)
    (shr_r16_cl_rex_effect_step p rex modrm hrex hmod hreg)

theorem shr_r64_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeShrR64Cl dst))
      (Effect.post (shrR64ClEffect p
        3 (dst.setWidth 5))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeShrR64Cl_spec dst
  rw [hbytes, ← hdst]
  exact shr_r64_cl_triple_of_bytes p rex modrm hrex hmod hreg

theorem shr_r32_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeShrR32Cl dst))
      (Effect.post (shrR32ClEffect p
        (encodeShrR32Cl dst).length (dst.setWidth 5))) := by
  rcases encodeShrR32Cl_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact shr_r32_cl_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact shr_r32_cl_rex_triple_of_bytes p rex modrm hrex hmod hreg

theorem shr_r16_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeShrR16Cl dst))
      (Effect.post (shrR16ClEffect p
        (encodeShrR16Cl dst).length (dst.setWidth 5))) := by
  rcases encodeShrR16Cl_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact shr_r16_cl_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact shr_r16_cl_rex_triple_of_bytes p rex modrm hrex hmod hreg

attribute [x86_compose] shrR64ClEffect shrR32ClEffect shrR16ClEffect

@[x86_local] theorem shrR64ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (shrR64ClEffect p len dst) :=
  Effect.Local.of_param (e := fun c => shrR64Effect p len dst c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => shrR64Effect_local

@[x86_local] theorem shrR32ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (shrR32ClEffect p len dst) :=
  Effect.Local.of_param (e := fun c => shrR32Effect p len dst c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => shrR32Effect_local

@[x86_local] theorem shrR16ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (shrR16ClEffect p len dst) :=
  Effect.Local.of_param (e := fun c => shrR16Effect p len dst c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => shrR16Effect_local

end X86Proofs
