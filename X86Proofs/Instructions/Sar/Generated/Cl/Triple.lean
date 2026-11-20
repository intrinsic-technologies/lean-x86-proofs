import X86Proofs.Instructions.Sar.Generated.Cl.Step
import X86Proofs.Instructions.Sar.Generated.Cl.Encode
import X86Proofs.Instructions.Sar.Generated.R.Triple
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def sarR64ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  sarR64Effect p len dst (shiftCount 64 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem sarR64ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (sarR64ClEffect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem sarR64ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (sarR64ClEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def sarR32ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  sarR32Effect p len dst (shiftCount 32 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem sarR32ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (sarR32ClEffect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem sarR32ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (sarR32ClEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def sarR16ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  sarR16Effect p len dst (shiftCount 16 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem sarR16ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (sarR16ClEffect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem sarR16ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (sarR16ClEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem sar_r64_cl_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (sarR64ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, sar_r64_cl_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sar_r64_cl_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, sarSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply sarFlags_allows

theorem sar_r64_cl_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (Effect.post (sarR64ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => sarR64ClEffect_avoids p _ _ s _)
    (sar_r64_cl_effect_step p rex modrm hrex hmod hreg)

theorem sar_r32_cl_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xD3, modrm])
      (sarR32ClEffect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, sar_r32_cl_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sar_r32_cl_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, sarSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply sarFlags_allows

theorem sar_r32_cl_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    Triple (fun s => s.RIP = p) (codeRange p [0xD3, modrm])
      (Effect.post (sarR32ClEffect p 2 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => sarR32ClEffect_avoids p _ _ s _)
    (sar_r32_cl_effect_step p modrm hmod hreg)

theorem sar_r32_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (sarR32ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, sar_r32_cl_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sar_r32_cl_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, sarSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply sarFlags_allows

theorem sar_r32_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (Effect.post (sarR32ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => sarR32ClEffect_avoids p _ _ s _)
    (sar_r32_cl_rex_effect_step p rex modrm hrex hmod hreg)

theorem sar_r16_cl_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0xD3, modrm])
      (sarR16ClEffect p 3 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, sar_r16_cl_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sar_r16_cl_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, sarSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply sarFlags_allows

theorem sar_r16_cl_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, 0xD3, modrm])
      (Effect.post (sarR16ClEffect p 3 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => sarR16ClEffect_avoids p _ _ s _)
    (sar_r16_cl_effect_step p modrm hmod hreg)

theorem sar_r16_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xD3, modrm])
      (sarR16ClEffect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, sar_r16_cl_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sar_r16_cl_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, sarSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply sarFlags_allows

theorem sar_r16_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xD3, modrm])
      (Effect.post (sarR16ClEffect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => sarR16ClEffect_avoids p _ _ s _)
    (sar_r16_cl_rex_effect_step p rex modrm hrex hmod hreg)

theorem sar_r64_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSarR64Cl dst))
      (Effect.post (sarR64ClEffect p
        3 (dst.setWidth 5))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeSarR64Cl_spec dst
  rw [hbytes, ← hdst]
  exact sar_r64_cl_triple_of_bytes p rex modrm hrex hmod hreg

theorem sar_r32_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSarR32Cl dst))
      (Effect.post (sarR32ClEffect p
        (encodeSarR32Cl dst).length (dst.setWidth 5))) := by
  rcases encodeSarR32Cl_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact sar_r32_cl_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact sar_r32_cl_rex_triple_of_bytes p rex modrm hrex hmod hreg

theorem sar_r16_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSarR16Cl dst))
      (Effect.post (sarR16ClEffect p
        (encodeSarR16Cl dst).length (dst.setWidth 5))) := by
  rcases encodeSarR16Cl_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact sar_r16_cl_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact sar_r16_cl_rex_triple_of_bytes p rex modrm hrex hmod hreg

attribute [x86_compose] sarR64ClEffect sarR32ClEffect sarR16ClEffect

@[x86_local] theorem sarR64ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (sarR64ClEffect p len dst) :=
  Effect.Local.of_param (e := fun c => sarR64Effect p len dst c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => sarR64Effect_local

@[x86_local] theorem sarR32ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (sarR32ClEffect p len dst) :=
  Effect.Local.of_param (e := fun c => sarR32Effect p len dst c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => sarR32Effect_local

@[x86_local] theorem sarR16ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (sarR16ClEffect p len dst) :=
  Effect.Local.of_param (e := fun c => sarR16Effect p len dst c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => sarR16Effect_local

end X86Proofs
