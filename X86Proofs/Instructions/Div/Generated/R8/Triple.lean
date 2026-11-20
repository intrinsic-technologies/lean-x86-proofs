import X86Proofs.Instructions.Div.Generated.R8.Step
import X86Proofs.Instructions.Div.Generated.R8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def divR8Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (s : RamState) : Effect :=
  let t := (Operand.reg 0 : Operand 16).read s
  let r := divResult t ((Operand.reg src : Operand 8).read s)
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 16 (r.2 ++ r.1) ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some divFlags }

@[simp] theorem divR8Effect_components (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (s : RamState) : (divR8Effect p len src s).components = [.reg 0, .flags, .rip] := rfl

theorem divR8Effect_avoids (p : BitVec 64) (len : Nat) (src : BitVec 5) (s : RamState)
    (code : CodeMap) : (divR8Effect p len src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem div_r8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p ∧
      DivDefined ((Operand.reg 0 : Operand 16).read s) ((Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 8).read s))
      (codeRange p [0xF6, modrm])
      (divR8Effect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode ⟨rfl, hdef⟩
  refine ⟨_, div_r8_step s h modrm hmod hreg hrm8 hcode.bytesAt
    (hcode.low (by simp) (by simp)) hdef, div_r8_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 6 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_writeOutputs_self_merge]
    simp only [divSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact divFlags_allows _ _ _

theorem div_r8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p ∧
      DivDefined ((Operand.reg 0 : Operand 16).read s) ((Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 8).read s))
      (codeRange p [0xF6, modrm])
      (Effect.post (divR8Effect p 2 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => divR8Effect_avoids p _ _ s _)
    (div_r8_effect_step p modrm hmod hreg hrm8)

theorem div_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    StepEffect (fun s => s.RIP = p ∧
      DivDefined ((Operand.reg 0 : Operand 16).read s) ((Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 8).read s))
      (codeRange p [rex, 0xF6, modrm])
      (divR8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode ⟨rfl, hdef⟩
  refine ⟨_, div_r8_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)) hdef, div_r8_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 6 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_writeOutputs_self_merge]
    simp only [divSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact divFlags_allows _ _ _

theorem div_r8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    Triple (fun s => s.RIP = p ∧
      DivDefined ((Operand.reg 0 : Operand 16).read s) ((Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 8).read s))
      (codeRange p [rex, 0xF6, modrm])
      (Effect.post (divR8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => divR8Effect_avoids p _ _ s _)
    (div_r8_rex_effect_step p rex modrm hrex hmod hreg)

theorem div_r8_triple [Bindings] (p : BitVec 64) (src : BitVec 4) :
    Triple (fun s => s.RIP = p ∧
      DivDefined ((Operand.reg 0 : Operand 16).read s) ((Operand.reg (src.setWidth 5) : Operand 8).read s))
      (codeRange p (encodeDivR8 src))
      (Effect.post (divR8Effect p (encodeDivR8 src).length (src.setWidth 5))) := by
  rcases encodeDivR8_spec src with ⟨modrm, hbytes, hmod, hreg, hrm8, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hsrc⟩
  · rw [hbytes, ← hsrc]
    exact div_r8_triple_of_bytes p modrm hmod hreg hrm8
  · rw [hbytes, ← hsrc]
    exact div_r8_rex_triple_of_bytes p rex modrm hrex hmod hreg

def divR8NoRexEffect (p : BitVec 64) (len : Nat) (src : BitVec 3) (s : RamState) : Effect :=
  let t := (Operand.reg 0 : Operand 16).read s
  let r := divResult t ((Operand.byteReg src).read s)
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 16 (r.2 ++ r.1) ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some divFlags }

@[simp] theorem divR8NoRexEffect_components (p : BitVec 64) (len : Nat) (src : BitVec 3)
    (s : RamState) : (divR8NoRexEffect p len src s).components = [.reg 0, .flags, .rip] := rfl

theorem divR8NoRexEffect_avoids (p : BitVec 64) (len : Nat) (src : BitVec 3) (s : RamState)
    (code : CodeMap) : (divR8NoRexEffect p len src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem div_r8_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    StepEffect (fun s => s.RIP = p ∧
      DivDefined ((Operand.reg 0 : Operand 16).read s) ((Operand.byteReg (modrmRm modrm)).read s))
      (codeRange p [0xF6, modrm])
      (divR8NoRexEffect p 2 (modrmRm modrm)) := by
  rintro s h hcode ⟨rfl, hdef⟩
  refine ⟨_, div_r8_norex_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)) hdef, div_r8_norex_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 6 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_writeOutputs_self_merge]
    simp only [divSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact divFlags_allows _ _ _

theorem div_r8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    Triple (fun s => s.RIP = p ∧
      DivDefined ((Operand.reg 0 : Operand 16).read s) ((Operand.byteReg (modrmRm modrm)).read s))
      (codeRange p [0xF6, modrm])
      (Effect.post (divR8NoRexEffect p 2 (modrmRm modrm))) :=
  Triple.of_effect (fun s _ => divR8NoRexEffect_avoids p _ _ s _)
    (div_r8_norex_effect_step p modrm hmod hreg)

theorem div_r8_norex_triple [Bindings] (p : BitVec 64) (src : BitVec 3) :
    Triple (fun s => s.RIP = p ∧
      DivDefined ((Operand.reg 0 : Operand 16).read s) ((Operand.byteReg src).read s))
      (codeRange p (encodeDivR8NoRex src))
      (Effect.post (divR8NoRexEffect p 2 src)) := by
  have h := div_r8_norex_triple_of_bytes p (modrmRegs 6 src) (modrmMod_modrmRegs _ _)
    (modrmReg_modrmRegs _ _)
  rwa [modrmRm_modrmRegs] at h

attribute [x86_compose] divR8Effect divR8NoRexEffect

@[x86_local] theorem divR8Effect_local {p : BitVec 64} {len : Nat} {src : BitVec 5} :
    Effect.Local (divR8Effect p len src) := by
  effect_local [divR8Effect, divFlags]

@[x86_local] theorem divR8NoRexEffect_local {p : BitVec 64} {len : Nat} {src : BitVec 3} :
    Effect.Local (divR8NoRexEffect p len src) := by
  effect_local [divR8NoRexEffect, divFlags]

end X86Proofs
