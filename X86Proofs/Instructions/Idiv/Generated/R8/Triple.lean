import X86Proofs.Instructions.Idiv.Generated.R8.Step
import X86Proofs.Instructions.Idiv.Generated.R8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def idivR8Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (s : RamState) : Effect :=
  let t := (Operand.reg 0 : Operand 16).read s
  let r := idivResult t ((Operand.reg src : Operand 8).read s)
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 16 (r.2 ++ r.1) ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some divFlags }

@[simp] theorem idivR8Effect_components (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (s : RamState) : (idivR8Effect p len src s).components = [.reg 0, .flags, .rip] := rfl

theorem idivR8Effect_avoids (p : BitVec 64) (len : Nat) (src : BitVec 5) (s : RamState)
    (code : CodeMap) : (idivR8Effect p len src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem idiv_r8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p ∧
      IdivDefined ((Operand.reg 0 : Operand 16).read s) ((Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 8).read s))
      (codeRange p [0xF6, modrm])
      (idivR8Effect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode ⟨rfl, hdef⟩
  refine ⟨_, idiv_r8_step s h modrm hmod hreg hrm8 hcode.bytesAt
    (hcode.low (by simp) (by simp)) hdef, idiv_r8_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 6 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_writeOutputs_self_merge]
    simp only [idivSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact idiv_divFlags_allows _ _ _

theorem idiv_r8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p ∧
      IdivDefined ((Operand.reg 0 : Operand 16).read s) ((Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 8).read s))
      (codeRange p [0xF6, modrm])
      (Effect.post (idivR8Effect p 2 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => idivR8Effect_avoids p _ _ s _)
    (idiv_r8_effect_step p modrm hmod hreg hrm8)

theorem idiv_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p ∧
      IdivDefined ((Operand.reg 0 : Operand 16).read s) ((Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 8).read s))
      (codeRange p [rex, 0xF6, modrm])
      (idivR8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode ⟨rfl, hdef⟩
  refine ⟨_, idiv_r8_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)) hdef, idiv_r8_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 6 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_writeOutputs_self_merge]
    simp only [idivSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact idiv_divFlags_allows _ _ _

theorem idiv_r8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    Triple (fun s => s.RIP = p ∧
      IdivDefined ((Operand.reg 0 : Operand 16).read s) ((Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 8).read s))
      (codeRange p [rex, 0xF6, modrm])
      (Effect.post (idivR8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => idivR8Effect_avoids p _ _ s _)
    (idiv_r8_rex_effect_step p rex modrm hrex hmod hreg)

theorem idiv_r8_triple [Bindings] (p : BitVec 64) (src : BitVec 4) :
    Triple (fun s => s.RIP = p ∧
      IdivDefined ((Operand.reg 0 : Operand 16).read s) ((Operand.reg (src.setWidth 5) : Operand 8).read s))
      (codeRange p (encodeIdivR8 src))
      (Effect.post (idivR8Effect p (encodeIdivR8 src).length (src.setWidth 5))) := by
  rcases encodeIdivR8_spec src with ⟨modrm, hbytes, hmod, hreg, hrm8, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hsrc⟩
  · rw [hbytes, ← hsrc]
    exact idiv_r8_triple_of_bytes p modrm hmod hreg hrm8
  · rw [hbytes, ← hsrc]
    exact idiv_r8_rex_triple_of_bytes p rex modrm hrex hmod hreg

def idivR8NoRexEffect (p : BitVec 64) (len : Nat) (src : BitVec 3) (s : RamState) : Effect :=
  let t := (Operand.reg 0 : Operand 16).read s
  let r := idivResult t ((Operand.byteReg src).read s)
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 16 (r.2 ++ r.1) ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some divFlags }

@[simp] theorem idivR8NoRexEffect_components (p : BitVec 64) (len : Nat) (src : BitVec 3)
    (s : RamState) : (idivR8NoRexEffect p len src s).components = [.reg 0, .flags, .rip] := rfl

theorem idivR8NoRexEffect_avoids (p : BitVec 64) (len : Nat) (src : BitVec 3) (s : RamState)
    (code : CodeMap) : (idivR8NoRexEffect p len src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem idiv_r8_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p ∧
      IdivDefined ((Operand.reg 0 : Operand 16).read s) ((Operand.byteReg (modrmRm modrm)).read s))
      (codeRange p [0xF6, modrm])
      (idivR8NoRexEffect p 2 (modrmRm modrm)) := by
  rintro s h hcode ⟨rfl, hdef⟩
  refine ⟨_, idiv_r8_norex_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)) hdef, idiv_r8_norex_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 6 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_writeOutputs_self_merge]
    simp only [idivSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact idiv_divFlags_allows _ _ _

theorem idiv_r8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    Triple (fun s => s.RIP = p ∧
      IdivDefined ((Operand.reg 0 : Operand 16).read s) ((Operand.byteReg (modrmRm modrm)).read s))
      (codeRange p [0xF6, modrm])
      (Effect.post (idivR8NoRexEffect p 2 (modrmRm modrm))) :=
  Triple.of_effect (fun s _ => idivR8NoRexEffect_avoids p _ _ s _)
    (idiv_r8_norex_effect_step p modrm hmod hreg)

theorem idiv_r8_norex_triple [Bindings] (p : BitVec 64) (src : BitVec 3) :
    Triple (fun s => s.RIP = p ∧
      IdivDefined ((Operand.reg 0 : Operand 16).read s) ((Operand.byteReg src).read s))
      (codeRange p (encodeIdivR8NoRex src))
      (Effect.post (idivR8NoRexEffect p 2 src)) := by
  have h := idiv_r8_norex_triple_of_bytes p (modrmRegs 7 src) (modrmMod_modrmRegs _ _)
    (modrmReg_modrmRegs _ _)
  rwa [modrmRm_modrmRegs] at h

attribute [x86_compose] idivR8Effect idivR8NoRexEffect

@[x86_local] theorem idivR8Effect_local {p : BitVec 64} {len : Nat} {src : BitVec 5} :
    Effect.Local (idivR8Effect p len src) := by
  effect_local [idivR8Effect, divFlags]

@[x86_local] theorem idivR8NoRexEffect_local {p : BitVec 64} {len : Nat} {src : BitVec 3} :
    Effect.Local (idivR8NoRexEffect p len src) := by
  effect_local [idivR8NoRexEffect, divFlags]

end X86Proofs
