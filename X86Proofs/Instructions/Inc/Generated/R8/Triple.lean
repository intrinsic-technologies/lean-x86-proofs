import X86Proofs.Instructions.Inc.Generated.R8.Step
import X86Proofs.Instructions.Inc.Generated.R8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def incR8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (a + 1) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (incSpec (StatusFlags.ofRFLAGS s.RFLAGS) a).2) }

@[simp] theorem incR8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (incR8Effect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem incR8Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (incR8Effect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem inc_r8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xFE, modrm])
      (incR8Effect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, inc_r8_step s h modrm hmod hreg hrm8 hcode.bytesAt
    (hcode.low (by simp) (by simp)), inc_r8_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, incSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem inc_r8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p) (codeRange p [0xFE, modrm])
      (Effect.post (incR8Effect p 2 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => incR8Effect_avoids p _ _ s _)
    (inc_r8_effect_step p modrm hmod hreg hrm8)

theorem inc_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xFE, modrm])
      (incR8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, inc_r8_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), inc_r8_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, incSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem inc_r8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xFE, modrm])
      (Effect.post (incR8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => incR8Effect_avoids p _ _ s _)
    (inc_r8_rex_effect_step p rex modrm hrex hmod hreg)

theorem inc_r8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeIncR8 dst))
      (Effect.post (incR8Effect p (encodeIncR8 dst).length (dst.setWidth 5))) := by
  rcases encodeIncR8_spec dst with ⟨modrm, hbytes, hmod, hreg, hrm8, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact inc_r8_triple_of_bytes p modrm hmod hreg hrm8
  · rw [hbytes, ← hdst]
    exact inc_r8_rex_triple_of_bytes p rex modrm hrex hmod hreg

def incR8NoRexEffect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (s : RamState) : Effect :=
  let a := (Operand.byteReg dst).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (byteRegGpr dst) : Operand 64),
      mergeByteReg dst (a + 1) ((Operand.reg (byteRegGpr dst) : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (incSpec (StatusFlags.ofRFLAGS s.RFLAGS) a).2) }

@[simp] theorem incR8NoRexEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (s : RamState) :
    (incR8NoRexEffect p len dst s).components = [.reg (byteRegGpr dst), .flags, .rip] :=
  rfl

theorem incR8NoRexEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 3) (s : RamState)
    (code : CodeMap) : (incR8NoRexEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem inc_r8_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xFE, modrm])
      (incR8NoRexEffect p 2 (modrmRm modrm)) := by
  rintro s h hcode rfl
  have hs := inc_r8_norex_step s h modrm hmod hreg hcode.bytesAt (hcode.low (by simp) (by simp))
  have hr := inc_r8_norex_ready h modrm
  simp only [writeOutputs_byteReg] at hs hr
  refine ⟨_, hs, hr,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, incSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem inc_r8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [0xFE, modrm])
      (Effect.post (incR8NoRexEffect p 2 (modrmRm modrm))) :=
  Triple.of_effect (fun s _ => incR8NoRexEffect_avoids p _ _ s _)
    (inc_r8_norex_effect_step p modrm hmod hreg)

theorem inc_r8_norex_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeIncR8NoRex dst))
      (Effect.post (incR8NoRexEffect p 2 dst)) := by
  have h := inc_r8_norex_triple_of_bytes p (modrmRegs 0 dst) (modrmMod_modrmRegs _ _)
    (modrmReg_modrmRegs _ _)
  rwa [modrmRm_modrmRegs] at h

attribute [x86_compose] incR8Effect incR8NoRexEffect

@[x86_local] theorem incR8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (incR8Effect p len dst) := by
  effect_local [incR8Effect, incSpec]

@[x86_local] theorem incR8NoRexEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3} :
    Effect.Local (incR8NoRexEffect p len dst) := by
  effect_local [incR8NoRexEffect, incSpec]

end X86Proofs
