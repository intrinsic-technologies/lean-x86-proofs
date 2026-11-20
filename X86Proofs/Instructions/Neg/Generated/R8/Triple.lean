import X86Proofs.Instructions.Neg.Generated.R8.Step
import X86Proofs.Instructions.Neg.Generated.R8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def negR8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (-a) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (negSpec a).2) }

@[simp] theorem negR8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (negR8Effect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem negR8Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (negR8Effect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem neg_r8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xF6, modrm])
      (negR8Effect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, neg_r8_step s h modrm hmod hreg hrm8 hcode.bytesAt
    (hcode.low (by simp) (by simp)), neg_r8_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, negSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem neg_r8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p) (codeRange p [0xF6, modrm])
      (Effect.post (negR8Effect p 2 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => negR8Effect_avoids p _ _ s _)
    (neg_r8_effect_step p modrm hmod hreg hrm8)

theorem neg_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xF6, modrm])
      (negR8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, neg_r8_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), neg_r8_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, negSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem neg_r8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xF6, modrm])
      (Effect.post (negR8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => negR8Effect_avoids p _ _ s _)
    (neg_r8_rex_effect_step p rex modrm hrex hmod hreg)

theorem neg_r8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeNegR8 dst))
      (Effect.post (negR8Effect p (encodeNegR8 dst).length (dst.setWidth 5))) := by
  rcases encodeNegR8_spec dst with ⟨modrm, hbytes, hmod, hreg, hrm8, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact neg_r8_triple_of_bytes p modrm hmod hreg hrm8
  · rw [hbytes, ← hdst]
    exact neg_r8_rex_triple_of_bytes p rex modrm hrex hmod hreg

def negR8NoRexEffect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (s : RamState) : Effect :=
  let a := (Operand.byteReg dst).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (byteRegGpr dst) : Operand 64),
      mergeByteReg dst (-a) ((Operand.reg (byteRegGpr dst) : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (negSpec a).2) }

@[simp] theorem negR8NoRexEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (s : RamState) :
    (negR8NoRexEffect p len dst s).components = [.reg (byteRegGpr dst), .flags, .rip] :=
  rfl

theorem negR8NoRexEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 3) (s : RamState)
    (code : CodeMap) : (negR8NoRexEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem neg_r8_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xF6, modrm])
      (negR8NoRexEffect p 2 (modrmRm modrm)) := by
  rintro s h hcode rfl
  have hs := neg_r8_norex_step s h modrm hmod hreg hcode.bytesAt (hcode.low (by simp) (by simp))
  have hr := neg_r8_norex_ready h modrm
  simp only [writeOutputs_byteReg] at hs hr
  refine ⟨_, hs, hr,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, negSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem neg_r8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [0xF6, modrm])
      (Effect.post (negR8NoRexEffect p 2 (modrmRm modrm))) :=
  Triple.of_effect (fun s _ => negR8NoRexEffect_avoids p _ _ s _)
    (neg_r8_norex_effect_step p modrm hmod hreg)

theorem neg_r8_norex_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeNegR8NoRex dst))
      (Effect.post (negR8NoRexEffect p 2 dst)) := by
  have h := neg_r8_norex_triple_of_bytes p (modrmRegs 3 dst) (modrmMod_modrmRegs _ _)
    (modrmReg_modrmRegs _ _)
  rwa [modrmRm_modrmRegs] at h

attribute [x86_compose] negR8Effect negR8NoRexEffect

@[x86_local] theorem negR8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (negR8Effect p len dst) := by
  effect_local [negR8Effect]

@[x86_local] theorem negR8NoRexEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3} :
    Effect.Local (negR8NoRexEffect p len dst) := by
  effect_local [negR8NoRexEffect]

end X86Proofs
