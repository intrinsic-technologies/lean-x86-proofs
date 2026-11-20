import X86Proofs.Instructions.Dec.Generated.R8.Step
import X86Proofs.Instructions.Dec.Generated.R8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def decR8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (a - 1) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (decSpec (StatusFlags.ofRFLAGS s.RFLAGS) a).2) }

@[simp] theorem decR8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (decR8Effect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem decR8Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (decR8Effect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem dec_r8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xFE, modrm])
      (decR8Effect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, dec_r8_step s h modrm hmod hreg hrm8 hcode.bytesAt
    (hcode.low (by simp) (by simp)), dec_r8_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, decSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem dec_r8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p) (codeRange p [0xFE, modrm])
      (Effect.post (decR8Effect p 2 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => decR8Effect_avoids p _ _ s _)
    (dec_r8_effect_step p modrm hmod hreg hrm8)

theorem dec_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xFE, modrm])
      (decR8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, dec_r8_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), dec_r8_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, decSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem dec_r8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xFE, modrm])
      (Effect.post (decR8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => decR8Effect_avoids p _ _ s _)
    (dec_r8_rex_effect_step p rex modrm hrex hmod hreg)

theorem dec_r8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeDecR8 dst))
      (Effect.post (decR8Effect p (encodeDecR8 dst).length (dst.setWidth 5))) := by
  rcases encodeDecR8_spec dst with ⟨modrm, hbytes, hmod, hreg, hrm8, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact dec_r8_triple_of_bytes p modrm hmod hreg hrm8
  · rw [hbytes, ← hdst]
    exact dec_r8_rex_triple_of_bytes p rex modrm hrex hmod hreg

def decR8NoRexEffect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (s : RamState) : Effect :=
  let a := (Operand.byteReg dst).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (byteRegGpr dst) : Operand 64),
      mergeByteReg dst (a - 1) ((Operand.reg (byteRegGpr dst) : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (decSpec (StatusFlags.ofRFLAGS s.RFLAGS) a).2) }

@[simp] theorem decR8NoRexEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (s : RamState) :
    (decR8NoRexEffect p len dst s).components = [.reg (byteRegGpr dst), .flags, .rip] :=
  rfl

theorem decR8NoRexEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 3) (s : RamState)
    (code : CodeMap) : (decR8NoRexEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem dec_r8_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xFE, modrm])
      (decR8NoRexEffect p 2 (modrmRm modrm)) := by
  rintro s h hcode rfl
  have hs := dec_r8_norex_step s h modrm hmod hreg hcode.bytesAt (hcode.low (by simp) (by simp))
  have hr := dec_r8_norex_ready h modrm
  simp only [writeOutputs_byteReg] at hs hr
  refine ⟨_, hs, hr,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, decSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem dec_r8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [0xFE, modrm])
      (Effect.post (decR8NoRexEffect p 2 (modrmRm modrm))) :=
  Triple.of_effect (fun s _ => decR8NoRexEffect_avoids p _ _ s _)
    (dec_r8_norex_effect_step p modrm hmod hreg)

theorem dec_r8_norex_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeDecR8NoRex dst))
      (Effect.post (decR8NoRexEffect p 2 dst)) := by
  have h := dec_r8_norex_triple_of_bytes p (modrmRegs 1 dst) (modrmMod_modrmRegs _ _)
    (modrmReg_modrmRegs _ _)
  rwa [modrmRm_modrmRegs] at h

attribute [x86_compose] decR8Effect decR8NoRexEffect

@[x86_local] theorem decR8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (decR8Effect p len dst) := by
  effect_local [decR8Effect, decSpec]

@[x86_local] theorem decR8NoRexEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3} :
    Effect.Local (decR8NoRexEffect p len dst) := by
  effect_local [decR8NoRexEffect, decSpec]

end X86Proofs
