import X86Proofs.Instructions.Not.Generated.R8.Step
import X86Proofs.Instructions.Not.Generated.R8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def notR8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (~~~a) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := none }

@[simp] theorem notR8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (notR8Effect p len dst s).components = [.reg dst, .rip] := rfl

theorem notR8Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (notR8Effect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem not_r8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xF6, modrm])
      (notR8Effect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, not_r8_step s h modrm hmod hreg hrm8 hcode.bytesAt
    (hcode.low (by simp) (by simp)), not_r8_ready h modrm,
    ⟨afterStep_writeResult_rip h 2 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 2 _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeResult_self_merge, notSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]

theorem not_r8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p) (codeRange p [0xF6, modrm])
      (Effect.post (notR8Effect p 2 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => notR8Effect_avoids p _ _ s _)
    (not_r8_effect_step p modrm hmod hreg hrm8)

theorem not_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xF6, modrm])
      (notR8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, not_r8_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), not_r8_rex_ready h rex modrm,
    ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 3 _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeResult_self_merge, notSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]

theorem not_r8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xF6, modrm])
      (Effect.post (notR8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => notR8Effect_avoids p _ _ s _)
    (not_r8_rex_effect_step p rex modrm hrex hmod hreg)

theorem not_r8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeNotR8 dst))
      (Effect.post (notR8Effect p (encodeNotR8 dst).length (dst.setWidth 5))) := by
  rcases encodeNotR8_spec dst with ⟨modrm, hbytes, hmod, hreg, hrm8, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact not_r8_triple_of_bytes p modrm hmod hreg hrm8
  · rw [hbytes, ← hdst]
    exact not_r8_rex_triple_of_bytes p rex modrm hrex hmod hreg

def notR8NoRexEffect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (s : RamState) : Effect :=
  let a := (Operand.byteReg dst).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (byteRegGpr dst) : Operand 64),
      mergeByteReg dst (~~~a) ((Operand.reg (byteRegGpr dst) : Operand 64).read s)⟩]
    flags := none }

@[simp] theorem notR8NoRexEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (s : RamState) :
    (notR8NoRexEffect p len dst s).components = [.reg (byteRegGpr dst), .rip] :=
  rfl

theorem notR8NoRexEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 3) (s : RamState)
    (code : CodeMap) : (notR8NoRexEffect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem not_r8_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xF6, modrm])
      (notR8NoRexEffect p 2 (modrmRm modrm)) := by
  rintro s h hcode rfl
  have hs := not_r8_norex_step s h modrm hmod hreg hcode.bytesAt (hcode.low (by simp) (by simp))
  have hr := not_r8_norex_ready h modrm
  simp only [writeResult_byteReg] at hs hr
  refine ⟨_, hs, hr,
    ⟨afterStep_writeResult_rip h 2 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 2 _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeResult_self, notSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]

theorem not_r8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p) (codeRange p [0xF6, modrm])
      (Effect.post (notR8NoRexEffect p 2 (modrmRm modrm))) :=
  Triple.of_effect (fun s _ => notR8NoRexEffect_avoids p _ _ s _)
    (not_r8_norex_effect_step p modrm hmod hreg)

theorem not_r8_norex_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeNotR8NoRex dst))
      (Effect.post (notR8NoRexEffect p 2 dst)) := by
  have h := not_r8_norex_triple_of_bytes p (modrmRegs 2 dst) (modrmMod_modrmRegs _ _)
    (modrmReg_modrmRegs _ _)
  rwa [modrmRm_modrmRegs] at h

attribute [x86_compose] notR8Effect notR8NoRexEffect

@[x86_local] theorem notR8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (notR8Effect p len dst) := by
  effect_local [notR8Effect]

@[x86_local] theorem notR8NoRexEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3} :
    Effect.Local (notR8NoRexEffect p len dst) := by
  effect_local [notR8NoRexEffect]

end X86Proofs
