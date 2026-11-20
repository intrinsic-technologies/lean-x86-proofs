import X86Proofs.Instructions.Xor.Generated.R8.Step
import X86Proofs.Instructions.Xor.Generated.R8.Encode
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Xor.Generated.RR.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def xorR8R8Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  let b := (Operand.reg src : Operand 8).read s
  let r := a ^^^ b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (r) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (xorFlags r) }

@[simp] theorem xorR8R8Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (s : RamState) :
    (xorR8R8Effect p len dst src s).components = [.reg dst, .flags, .rip] := rfl

theorem xorR8R8Effect_avoids (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) (code : CodeMap) : (xorR8R8Effect p len dst src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def xorR8R8NoRexEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 3) (s : RamState) : Effect :=
  let a := (Operand.byteReg dst).read s
  let b := (Operand.byteReg src).read s
  let r := a ^^^ b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (byteRegGpr dst) : Operand 64),
      mergeByteReg dst (r) ((Operand.reg (byteRegGpr dst) : Operand 64).read s)⟩]
    flags := some (xorFlags r) }

@[simp] theorem xorR8R8NoRexEffect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 3) (s : RamState) :
    (xorR8R8NoRexEffect p len dst src s).components =
      [.reg (byteRegGpr dst), .flags, .rip] := rfl

theorem xorR8R8NoRexEffect_avoids (p : BitVec 64) (len : Nat) (dst src : BitVec 3)
    (s : RamState) (code : CodeMap) : (xorR8R8NoRexEffect p len dst src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem xor_r8_r8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3)
    (hreg8 : (modrmReg modrm).toNat < 4) (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x30, modrm])
      (xorR8R8Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, xor_r8_r8_step s h modrm hmod hreg8 hrm8 hcode.bytesAt
    (hcode.low (by simp) (by simp)), xor_r8_r8_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, xorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_r8_r8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3)
    (hreg8 : (modrmReg modrm).toNat < 4) (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p) (codeRange p [0x30, modrm])
      (Effect.post (xorR8R8Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => xorR8R8Effect_avoids p _ _ _ s _)
    (xor_r8_r8_effect_step p modrm hmod hreg8 hrm8)

theorem xor_r8_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x30, modrm])
      (xorR8R8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, xor_r8_r8_rex_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), xor_r8_r8_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, xorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_r8_r8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0x30, modrm])
      (Effect.post (xorR8R8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => xorR8R8Effect_avoids p _ _ _ s _)
    (xor_r8_r8_rex_effect_step p rex modrm hrex hmod)

theorem xor_r8_r8_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeXorR8R8 dst src))
      (Effect.post (xorR8R8Effect p (encodeXorR8R8 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  rcases encodeXorR8R8_spec dst src with ⟨modrm, hbytes, hmod, hreg8, hrm8, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact xor_r8_r8_triple_of_bytes p modrm hmod hreg8 hrm8
  · rw [hbytes, ← hdst, ← hsrc]
    exact xor_r8_r8_rex_triple_of_bytes p rex modrm hrex hmod

theorem xor_r8_r8_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x30, modrm])
      (xorR8R8NoRexEffect p 2 (modrmRm modrm) (modrmReg modrm)) := by
  rintro s h hcode rfl
  have hs := xor_r8_r8_norex_step s h modrm hmod hcode.bytesAt (hcode.low (by simp) (by simp))
  have hr := xor_r8_r8_norex_ready h modrm
  simp only [writeOutputs_byteReg] at hs hr
  refine ⟨_, hs, hr,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, xorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_r8_r8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [0x30, modrm])
      (Effect.post (xorR8R8NoRexEffect p 2 (modrmRm modrm) (modrmReg modrm))) :=
  Triple.of_effect (fun s _ => xorR8R8NoRexEffect_avoids p _ _ _ s _)
    (xor_r8_r8_norex_effect_step p modrm hmod)

theorem xor_r8_r8_norex_triple [Bindings] (p : BitVec 64) (dst src : BitVec 3) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeXorR8R8NoRex dst src))
      (Effect.post (xorR8R8NoRexEffect p 2 dst src)) := by
  have h := xor_r8_r8_norex_triple_of_bytes p (modrmRegs src dst) (modrmMod_modrmRegs _ _)
  rwa [modrmRm_modrmRegs, modrmReg_modrmRegs] at h

attribute [x86_compose] xorR8R8Effect xorR8R8NoRexEffect

@[x86_local] theorem xorR8R8Effect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5} :
    Effect.Local (xorR8R8Effect p len dst src) := by
  effect_local [xorR8R8Effect]

@[x86_local] theorem xorR8R8NoRexEffect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 3} :
    Effect.Local (xorR8R8NoRexEffect p len dst src) := by
  effect_local [xorR8R8NoRexEffect]

end X86Proofs
