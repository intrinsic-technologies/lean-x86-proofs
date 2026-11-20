import X86Proofs.Instructions.Or.Generated.RR.Step
import X86Proofs.Instructions.Or.Generated.RR.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def orFlags {n : Nat} (r : BitVec n) : StatusFlagsOutcome where
  CF := some false
  PF := some (evenParity (r.extractLsb' 0 8))
  AF := none
  ZF := some (r == 0)
  SF := some r.msb
  OF := some false

def orR64R64Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  let r := (Operand.reg dst : Operand 64).read s ||| (Operand.reg src : Operand 64).read s
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64), r⟩]
    flags := some (orFlags r) }

@[simp] theorem orR64R64Effect_components (p : BitVec 64) (dst src : BitVec 5) (s : RamState) :
    (orR64R64Effect p dst src s).components = [.reg dst, .flags, .rip] := rfl

theorem orR64R64Effect_avoids (p : BitVec 64) (dst src : BitVec 5) (s : RamState)
    (code : CodeMap) : (orR64R64Effect p dst src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def orR32R32Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) : Effect :=
  let r := (Operand.reg dst : Operand 32).read s ||| (Operand.reg src : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), r.setWidth 64⟩]
    flags := some (orFlags r) }

@[simp] theorem orR32R32Effect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : (orR32R32Effect p len dst src s).components = [.reg dst, .flags, .rip] := rfl

theorem orR32R32Effect_avoids (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState)
    (code : CodeMap) : (orR32R32Effect p len dst src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def orR16R16Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := (Operand.reg src : Operand 16).read s
  let r := a ||| b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (r) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (orFlags r) }

@[simp] theorem orR16R16Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (s : RamState) :
    (orR16R16Effect p len dst src s).components = [.reg dst, .flags, .rip] := rfl

theorem orR16R16Effect_avoids (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) (code : CodeMap) : (orR16R16Effect p len dst src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem or_r64_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x09, modrm])
      (orR64R64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, or_r64_r64_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), or_r64_r64_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, orSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem or_r64_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0x09, modrm])
      (Effect.post (orR64R64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => orR64R64Effect_avoids p _ _ s _)
    (or_r64_r64_effect_step p rex modrm hrex hmod)

theorem or_r32_r32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x09, modrm])
      (orR32R32Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, or_r32_r32_step s h modrm hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), or_r32_r32_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, orSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem or_r32_r32_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [0x09, modrm])
      (Effect.post (orR32R32Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => orR32R32Effect_avoids p _ _ _ s _)
    (or_r32_r32_effect_step p modrm hmod)

theorem or_r32_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x09, modrm])
      (orR32R32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, or_r32_r32_rex_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), or_r32_r32_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, orSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem or_r32_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0x09, modrm])
      (Effect.post (orR32R32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => orR32R32Effect_avoids p _ _ _ s _)
    (or_r32_r32_rex_effect_step p rex modrm hrex hmod)

theorem or_r16_r16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0x09, modrm])
      (orR16R16Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, or_r16_r16_step s h modrm hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), or_r16_r16_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, orSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem or_r16_r16_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, 0x09, modrm])
      (Effect.post (orR16R16Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => orR16R16Effect_avoids p _ _ _ s _)
    (or_r16_r16_effect_step p modrm hmod)

theorem or_r16_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, rex, 0x09, modrm])
      (orR16R16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, or_r16_r16_rex_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), or_r16_r16_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, orSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem or_r16_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, rex, 0x09, modrm])
      (Effect.post (orR16R16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => orR16R16Effect_avoids p _ _ _ s _)
    (or_r16_r16_rex_effect_step p rex modrm hrex hmod)

theorem or_r64_r64_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeOrR64R64 dst src))
      (Effect.post (orR64R64Effect p (dst.setWidth 5) (src.setWidth 5))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeOrR64R64_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact or_r64_r64_triple_of_bytes p rex modrm hrex hmod

theorem or_r32_r32_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeOrR32R32 dst src))
      (Effect.post (orR32R32Effect p (encodeOrR32R32 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  rcases encodeOrR32R32_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact or_r32_r32_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact or_r32_r32_rex_triple_of_bytes p rex modrm hrex hmod

theorem or_r16_r16_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeOrR16R16 dst src))
      (Effect.post (orR16R16Effect p (encodeOrR16R16 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  rcases encodeOrR16R16_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact or_r16_r16_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact or_r16_r16_rex_triple_of_bytes p rex modrm hrex hmod

attribute [x86_compose] orR64R64Effect orR32R32Effect orR16R16Effect orFlags

@[x86_local] theorem orR64R64Effect_local {p : BitVec 64} {dst src : BitVec 5} :
    Effect.Local (orR64R64Effect p dst src) := by
  effect_local [orR64R64Effect]

@[x86_local] theorem orR32R32Effect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5} :
    Effect.Local (orR32R32Effect p len dst src) := by
  effect_local [orR32R32Effect]

@[x86_local] theorem orR16R16Effect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5} :
    Effect.Local (orR16R16Effect p len dst src) := by
  effect_local [orR16R16Effect]

end X86Proofs
