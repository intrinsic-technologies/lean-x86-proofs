import X86Proofs.Instructions.Test.Generated.RR.Step
import X86Proofs.Instructions.Test.Generated.RR.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def testFlags {n : Nat} (r : BitVec n) : StatusFlagsOutcome where
  CF := some false
  PF := some (evenParity (r.extractLsb' 0 8))
  AF := none
  ZF := some (r == 0)
  SF := some r.msb
  OF := some false

def testR64R64Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  let r := (Operand.reg dst : Operand 64).read s &&& (Operand.reg src : Operand 64).read s
  { rip := p + 3
    writes := []
    flags := some (testFlags r) }

@[simp] theorem testR64R64Effect_components (p : BitVec 64) (dst src : BitVec 5) (s : RamState) :
    (testR64R64Effect p dst src s).components = [.flags, .rip] := rfl

theorem testR64R64Effect_avoids (p : BitVec 64) (dst src : BitVec 5) (s : RamState)
    (code : CodeMap) : (testR64R64Effect p dst src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def testR32R32Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) : Effect :=
  let r := (Operand.reg dst : Operand 32).read s &&& (Operand.reg src : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (testFlags r) }

@[simp] theorem testR32R32Effect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : (testR32R32Effect p len dst src s).components = [.flags, .rip] := rfl

theorem testR32R32Effect_avoids (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState)
    (code : CodeMap) : (testR32R32Effect p len dst src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def testR16R16Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := (Operand.reg src : Operand 16).read s
  let r := a &&& b
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (testFlags r) }

@[simp] theorem testR16R16Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (s : RamState) :
    (testR16R16Effect p len dst src s).components = [.flags, .rip] := rfl

theorem testR16R16Effect_avoids (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) (code : CodeMap) : (testR16R16Effect p len dst src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem test_r64_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x85, modrm])
      (testR64R64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, test_r64_r64_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), test_r64_r64_ready h rex modrm,
    ⟨afterStep_writeFlagsOutputs_rip h 3 _ 1 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 3 _ 1 _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r64_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0x85, modrm])
      (Effect.post (testR64R64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => testR64R64Effect_avoids p _ _ s _)
    (test_r64_r64_effect_step p rex modrm hrex hmod)

theorem test_r32_r32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x85, modrm])
      (testR32R32Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, test_r32_r32_step s h modrm hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), test_r32_r32_ready h modrm,
    ⟨afterStep_writeFlagsOutputs_rip h 2 _ 1 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 2 _ 1 _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r32_r32_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [0x85, modrm])
      (Effect.post (testR32R32Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => testR32R32Effect_avoids p _ _ _ s _)
    (test_r32_r32_effect_step p modrm hmod)

theorem test_r32_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x85, modrm])
      (testR32R32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, test_r32_r32_rex_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), test_r32_r32_rex_ready h rex modrm,
    ⟨afterStep_writeFlagsOutputs_rip h 3 _ 1 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 3 _ 1 _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r32_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0x85, modrm])
      (Effect.post (testR32R32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => testR32R32Effect_avoids p _ _ _ s _)
    (test_r32_r32_rex_effect_step p rex modrm hrex hmod)

theorem test_r16_r16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0x85, modrm])
      (testR16R16Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, test_r16_r16_step s h modrm hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), test_r16_r16_ready h modrm,
    ⟨afterStep_writeFlagsOutputs_rip h 3 _ 1 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 3 _ 1 _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r16_r16_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, 0x85, modrm])
      (Effect.post (testR16R16Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => testR16R16Effect_avoids p _ _ _ s _)
    (test_r16_r16_effect_step p modrm hmod)

theorem test_r16_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, rex, 0x85, modrm])
      (testR16R16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, test_r16_r16_rex_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), test_r16_r16_rex_ready h rex modrm,
    ⟨afterStep_writeFlagsOutputs_rip h 4 _ 1 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 4 _ 1 _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r16_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, rex, 0x85, modrm])
      (Effect.post (testR16R16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => testR16R16Effect_avoids p _ _ _ s _)
    (test_r16_r16_rex_effect_step p rex modrm hrex hmod)

theorem test_r64_r64_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeTestR64R64 dst src))
      (Effect.post (testR64R64Effect p (dst.setWidth 5) (src.setWidth 5))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeTestR64R64_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact test_r64_r64_triple_of_bytes p rex modrm hrex hmod

theorem test_r32_r32_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeTestR32R32 dst src))
      (Effect.post (testR32R32Effect p (encodeTestR32R32 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  rcases encodeTestR32R32_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact test_r32_r32_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact test_r32_r32_rex_triple_of_bytes p rex modrm hrex hmod

theorem test_r16_r16_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeTestR16R16 dst src))
      (Effect.post (testR16R16Effect p (encodeTestR16R16 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  rcases encodeTestR16R16_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact test_r16_r16_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact test_r16_r16_rex_triple_of_bytes p rex modrm hrex hmod

attribute [x86_compose] testR64R64Effect testR32R32Effect testR16R16Effect testFlags

@[x86_local] theorem testR64R64Effect_local {p : BitVec 64} {dst src : BitVec 5} :
    Effect.Local (testR64R64Effect p dst src) := by
  effect_local [testR64R64Effect]

@[x86_local] theorem testR32R32Effect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5} :
    Effect.Local (testR32R32Effect p len dst src) := by
  effect_local [testR32R32Effect]

@[x86_local] theorem testR16R16Effect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5} :
    Effect.Local (testR16R16Effect p len dst src) := by
  effect_local [testR16R16Effect]

end X86Proofs
