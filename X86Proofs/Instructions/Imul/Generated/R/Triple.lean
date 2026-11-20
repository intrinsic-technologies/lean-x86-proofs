import X86Proofs.Instructions.Imul.Generated.R.Step
import X86Proofs.Instructions.Imul.Generated.R.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def imulR64Effect (p : BitVec 64) (src : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 64).read s
  let b := (Operand.reg src : Operand 64).read s
  let r := imulWideResult a b
  { rip := p + 3
    writes := [⟨(Operand.reg 0 : Operand 64), r.1⟩,
      ⟨(Operand.reg 2 : Operand 64), r.2⟩]
    flags := some (imulWideFlags a b) }

@[simp] theorem imulR64Effect_components (p : BitVec 64) (src : BitVec 5) (s : RamState) :
    (imulR64Effect p src s).components = [.reg 0, .reg 2, .flags, .rip] := rfl

theorem imulR64Effect_avoids (p : BitVec 64) (src : BitVec 5) (s : RamState) (code : CodeMap) :
    (imulR64Effect p src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def imulR32Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 32).read s
  let b := (Operand.reg src : Operand 32).read s
  let r := imulWideResult a b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64), r.1.setWidth 64⟩,
      ⟨(Operand.reg 2 : Operand 64), r.2.setWidth 64⟩]
    flags := some (imulWideFlags a b) }

@[simp] theorem imulR32Effect_components (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (s : RamState) : (imulR32Effect p len src s).components = [.reg 0, .reg 2, .flags, .rip] := rfl

theorem imulR32Effect_avoids (p : BitVec 64) (len : Nat) (src : BitVec 5) (s : RamState)
    (code : CodeMap) : (imulR32Effect p len src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def imulR16Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 16).read s
  let b := (Operand.reg src : Operand 16).read s
  let r := imulWideResult a b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64), mergeGPR 16 r.1 ((Operand.reg 0 : Operand 64).read s)⟩,
      ⟨(Operand.reg 2 : Operand 64), mergeGPR 16 r.2 ((Operand.reg 2 : Operand 64).read s)⟩]
    flags := some (imulWideFlags a b) }

@[simp] theorem imulR16Effect_components (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (s : RamState) : (imulR16Effect p len src s).components = [.reg 0, .reg 2, .flags, .rip] := rfl

theorem imulR16Effect_avoids (p : BitVec 64) (len : Nat) (src : BitVec 5) (s : RamState)
    (code : CodeMap) : (imulR16Effect p len src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem imul_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p [rex, 0xF7, modrm])
      (imulR64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, imul_r64_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), imul_r64_ready h rex modrm,
    ⟨afterStep_writePairOutputs_rip h 3 _ _ _ _ _ 4 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writePairOutputs s 3 _ _ _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [imulWideSpec, Operand.read_afterFetches, Operand.read_beforeFetch, mergeGPR_64, and_self]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulWideFlags_allows _ _ _

theorem imul_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    Triple (fun s => s.RIP = p)
      (codeRange p [rex, 0xF7, modrm])
      (Effect.post (imulR64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => imulR64Effect_avoids p _ s _)
    (imul_r64_effect_step p rex modrm hrex hmod hreg)

theorem imul_r32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p [0xF7, modrm])
      (imulR32Effect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, imul_r32_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), imul_r32_ready h modrm,
    ⟨afterStep_writePairOutputs_rip h 2 _ _ _ _ _ 4 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writePairOutputs s 2 _ _ _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [imulWideSpec, Operand.read_afterFetches, Operand.read_beforeFetch, mergeGPR_32, and_self]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulWideFlags_allows _ _ _

theorem imul_r32_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    Triple (fun s => s.RIP = p)
      (codeRange p [0xF7, modrm])
      (Effect.post (imulR32Effect p 2 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => imulR32Effect_avoids p _ _ s _)
    (imul_r32_effect_step p modrm hmod hreg)

theorem imul_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p [rex, 0xF7, modrm])
      (imulR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, imul_r32_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), imul_r32_rex_ready h rex modrm,
    ⟨afterStep_writePairOutputs_rip h 3 _ _ _ _ _ 4 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writePairOutputs s 3 _ _ _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [imulWideSpec, Operand.read_afterFetches, Operand.read_beforeFetch, mergeGPR_32, and_self]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulWideFlags_allows _ _ _

theorem imul_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    Triple (fun s => s.RIP = p)
      (codeRange p [rex, 0xF7, modrm])
      (Effect.post (imulR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => imulR32Effect_avoids p _ _ s _)
    (imul_r32_rex_effect_step p rex modrm hrex hmod hreg)

theorem imul_r16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p [0x66, 0xF7, modrm])
      (imulR16Effect p 3 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, imul_r16_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), imul_r16_ready h modrm,
    ⟨afterStep_writePairOutputs_rip h 3 _ _ _ _ _ 4 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writePairOutputs s 3 _ _ _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [imulWideSpec, Operand.read_afterFetches, Operand.read_beforeFetch, and_self]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulWideFlags_allows _ _ _

theorem imul_r16_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    Triple (fun s => s.RIP = p)
      (codeRange p [0x66, 0xF7, modrm])
      (Effect.post (imulR16Effect p 3 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => imulR16Effect_avoids p _ _ s _)
    (imul_r16_effect_step p modrm hmod hreg)

theorem imul_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p [0x66, rex, 0xF7, modrm])
      (imulR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, imul_r16_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), imul_r16_rex_ready h rex modrm,
    ⟨afterStep_writePairOutputs_rip h 4 _ _ _ _ _ 4 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writePairOutputs s 4 _ _ _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [imulWideSpec, Operand.read_afterFetches, Operand.read_beforeFetch, and_self]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulWideFlags_allows _ _ _

theorem imul_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    Triple (fun s => s.RIP = p)
      (codeRange p [0x66, rex, 0xF7, modrm])
      (Effect.post (imulR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => imulR16Effect_avoids p _ _ s _)
    (imul_r16_rex_effect_step p rex modrm hrex hmod hreg)

theorem imul_r64_triple [Bindings] (p : BitVec 64) (src : BitVec 4) :
    Triple (fun s => s.RIP = p)
      (codeRange p (encodeImulR64 src))
      (Effect.post (imulR64Effect p (src.setWidth 5))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hsrc⟩ := encodeImulR64_spec src
  rw [hbytes, ← hsrc]
  exact imul_r64_triple_of_bytes p rex modrm hrex hmod hreg

theorem imul_r32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) :
    Triple (fun s => s.RIP = p)
      (codeRange p (encodeImulR32 src))
      (Effect.post (imulR32Effect p (encodeImulR32 src).length (src.setWidth 5))) := by
  rcases encodeImulR32_spec src with ⟨modrm, hbytes, hmod, hreg, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hsrc⟩
  · rw [hbytes, ← hsrc]
    exact imul_r32_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hsrc]
    exact imul_r32_rex_triple_of_bytes p rex modrm hrex hmod hreg

theorem imul_r16_triple [Bindings] (p : BitVec 64) (src : BitVec 4) :
    Triple (fun s => s.RIP = p)
      (codeRange p (encodeImulR16 src))
      (Effect.post (imulR16Effect p (encodeImulR16 src).length (src.setWidth 5))) := by
  rcases encodeImulR16_spec src with ⟨modrm, hbytes, hmod, hreg, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hsrc⟩
  · rw [hbytes, ← hsrc]
    exact imul_r16_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hsrc]
    exact imul_r16_rex_triple_of_bytes p rex modrm hrex hmod hreg

attribute [x86_compose] imulR64Effect imulR32Effect imulR16Effect

@[x86_local] theorem imulR64Effect_local {p : BitVec 64} {src : BitVec 5} :
    Effect.Local (imulR64Effect p src) := by
  effect_local [imulR64Effect, imulWideFlags]

@[x86_local] theorem imulR32Effect_local {p : BitVec 64} {len : Nat} {src : BitVec 5} :
    Effect.Local (imulR32Effect p len src) := by
  effect_local [imulR32Effect, imulWideFlags]

@[x86_local] theorem imulR16Effect_local {p : BitVec 64} {len : Nat} {src : BitVec 5} :
    Effect.Local (imulR16Effect p len src) := by
  effect_local [imulR16Effect, imulWideFlags]

end X86Proofs
