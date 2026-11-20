import X86Proofs.Instructions.Inc.Generated.R.Step
import X86Proofs.Instructions.Inc.Generated.R.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def incR64Effect (p : BitVec 64) (dst : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64), a + 1⟩]
    flags := some (.ofStatusFlags (incSpec (StatusFlags.ofRFLAGS s.RFLAGS) a).2) }

@[simp] theorem incR64Effect_components (p : BitVec 64) (dst : BitVec 5) (s : RamState) :
    (incR64Effect p dst s).components = [.reg dst, .flags, .rip] := rfl

theorem incR64Effect_avoids (p : BitVec 64) (dst : BitVec 5) (s : RamState) (code : CodeMap) :
    (incR64Effect p dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def incR32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (a + 1).setWidth 64⟩]
    flags := some (.ofStatusFlags (incSpec (StatusFlags.ofRFLAGS s.RFLAGS) a).2) }

@[simp] theorem incR32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (incR32Effect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem incR32Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (incR32Effect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def incR16Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (a + 1) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (incSpec (StatusFlags.ofRFLAGS s.RFLAGS) a).2) }

@[simp] theorem incR16Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (incR16Effect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem incR16Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (incR16Effect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem inc_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xFF, modrm])
      (incR64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, inc_r64_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), inc_r64_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, incSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem inc_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xFF, modrm])
      (Effect.post (incR64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => incR64Effect_avoids p _ s _)
    (inc_r64_effect_step p rex modrm hrex hmod hreg)

theorem inc_r32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xFF, modrm])
      (incR32Effect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, inc_r32_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), inc_r32_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, incSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem inc_r32_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [0xFF, modrm])
      (Effect.post (incR32Effect p 2 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => incR32Effect_avoids p _ _ s _)
    (inc_r32_effect_step p modrm hmod hreg)

theorem inc_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xFF, modrm])
      (incR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, inc_r32_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), inc_r32_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, incSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem inc_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xFF, modrm])
      (Effect.post (incR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => incR32Effect_avoids p _ _ s _)
    (inc_r32_rex_effect_step p rex modrm hrex hmod hreg)

theorem inc_r16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0xFF, modrm])
      (incR16Effect p 3 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, inc_r16_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), inc_r16_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, incSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem inc_r16_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, 0xFF, modrm])
      (Effect.post (incR16Effect p 3 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => incR16Effect_avoids p _ _ s _)
    (inc_r16_effect_step p modrm hmod hreg)

theorem inc_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xFF, modrm])
      (incR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, inc_r16_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), inc_r16_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, incSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem inc_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xFF, modrm])
      (Effect.post (incR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => incR16Effect_avoids p _ _ s _)
    (inc_r16_rex_effect_step p rex modrm hrex hmod hreg)

theorem inc_r64_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeIncR64 dst))
      (Effect.post (incR64Effect p (dst.setWidth 5))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeIncR64_spec dst
  rw [hbytes, ← hdst]
  exact inc_r64_triple_of_bytes p rex modrm hrex hmod hreg

theorem inc_r32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeIncR32 dst))
      (Effect.post (incR32Effect p (encodeIncR32 dst).length (dst.setWidth 5))) := by
  rcases encodeIncR32_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact inc_r32_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact inc_r32_rex_triple_of_bytes p rex modrm hrex hmod hreg

theorem inc_r16_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeIncR16 dst))
      (Effect.post (incR16Effect p (encodeIncR16 dst).length (dst.setWidth 5))) := by
  rcases encodeIncR16_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact inc_r16_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact inc_r16_rex_triple_of_bytes p rex modrm hrex hmod hreg

attribute [x86_compose] incR64Effect incR32Effect incR16Effect

@[x86_local] theorem incR64Effect_local {p : BitVec 64} {dst : BitVec 5} :
    Effect.Local (incR64Effect p dst) := by
  effect_local [incR64Effect, incSpec]

@[x86_local] theorem incR32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (incR32Effect p len dst) := by
  effect_local [incR32Effect, incSpec]

@[x86_local] theorem incR16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (incR16Effect p len dst) := by
  effect_local [incR16Effect, incSpec]

end X86Proofs
