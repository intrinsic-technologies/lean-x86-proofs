import X86Proofs.Instructions.Neg.Generated.R.Step
import X86Proofs.Instructions.Neg.Generated.R.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def negR64Effect (p : BitVec 64) (dst : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64), -a⟩]
    flags := some (.ofStatusFlags (negSpec a).2) }

@[simp] theorem negR64Effect_components (p : BitVec 64) (dst : BitVec 5) (s : RamState) :
    (negR64Effect p dst s).components = [.reg dst, .flags, .rip] := rfl

theorem negR64Effect_avoids (p : BitVec 64) (dst : BitVec 5) (s : RamState) (code : CodeMap) :
    (negR64Effect p dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def negR32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (-a).setWidth 64⟩]
    flags := some (.ofStatusFlags (negSpec a).2) }

@[simp] theorem negR32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (negR32Effect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem negR32Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (negR32Effect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def negR16Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (-a) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (negSpec a).2) }

@[simp] theorem negR16Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (negR16Effect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem negR16Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (negR16Effect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem neg_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xF7, modrm])
      (negR64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, neg_r64_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), neg_r64_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, negSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem neg_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xF7, modrm])
      (Effect.post (negR64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => negR64Effect_avoids p _ s _)
    (neg_r64_effect_step p rex modrm hrex hmod hreg)

theorem neg_r32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xF7, modrm])
      (negR32Effect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, neg_r32_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), neg_r32_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, negSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem neg_r32_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [0xF7, modrm])
      (Effect.post (negR32Effect p 2 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => negR32Effect_avoids p _ _ s _)
    (neg_r32_effect_step p modrm hmod hreg)

theorem neg_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xF7, modrm])
      (negR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, neg_r32_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), neg_r32_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, negSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem neg_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xF7, modrm])
      (Effect.post (negR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => negR32Effect_avoids p _ _ s _)
    (neg_r32_rex_effect_step p rex modrm hrex hmod hreg)

theorem neg_r16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0xF7, modrm])
      (negR16Effect p 3 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, neg_r16_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), neg_r16_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, negSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem neg_r16_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, 0xF7, modrm])
      (Effect.post (negR16Effect p 3 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => negR16Effect_avoids p _ _ s _)
    (neg_r16_effect_step p modrm hmod hreg)

theorem neg_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xF7, modrm])
      (negR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, neg_r16_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), neg_r16_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, negSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem neg_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xF7, modrm])
      (Effect.post (negR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => negR16Effect_avoids p _ _ s _)
    (neg_r16_rex_effect_step p rex modrm hrex hmod hreg)

theorem neg_r64_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeNegR64 dst))
      (Effect.post (negR64Effect p (dst.setWidth 5))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeNegR64_spec dst
  rw [hbytes, ← hdst]
  exact neg_r64_triple_of_bytes p rex modrm hrex hmod hreg

theorem neg_r32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeNegR32 dst))
      (Effect.post (negR32Effect p (encodeNegR32 dst).length (dst.setWidth 5))) := by
  rcases encodeNegR32_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact neg_r32_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact neg_r32_rex_triple_of_bytes p rex modrm hrex hmod hreg

theorem neg_r16_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeNegR16 dst))
      (Effect.post (negR16Effect p (encodeNegR16 dst).length (dst.setWidth 5))) := by
  rcases encodeNegR16_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact neg_r16_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact neg_r16_rex_triple_of_bytes p rex modrm hrex hmod hreg

attribute [x86_compose] negR64Effect negR32Effect negR16Effect

@[x86_local] theorem negR64Effect_local {p : BitVec 64} {dst : BitVec 5} :
    Effect.Local (negR64Effect p dst) := by
  effect_local [negR64Effect]

@[x86_local] theorem negR32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (negR32Effect p len dst) := by
  effect_local [negR32Effect]

@[x86_local] theorem negR16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (negR16Effect p len dst) := by
  effect_local [negR16Effect]

end X86Proofs
