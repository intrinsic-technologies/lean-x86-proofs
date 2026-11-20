import X86Proofs.Instructions.Dec.Generated.R.Step
import X86Proofs.Instructions.Dec.Generated.R.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def decR64Effect (p : BitVec 64) (dst : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64), a - 1⟩]
    flags := some (.ofStatusFlags (decSpec (StatusFlags.ofRFLAGS s.RFLAGS) a).2) }

@[simp] theorem decR64Effect_components (p : BitVec 64) (dst : BitVec 5) (s : RamState) :
    (decR64Effect p dst s).components = [.reg dst, .flags, .rip] := rfl

theorem decR64Effect_avoids (p : BitVec 64) (dst : BitVec 5) (s : RamState) (code : CodeMap) :
    (decR64Effect p dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def decR32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (a - 1).setWidth 64⟩]
    flags := some (.ofStatusFlags (decSpec (StatusFlags.ofRFLAGS s.RFLAGS) a).2) }

@[simp] theorem decR32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (decR32Effect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem decR32Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (decR32Effect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def decR16Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (a - 1) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (decSpec (StatusFlags.ofRFLAGS s.RFLAGS) a).2) }

@[simp] theorem decR16Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (decR16Effect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem decR16Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (decR16Effect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem dec_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xFF, modrm])
      (decR64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, dec_r64_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), dec_r64_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, decSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem dec_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xFF, modrm])
      (Effect.post (decR64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => decR64Effect_avoids p _ s _)
    (dec_r64_effect_step p rex modrm hrex hmod hreg)

theorem dec_r32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xFF, modrm])
      (decR32Effect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, dec_r32_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), dec_r32_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, decSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem dec_r32_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [0xFF, modrm])
      (Effect.post (decR32Effect p 2 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => decR32Effect_avoids p _ _ s _)
    (dec_r32_effect_step p modrm hmod hreg)

theorem dec_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xFF, modrm])
      (decR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, dec_r32_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), dec_r32_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, decSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem dec_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xFF, modrm])
      (Effect.post (decR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => decR32Effect_avoids p _ _ s _)
    (dec_r32_rex_effect_step p rex modrm hrex hmod hreg)

theorem dec_r16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0xFF, modrm])
      (decR16Effect p 3 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, dec_r16_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), dec_r16_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, decSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem dec_r16_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, 0xFF, modrm])
      (Effect.post (decR16Effect p 3 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => decR16Effect_avoids p _ _ s _)
    (dec_r16_effect_step p modrm hmod hreg)

theorem dec_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xFF, modrm])
      (decR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, dec_r16_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), dec_r16_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, decSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem dec_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xFF, modrm])
      (Effect.post (decR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => decR16Effect_avoids p _ _ s _)
    (dec_r16_rex_effect_step p rex modrm hrex hmod hreg)

theorem dec_r64_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeDecR64 dst))
      (Effect.post (decR64Effect p (dst.setWidth 5))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeDecR64_spec dst
  rw [hbytes, ← hdst]
  exact dec_r64_triple_of_bytes p rex modrm hrex hmod hreg

theorem dec_r32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeDecR32 dst))
      (Effect.post (decR32Effect p (encodeDecR32 dst).length (dst.setWidth 5))) := by
  rcases encodeDecR32_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact dec_r32_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact dec_r32_rex_triple_of_bytes p rex modrm hrex hmod hreg

theorem dec_r16_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeDecR16 dst))
      (Effect.post (decR16Effect p (encodeDecR16 dst).length (dst.setWidth 5))) := by
  rcases encodeDecR16_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact dec_r16_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact dec_r16_rex_triple_of_bytes p rex modrm hrex hmod hreg

attribute [x86_compose] decR64Effect decR32Effect decR16Effect

@[x86_local] theorem decR64Effect_local {p : BitVec 64} {dst : BitVec 5} :
    Effect.Local (decR64Effect p dst) := by
  effect_local [decR64Effect, decSpec]

@[x86_local] theorem decR32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (decR32Effect p len dst) := by
  effect_local [decR32Effect, decSpec]

@[x86_local] theorem decR16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (decR16Effect p len dst) := by
  effect_local [decR16Effect, decSpec]

end X86Proofs
