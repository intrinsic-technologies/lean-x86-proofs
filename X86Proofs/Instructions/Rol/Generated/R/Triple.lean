import X86Proofs.Instructions.Rol.Generated.R.Step
import X86Proofs.Instructions.Rol.Generated.R.Encode
import X86Proofs.Program.Compose
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def rolR64Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), a.rotateLeft c⟩]
    flags := some (rolFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[simp] theorem rolR64Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat)
    (s : RamState) : (rolR64Effect p len dst c s).components = [.reg dst, .flags, .rip] := rfl

theorem rolR64Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState)
    (code : CodeMap) : (rolR64Effect p len dst c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def rolR32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (a.rotateLeft c).setWidth 64⟩]
    flags := some (rolFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[simp] theorem rolR32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat)
    (s : RamState) : (rolR32Effect p len dst c s).components = [.reg dst, .flags, .rip] := rfl

theorem rolR32Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState)
    (code : CodeMap) : (rolR32Effect p len dst c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def rolR16Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (a.rotateLeft c) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (rolFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[simp] theorem rolR16Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat)
    (s : RamState) : (rolR16Effect p len dst c s).components = [.reg dst, .flags, .rip] := rfl

theorem rolR16Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState)
    (code : CodeMap) : (rolR16Effect p len dst c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem rol_r64_imm8_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (rolR64Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 64 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, rol_r64_imm8_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rol_r64_imm8_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, rolSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rolFlags_allows

theorem rol_r64_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (Effect.post (rolR64Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 64 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => rolR64Effect_avoids p _ _ _ s _)
    (rol_r64_imm8_effect_step p rex modrm imm hrex hmod hreg)

theorem rol_r32_imm8_effect_step [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xC1, modrm, imm])
      (rolR32Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 32 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, rol_r32_imm8_step s h modrm imm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rol_r32_imm8_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, rolSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rolFlags_allows

theorem rol_r32_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [0xC1, modrm, imm])
      (Effect.post (rolR32Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 32 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => rolR32Effect_avoids p _ _ _ s _)
    (rol_r32_imm8_effect_step p modrm imm hmod hreg)

theorem rol_r32_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (rolR32Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 32 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, rol_r32_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rol_r32_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, rolSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rolFlags_allows

theorem rol_r32_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (Effect.post (rolR32Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 32 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => rolR32Effect_avoids p _ _ _ s _)
    (rol_r32_imm8_rex_effect_step p rex modrm imm hrex hmod hreg)

theorem rol_r16_imm8_effect_step [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0xC1, modrm, imm])
      (rolR16Effect p 4 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 16 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, rol_r16_imm8_step s h modrm imm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rol_r16_imm8_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rolSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rolFlags_allows

theorem rol_r16_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, 0xC1, modrm, imm])
      (Effect.post (rolR16Effect p 4 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 16 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => rolR16Effect_avoids p _ _ _ s _)
    (rol_r16_imm8_effect_step p modrm imm hmod hreg)

theorem rol_r16_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xC1, modrm, imm])
      (rolR16Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 16 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, rol_r16_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rol_r16_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 5 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 5 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rolSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rolFlags_allows

theorem rol_r16_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xC1, modrm, imm])
      (Effect.post (rolR16Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 16 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => rolR16Effect_avoids p _ _ _ s _)
    (rol_r16_imm8_rex_effect_step p rex modrm imm hrex hmod hreg)

theorem rol_r64_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRolR64Imm8 dst imm))
      (Effect.post (rolR64Effect p
        4 (dst.setWidth 5)
        (shiftCount 64 imm))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeRolR64Imm8_spec imm dst
  rw [hbytes, ← hdst, immBytes_eight]
  exact rol_r64_imm8_triple_of_bytes p rex modrm (UInt8.ofBitVec imm) hrex hmod hreg

theorem rol_r32_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRolR32Imm8 dst imm))
      (Effect.post (rolR32Effect p
        (encodeRolR32Imm8 dst imm).length (dst.setWidth 5)
        (shiftCount 32 imm))) := by
  rcases encodeRolR32Imm8_spec imm dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst, immBytes_eight]
    exact rol_r32_imm8_triple_of_bytes p modrm (UInt8.ofBitVec imm) hmod hreg
  · rw [hbytes, ← hdst, immBytes_eight]
    exact rol_r32_imm8_rex_triple_of_bytes p rex modrm (UInt8.ofBitVec imm) hrex hmod hreg

theorem rol_r16_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRolR16Imm8 dst imm))
      (Effect.post (rolR16Effect p
        (encodeRolR16Imm8 dst imm).length (dst.setWidth 5)
        (shiftCount 16 imm))) := by
  rcases encodeRolR16Imm8_spec imm dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst, immBytes_eight]
    exact rol_r16_imm8_triple_of_bytes p modrm (UInt8.ofBitVec imm) hmod hreg
  · rw [hbytes, ← hdst, immBytes_eight]
    exact rol_r16_imm8_rex_triple_of_bytes p rex modrm (UInt8.ofBitVec imm) hrex hmod hreg

theorem rol_r64_one_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD1, modrm])
      (rolR64Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, rol_r64_one_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rol_r64_one_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, rolSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rolFlags_allows

theorem rol_r64_one_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xD1, modrm])
      (Effect.post (rolR64Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => rolR64Effect_avoids p _ _ _ s _)
    (rol_r64_one_effect_step p rex modrm hrex hmod hreg)

theorem rol_r32_one_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xD1, modrm])
      (rolR32Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, rol_r32_one_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rol_r32_one_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, rolSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rolFlags_allows

theorem rol_r32_one_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [0xD1, modrm])
      (Effect.post (rolR32Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => rolR32Effect_avoids p _ _ _ s _)
    (rol_r32_one_effect_step p modrm hmod hreg)

theorem rol_r32_one_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD1, modrm])
      (rolR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, rol_r32_one_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rol_r32_one_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, rolSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rolFlags_allows

theorem rol_r32_one_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xD1, modrm])
      (Effect.post (rolR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => rolR32Effect_avoids p _ _ _ s _)
    (rol_r32_one_rex_effect_step p rex modrm hrex hmod hreg)

theorem rol_r16_one_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0xD1, modrm])
      (rolR16Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, rol_r16_one_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rol_r16_one_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rolSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rolFlags_allows

theorem rol_r16_one_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, 0xD1, modrm])
      (Effect.post (rolR16Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => rolR16Effect_avoids p _ _ _ s _)
    (rol_r16_one_effect_step p modrm hmod hreg)

theorem rol_r16_one_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xD1, modrm])
      (rolR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, rol_r16_one_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rol_r16_one_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rolSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rolFlags_allows

theorem rol_r16_one_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xD1, modrm])
      (Effect.post (rolR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => rolR16Effect_avoids p _ _ _ s _)
    (rol_r16_one_rex_effect_step p rex modrm hrex hmod hreg)

theorem rol_r64_one_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRolR64One dst))
      (Effect.post (rolR64Effect p
        3 (dst.setWidth 5)
        (1))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeRolR64One_spec dst
  rw [hbytes, ← hdst]
  exact rol_r64_one_triple_of_bytes p rex modrm hrex hmod hreg

theorem rol_r32_one_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRolR32One dst))
      (Effect.post (rolR32Effect p
        (encodeRolR32One dst).length (dst.setWidth 5)
        (1))) := by
  rcases encodeRolR32One_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact rol_r32_one_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact rol_r32_one_rex_triple_of_bytes p rex modrm hrex hmod hreg

theorem rol_r16_one_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRolR16One dst))
      (Effect.post (rolR16Effect p
        (encodeRolR16One dst).length (dst.setWidth 5)
        (1))) := by
  rcases encodeRolR16One_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact rol_r16_one_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact rol_r16_one_rex_triple_of_bytes p rex modrm hrex hmod hreg

attribute [x86_compose] rolR64Effect rolR32Effect rolR16Effect

@[x86_local] theorem rolR64Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {c : Nat} :
    Effect.Local (rolR64Effect p len dst c) := by
  effect_local [rolR64Effect, rolFlags]

@[x86_local] theorem rolR32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {c : Nat} :
    Effect.Local (rolR32Effect p len dst c) := by
  effect_local [rolR32Effect, rolFlags]

@[x86_local] theorem rolR16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {c : Nat} :
    Effect.Local (rolR16Effect p len dst c) := by
  effect_local [rolR16Effect, rolFlags]

end X86Proofs
