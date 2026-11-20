import X86Proofs.Instructions.Ror.Generated.R.Step
import X86Proofs.Instructions.Ror.Generated.R.Encode
import X86Proofs.Program.Compose
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def rorR64Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), a.rotateRight c⟩]
    flags := some (rorFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[simp] theorem rorR64Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat)
    (s : RamState) : (rorR64Effect p len dst c s).components = [.reg dst, .flags, .rip] := rfl

theorem rorR64Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState)
    (code : CodeMap) : (rorR64Effect p len dst c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def rorR32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (a.rotateRight c).setWidth 64⟩]
    flags := some (rorFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[simp] theorem rorR32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat)
    (s : RamState) : (rorR32Effect p len dst c s).components = [.reg dst, .flags, .rip] := rfl

theorem rorR32Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState)
    (code : CodeMap) : (rorR32Effect p len dst c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def rorR16Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (a.rotateRight c) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (rorFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[simp] theorem rorR16Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat)
    (s : RamState) : (rorR16Effect p len dst c s).components = [.reg dst, .flags, .rip] := rfl

theorem rorR16Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState)
    (code : CodeMap) : (rorR16Effect p len dst c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem ror_r64_imm8_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (rorR64Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 64 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, ror_r64_imm8_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), ror_r64_imm8_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, rorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rorFlags_allows

theorem ror_r64_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (Effect.post (rorR64Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 64 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => rorR64Effect_avoids p _ _ _ s _)
    (ror_r64_imm8_effect_step p rex modrm imm hrex hmod hreg)

theorem ror_r32_imm8_effect_step [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xC1, modrm, imm])
      (rorR32Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 32 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, ror_r32_imm8_step s h modrm imm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), ror_r32_imm8_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, rorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rorFlags_allows

theorem ror_r32_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [0xC1, modrm, imm])
      (Effect.post (rorR32Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 32 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => rorR32Effect_avoids p _ _ _ s _)
    (ror_r32_imm8_effect_step p modrm imm hmod hreg)

theorem ror_r32_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (rorR32Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 32 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, ror_r32_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), ror_r32_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, rorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rorFlags_allows

theorem ror_r32_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (Effect.post (rorR32Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 32 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => rorR32Effect_avoids p _ _ _ s _)
    (ror_r32_imm8_rex_effect_step p rex modrm imm hrex hmod hreg)

theorem ror_r16_imm8_effect_step [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0xC1, modrm, imm])
      (rorR16Effect p 4 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 16 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, ror_r16_imm8_step s h modrm imm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), ror_r16_imm8_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rorFlags_allows

theorem ror_r16_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, 0xC1, modrm, imm])
      (Effect.post (rorR16Effect p 4 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 16 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => rorR16Effect_avoids p _ _ _ s _)
    (ror_r16_imm8_effect_step p modrm imm hmod hreg)

theorem ror_r16_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xC1, modrm, imm])
      (rorR16Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 16 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, ror_r16_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), ror_r16_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 5 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 5 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rorFlags_allows

theorem ror_r16_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xC1, modrm, imm])
      (Effect.post (rorR16Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 16 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => rorR16Effect_avoids p _ _ _ s _)
    (ror_r16_imm8_rex_effect_step p rex modrm imm hrex hmod hreg)

theorem ror_r64_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRorR64Imm8 dst imm))
      (Effect.post (rorR64Effect p
        4 (dst.setWidth 5)
        (shiftCount 64 imm))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeRorR64Imm8_spec imm dst
  rw [hbytes, ← hdst, immBytes_eight]
  exact ror_r64_imm8_triple_of_bytes p rex modrm (UInt8.ofBitVec imm) hrex hmod hreg

theorem ror_r32_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRorR32Imm8 dst imm))
      (Effect.post (rorR32Effect p
        (encodeRorR32Imm8 dst imm).length (dst.setWidth 5)
        (shiftCount 32 imm))) := by
  rcases encodeRorR32Imm8_spec imm dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst, immBytes_eight]
    exact ror_r32_imm8_triple_of_bytes p modrm (UInt8.ofBitVec imm) hmod hreg
  · rw [hbytes, ← hdst, immBytes_eight]
    exact ror_r32_imm8_rex_triple_of_bytes p rex modrm (UInt8.ofBitVec imm) hrex hmod hreg

theorem ror_r16_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRorR16Imm8 dst imm))
      (Effect.post (rorR16Effect p
        (encodeRorR16Imm8 dst imm).length (dst.setWidth 5)
        (shiftCount 16 imm))) := by
  rcases encodeRorR16Imm8_spec imm dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst, immBytes_eight]
    exact ror_r16_imm8_triple_of_bytes p modrm (UInt8.ofBitVec imm) hmod hreg
  · rw [hbytes, ← hdst, immBytes_eight]
    exact ror_r16_imm8_rex_triple_of_bytes p rex modrm (UInt8.ofBitVec imm) hrex hmod hreg

theorem ror_r64_one_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD1, modrm])
      (rorR64Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, ror_r64_one_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), ror_r64_one_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, rorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rorFlags_allows

theorem ror_r64_one_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xD1, modrm])
      (Effect.post (rorR64Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => rorR64Effect_avoids p _ _ _ s _)
    (ror_r64_one_effect_step p rex modrm hrex hmod hreg)

theorem ror_r32_one_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xD1, modrm])
      (rorR32Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, ror_r32_one_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), ror_r32_one_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, rorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rorFlags_allows

theorem ror_r32_one_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [0xD1, modrm])
      (Effect.post (rorR32Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => rorR32Effect_avoids p _ _ _ s _)
    (ror_r32_one_effect_step p modrm hmod hreg)

theorem ror_r32_one_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD1, modrm])
      (rorR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, ror_r32_one_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), ror_r32_one_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, rorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rorFlags_allows

theorem ror_r32_one_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xD1, modrm])
      (Effect.post (rorR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => rorR32Effect_avoids p _ _ _ s _)
    (ror_r32_one_rex_effect_step p rex modrm hrex hmod hreg)

theorem ror_r16_one_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0xD1, modrm])
      (rorR16Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, ror_r16_one_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), ror_r16_one_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rorFlags_allows

theorem ror_r16_one_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, 0xD1, modrm])
      (Effect.post (rorR16Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => rorR16Effect_avoids p _ _ _ s _)
    (ror_r16_one_effect_step p modrm hmod hreg)

theorem ror_r16_one_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xD1, modrm])
      (rorR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, ror_r16_one_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), ror_r16_one_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rorFlags_allows

theorem ror_r16_one_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xD1, modrm])
      (Effect.post (rorR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => rorR16Effect_avoids p _ _ _ s _)
    (ror_r16_one_rex_effect_step p rex modrm hrex hmod hreg)

theorem ror_r64_one_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRorR64One dst))
      (Effect.post (rorR64Effect p
        3 (dst.setWidth 5)
        (1))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeRorR64One_spec dst
  rw [hbytes, ← hdst]
  exact ror_r64_one_triple_of_bytes p rex modrm hrex hmod hreg

theorem ror_r32_one_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRorR32One dst))
      (Effect.post (rorR32Effect p
        (encodeRorR32One dst).length (dst.setWidth 5)
        (1))) := by
  rcases encodeRorR32One_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact ror_r32_one_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact ror_r32_one_rex_triple_of_bytes p rex modrm hrex hmod hreg

theorem ror_r16_one_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeRorR16One dst))
      (Effect.post (rorR16Effect p
        (encodeRorR16One dst).length (dst.setWidth 5)
        (1))) := by
  rcases encodeRorR16One_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact ror_r16_one_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact ror_r16_one_rex_triple_of_bytes p rex modrm hrex hmod hreg

attribute [x86_compose] rorR64Effect rorR32Effect rorR16Effect

@[x86_local] theorem rorR64Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {c : Nat} :
    Effect.Local (rorR64Effect p len dst c) := by
  effect_local [rorR64Effect, rorFlags]

@[x86_local] theorem rorR32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {c : Nat} :
    Effect.Local (rorR32Effect p len dst c) := by
  effect_local [rorR32Effect, rorFlags]

@[x86_local] theorem rorR16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {c : Nat} :
    Effect.Local (rorR16Effect p len dst c) := by
  effect_local [rorR16Effect, rorFlags]

end X86Proofs
