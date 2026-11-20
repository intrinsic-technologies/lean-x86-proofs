import X86Proofs.Instructions.Sar.Generated.R.Step
import X86Proofs.Instructions.Sar.Generated.R.Encode
import X86Proofs.Program.Compose
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def sarR64Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), a.sshiftRight c⟩]
    flags := some (sarFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[simp] theorem sarR64Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat)
    (s : RamState) : (sarR64Effect p len dst c s).components = [.reg dst, .flags, .rip] := rfl

theorem sarR64Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState)
    (code : CodeMap) : (sarR64Effect p len dst c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def sarR32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (a.sshiftRight c).setWidth 64⟩]
    flags := some (sarFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[simp] theorem sarR32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat)
    (s : RamState) : (sarR32Effect p len dst c s).components = [.reg dst, .flags, .rip] := rfl

theorem sarR32Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState)
    (code : CodeMap) : (sarR32Effect p len dst c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def sarR16Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (a.sshiftRight c) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (sarFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[simp] theorem sarR16Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat)
    (s : RamState) : (sarR16Effect p len dst c s).components = [.reg dst, .flags, .rip] := rfl

theorem sarR16Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState)
    (code : CodeMap) : (sarR16Effect p len dst c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem sar_r64_imm8_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (sarR64Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 64 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, sar_r64_imm8_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sar_r64_imm8_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, sarSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply sarFlags_allows

theorem sar_r64_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (Effect.post (sarR64Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 64 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => sarR64Effect_avoids p _ _ _ s _)
    (sar_r64_imm8_effect_step p rex modrm imm hrex hmod hreg)

theorem sar_r32_imm8_effect_step [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xC1, modrm, imm])
      (sarR32Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 32 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, sar_r32_imm8_step s h modrm imm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sar_r32_imm8_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, sarSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply sarFlags_allows

theorem sar_r32_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    Triple (fun s => s.RIP = p) (codeRange p [0xC1, modrm, imm])
      (Effect.post (sarR32Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 32 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => sarR32Effect_avoids p _ _ _ s _)
    (sar_r32_imm8_effect_step p modrm imm hmod hreg)

theorem sar_r32_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (sarR32Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 32 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, sar_r32_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sar_r32_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, sarSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply sarFlags_allows

theorem sar_r32_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (Effect.post (sarR32Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 32 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => sarR32Effect_avoids p _ _ _ s _)
    (sar_r32_imm8_rex_effect_step p rex modrm imm hrex hmod hreg)

theorem sar_r16_imm8_effect_step [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0xC1, modrm, imm])
      (sarR16Effect p 4 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 16 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, sar_r16_imm8_step s h modrm imm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sar_r16_imm8_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, sarSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply sarFlags_allows

theorem sar_r16_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, 0xC1, modrm, imm])
      (Effect.post (sarR16Effect p 4 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 16 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => sarR16Effect_avoids p _ _ _ s _)
    (sar_r16_imm8_effect_step p modrm imm hmod hreg)

theorem sar_r16_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xC1, modrm, imm])
      (sarR16Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 16 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, sar_r16_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sar_r16_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 5 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 5 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, sarSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply sarFlags_allows

theorem sar_r16_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xC1, modrm, imm])
      (Effect.post (sarR16Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 16 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => sarR16Effect_avoids p _ _ _ s _)
    (sar_r16_imm8_rex_effect_step p rex modrm imm hrex hmod hreg)

theorem sar_r64_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSarR64Imm8 dst imm))
      (Effect.post (sarR64Effect p
        4 (dst.setWidth 5)
        (shiftCount 64 imm))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeSarR64Imm8_spec imm dst
  rw [hbytes, ← hdst, immBytes_eight]
  exact sar_r64_imm8_triple_of_bytes p rex modrm (UInt8.ofBitVec imm) hrex hmod hreg

theorem sar_r32_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSarR32Imm8 dst imm))
      (Effect.post (sarR32Effect p
        (encodeSarR32Imm8 dst imm).length (dst.setWidth 5)
        (shiftCount 32 imm))) := by
  rcases encodeSarR32Imm8_spec imm dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst, immBytes_eight]
    exact sar_r32_imm8_triple_of_bytes p modrm (UInt8.ofBitVec imm) hmod hreg
  · rw [hbytes, ← hdst, immBytes_eight]
    exact sar_r32_imm8_rex_triple_of_bytes p rex modrm (UInt8.ofBitVec imm) hrex hmod hreg

theorem sar_r16_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSarR16Imm8 dst imm))
      (Effect.post (sarR16Effect p
        (encodeSarR16Imm8 dst imm).length (dst.setWidth 5)
        (shiftCount 16 imm))) := by
  rcases encodeSarR16Imm8_spec imm dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst, immBytes_eight]
    exact sar_r16_imm8_triple_of_bytes p modrm (UInt8.ofBitVec imm) hmod hreg
  · rw [hbytes, ← hdst, immBytes_eight]
    exact sar_r16_imm8_rex_triple_of_bytes p rex modrm (UInt8.ofBitVec imm) hrex hmod hreg

theorem sar_r64_one_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD1, modrm])
      (sarR64Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, sar_r64_one_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sar_r64_one_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, sarSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply sarFlags_allows

theorem sar_r64_one_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xD1, modrm])
      (Effect.post (sarR64Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => sarR64Effect_avoids p _ _ _ s _)
    (sar_r64_one_effect_step p rex modrm hrex hmod hreg)

theorem sar_r32_one_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xD1, modrm])
      (sarR32Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, sar_r32_one_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sar_r32_one_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, sarSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply sarFlags_allows

theorem sar_r32_one_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    Triple (fun s => s.RIP = p) (codeRange p [0xD1, modrm])
      (Effect.post (sarR32Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => sarR32Effect_avoids p _ _ _ s _)
    (sar_r32_one_effect_step p modrm hmod hreg)

theorem sar_r32_one_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD1, modrm])
      (sarR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, sar_r32_one_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sar_r32_one_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, sarSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply sarFlags_allows

theorem sar_r32_one_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xD1, modrm])
      (Effect.post (sarR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => sarR32Effect_avoids p _ _ _ s _)
    (sar_r32_one_rex_effect_step p rex modrm hrex hmod hreg)

theorem sar_r16_one_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0xD1, modrm])
      (sarR16Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, sar_r16_one_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sar_r16_one_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, sarSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply sarFlags_allows

theorem sar_r16_one_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, 0xD1, modrm])
      (Effect.post (sarR16Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => sarR16Effect_avoids p _ _ _ s _)
    (sar_r16_one_effect_step p modrm hmod hreg)

theorem sar_r16_one_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xD1, modrm])
      (sarR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, sar_r16_one_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sar_r16_one_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, sarSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply sarFlags_allows

theorem sar_r16_one_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xD1, modrm])
      (Effect.post (sarR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => sarR16Effect_avoids p _ _ _ s _)
    (sar_r16_one_rex_effect_step p rex modrm hrex hmod hreg)

theorem sar_r64_one_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSarR64One dst))
      (Effect.post (sarR64Effect p
        3 (dst.setWidth 5)
        (1))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeSarR64One_spec dst
  rw [hbytes, ← hdst]
  exact sar_r64_one_triple_of_bytes p rex modrm hrex hmod hreg

theorem sar_r32_one_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSarR32One dst))
      (Effect.post (sarR32Effect p
        (encodeSarR32One dst).length (dst.setWidth 5)
        (1))) := by
  rcases encodeSarR32One_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact sar_r32_one_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact sar_r32_one_rex_triple_of_bytes p rex modrm hrex hmod hreg

theorem sar_r16_one_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSarR16One dst))
      (Effect.post (sarR16Effect p
        (encodeSarR16One dst).length (dst.setWidth 5)
        (1))) := by
  rcases encodeSarR16One_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact sar_r16_one_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact sar_r16_one_rex_triple_of_bytes p rex modrm hrex hmod hreg

attribute [x86_compose] sarR64Effect sarR32Effect sarR16Effect

@[x86_local] theorem sarR64Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {c : Nat} :
    Effect.Local (sarR64Effect p len dst c) := by
  effect_local [sarR64Effect, sarFlags]

@[x86_local] theorem sarR32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {c : Nat} :
    Effect.Local (sarR32Effect p len dst c) := by
  effect_local [sarR32Effect, sarFlags]

@[x86_local] theorem sarR16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {c : Nat} :
    Effect.Local (sarR16Effect p len dst c) := by
  effect_local [sarR16Effect, sarFlags]

end X86Proofs
