import X86Proofs.Instructions.Sal.Generated.R.Step
import X86Proofs.Instructions.Sal.Generated.R.Encode
import X86Proofs.Program.Compose
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def salR64Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), a <<< c⟩]
    flags := some (shlFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[simp] theorem salR64Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat)
    (s : RamState) : (salR64Effect p len dst c s).components = [.reg dst, .flags, .rip] := rfl

theorem salR64Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState)
    (code : CodeMap) : (salR64Effect p len dst c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def salR32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (a <<< c).setWidth 64⟩]
    flags := some (shlFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[simp] theorem salR32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat)
    (s : RamState) : (salR32Effect p len dst c s).components = [.reg dst, .flags, .rip] := rfl

theorem salR32Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState)
    (code : CodeMap) : (salR32Effect p len dst c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def salR16Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (a <<< c) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (shlFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[simp] theorem salR16Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat)
    (s : RamState) : (salR16Effect p len dst c s).components = [.reg dst, .flags, .rip] := rfl

theorem salR16Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState)
    (code : CodeMap) : (salR16Effect p len dst c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem sal_r64_imm8_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (salR64Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 64 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, sal_r64_imm8_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sal_r64_imm8_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem sal_r64_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (Effect.post (salR64Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 64 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => salR64Effect_avoids p _ _ _ s _)
    (sal_r64_imm8_effect_step p rex modrm imm hrex hmod hreg)

theorem sal_r32_imm8_effect_step [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xC1, modrm, imm])
      (salR32Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 32 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, sal_r32_imm8_step s h modrm imm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sal_r32_imm8_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem sal_r32_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    Triple (fun s => s.RIP = p) (codeRange p [0xC1, modrm, imm])
      (Effect.post (salR32Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 32 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => salR32Effect_avoids p _ _ _ s _)
    (sal_r32_imm8_effect_step p modrm imm hmod hreg)

theorem sal_r32_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (salR32Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 32 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, sal_r32_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sal_r32_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem sal_r32_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (Effect.post (salR32Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 32 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => salR32Effect_avoids p _ _ _ s _)
    (sal_r32_imm8_rex_effect_step p rex modrm imm hrex hmod hreg)

theorem sal_r16_imm8_effect_step [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0xC1, modrm, imm])
      (salR16Effect p 4 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 16 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, sal_r16_imm8_step s h modrm imm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sal_r16_imm8_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem sal_r16_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, 0xC1, modrm, imm])
      (Effect.post (salR16Effect p 4 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 16 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => salR16Effect_avoids p _ _ _ s _)
    (sal_r16_imm8_effect_step p modrm imm hmod hreg)

theorem sal_r16_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xC1, modrm, imm])
      (salR16Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 16 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, sal_r16_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sal_r16_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 5 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 5 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem sal_r16_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xC1, modrm, imm])
      (Effect.post (salR16Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 16 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => salR16Effect_avoids p _ _ _ s _)
    (sal_r16_imm8_rex_effect_step p rex modrm imm hrex hmod hreg)

theorem sal_r64_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSalR64Imm8 dst imm))
      (Effect.post (salR64Effect p
        4 (dst.setWidth 5)
        (shiftCount 64 imm))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeSalR64Imm8_spec imm dst
  rw [hbytes, ← hdst, immBytes_eight]
  exact sal_r64_imm8_triple_of_bytes p rex modrm (UInt8.ofBitVec imm) hrex hmod hreg

theorem sal_r32_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSalR32Imm8 dst imm))
      (Effect.post (salR32Effect p
        (encodeSalR32Imm8 dst imm).length (dst.setWidth 5)
        (shiftCount 32 imm))) := by
  rcases encodeSalR32Imm8_spec imm dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst, immBytes_eight]
    exact sal_r32_imm8_triple_of_bytes p modrm (UInt8.ofBitVec imm) hmod hreg
  · rw [hbytes, ← hdst, immBytes_eight]
    exact sal_r32_imm8_rex_triple_of_bytes p rex modrm (UInt8.ofBitVec imm) hrex hmod hreg

theorem sal_r16_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSalR16Imm8 dst imm))
      (Effect.post (salR16Effect p
        (encodeSalR16Imm8 dst imm).length (dst.setWidth 5)
        (shiftCount 16 imm))) := by
  rcases encodeSalR16Imm8_spec imm dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst, immBytes_eight]
    exact sal_r16_imm8_triple_of_bytes p modrm (UInt8.ofBitVec imm) hmod hreg
  · rw [hbytes, ← hdst, immBytes_eight]
    exact sal_r16_imm8_rex_triple_of_bytes p rex modrm (UInt8.ofBitVec imm) hrex hmod hreg

theorem sal_r64_one_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD1, modrm])
      (salR64Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, sal_r64_one_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sal_r64_one_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem sal_r64_one_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xD1, modrm])
      (Effect.post (salR64Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => salR64Effect_avoids p _ _ _ s _)
    (sal_r64_one_effect_step p rex modrm hrex hmod hreg)

theorem sal_r32_one_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xD1, modrm])
      (salR32Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, sal_r32_one_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sal_r32_one_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem sal_r32_one_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    Triple (fun s => s.RIP = p) (codeRange p [0xD1, modrm])
      (Effect.post (salR32Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => salR32Effect_avoids p _ _ _ s _)
    (sal_r32_one_effect_step p modrm hmod hreg)

theorem sal_r32_one_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD1, modrm])
      (salR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, sal_r32_one_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sal_r32_one_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem sal_r32_one_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xD1, modrm])
      (Effect.post (salR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => salR32Effect_avoids p _ _ _ s _)
    (sal_r32_one_rex_effect_step p rex modrm hrex hmod hreg)

theorem sal_r16_one_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0xD1, modrm])
      (salR16Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, sal_r16_one_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sal_r16_one_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem sal_r16_one_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, 0xD1, modrm])
      (Effect.post (salR16Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => salR16Effect_avoids p _ _ _ s _)
    (sal_r16_one_effect_step p modrm hmod hreg)

theorem sal_r16_one_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xD1, modrm])
      (salR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, sal_r16_one_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sal_r16_one_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem sal_r16_one_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, rex, 0xD1, modrm])
      (Effect.post (salR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1))) :=
  Triple.of_effect (fun s _ => salR16Effect_avoids p _ _ _ s _)
    (sal_r16_one_rex_effect_step p rex modrm hrex hmod hreg)

theorem sal_r64_one_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSalR64One dst))
      (Effect.post (salR64Effect p
        3 (dst.setWidth 5)
        (1))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeSalR64One_spec dst
  rw [hbytes, ← hdst]
  exact sal_r64_one_triple_of_bytes p rex modrm hrex hmod hreg

theorem sal_r32_one_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSalR32One dst))
      (Effect.post (salR32Effect p
        (encodeSalR32One dst).length (dst.setWidth 5)
        (1))) := by
  rcases encodeSalR32One_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact sal_r32_one_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact sal_r32_one_rex_triple_of_bytes p rex modrm hrex hmod hreg

theorem sal_r16_one_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSalR16One dst))
      (Effect.post (salR16Effect p
        (encodeSalR16One dst).length (dst.setWidth 5)
        (1))) := by
  rcases encodeSalR16One_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact sal_r16_one_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact sal_r16_one_rex_triple_of_bytes p rex modrm hrex hmod hreg

attribute [x86_compose] salR64Effect salR32Effect salR16Effect

@[x86_local] theorem salR64Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {c : Nat} :
    Effect.Local (salR64Effect p len dst c) := by
  effect_local [salR64Effect, shlFlags]

@[x86_local] theorem salR32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {c : Nat} :
    Effect.Local (salR32Effect p len dst c) := by
  effect_local [salR32Effect, shlFlags]

@[x86_local] theorem salR16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {c : Nat} :
    Effect.Local (salR16Effect p len dst c) := by
  effect_local [salR16Effect, shlFlags]

end X86Proofs
