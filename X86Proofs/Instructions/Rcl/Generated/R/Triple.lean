import X86Proofs.Instructions.Rcl.Generated.R.Step
import X86Proofs.Instructions.Rcl.Generated.R.Encode
import X86Proofs.Program.Compose
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def rclR64Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (cf : Bool) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), ((BitVec.cons cf a).rotateLeft c).setWidth 64⟩]
    flags := some (rclFlags (StatusFlags.ofRFLAGS s.RFLAGS) cf c a) }

@[simp] theorem rclR64Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (cf : Bool)
    (s : RamState) : (rclR64Effect p len dst c cf s).components = [.reg dst, .flags, .rip] := rfl

theorem rclR64Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (cf : Bool) (s : RamState)
    (code : CodeMap) : (rclR64Effect p len dst c cf s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def rclR32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (cf : Bool) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (((BitVec.cons cf a).rotateLeft c).setWidth 32).setWidth 64⟩]
    flags := some (rclFlags (StatusFlags.ofRFLAGS s.RFLAGS) cf c a) }

@[simp] theorem rclR32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (cf : Bool)
    (s : RamState) : (rclR32Effect p len dst c cf s).components = [.reg dst, .flags, .rip] := rfl

theorem rclR32Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (cf : Bool) (s : RamState)
    (code : CodeMap) : (rclR32Effect p len dst c cf s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def rclR16Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (cf : Bool) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (((BitVec.cons cf a).rotateLeft c).setWidth 16) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (rclFlags (StatusFlags.ofRFLAGS s.RFLAGS) cf c a) }

@[simp] theorem rclR16Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (cf : Bool)
    (s : RamState) : (rclR16Effect p len dst c cf s).components = [.reg dst, .flags, .rip] := rfl

theorem rclR16Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (cf : Bool) (s : RamState)
    (code : CodeMap) : (rclR16Effect p len dst c cf s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem rcl_r64_imm8_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8) (cf : Bool)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [rex, 0xC1, modrm, imm])
      (rclR64Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 64 imm.toBitVec) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcl_r64_imm8_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcl_r64_imm8_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rclFlags_allows

theorem rcl_r64_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm imm : UInt8) (cf : Bool)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [rex, 0xC1, modrm, imm])
      (Effect.post (rclR64Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 64 imm.toBitVec) cf)) :=
  Triple.of_effect (fun s _ => rclR64Effect_avoids p _ _ _ _ s _)
    (rcl_r64_imm8_effect_step p rex modrm imm cf hrex hmod hreg)

theorem rcl_r32_imm8_effect_step [Bindings] (p : BitVec 64) (modrm imm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0xC1, modrm, imm])
      (rclR32Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 32 imm.toBitVec) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcl_r32_imm8_step s h modrm imm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcl_r32_imm8_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rclFlags_allows

theorem rcl_r32_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm imm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0xC1, modrm, imm])
      (Effect.post (rclR32Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 32 imm.toBitVec) cf)) :=
  Triple.of_effect (fun s _ => rclR32Effect_avoids p _ _ _ _ s _)
    (rcl_r32_imm8_effect_step p modrm imm cf hmod hreg)

theorem rcl_r32_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8) (cf : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [rex, 0xC1, modrm, imm])
      (rclR32Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 32 imm.toBitVec) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcl_r32_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcl_r32_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rclFlags_allows

theorem rcl_r32_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm imm : UInt8) (cf : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [rex, 0xC1, modrm, imm])
      (Effect.post (rclR32Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 32 imm.toBitVec) cf)) :=
  Triple.of_effect (fun s _ => rclR32Effect_avoids p _ _ _ _ s _)
    (rcl_r32_imm8_rex_effect_step p rex modrm imm cf hrex hmod hreg)

theorem rcl_r16_imm8_effect_step [Bindings] (p : BitVec 64) (modrm imm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0x66, 0xC1, modrm, imm])
      (rclR16Effect p 4 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 16 imm.toBitVec) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcl_r16_imm8_step s h modrm imm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcl_r16_imm8_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rclFlags_allows

theorem rcl_r16_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm imm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0x66, 0xC1, modrm, imm])
      (Effect.post (rclR16Effect p 4 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 16 imm.toBitVec) cf)) :=
  Triple.of_effect (fun s _ => rclR16Effect_avoids p _ _ _ _ s _)
    (rcl_r16_imm8_effect_step p modrm imm cf hmod hreg)

theorem rcl_r16_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8) (cf : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0x66, rex, 0xC1, modrm, imm])
      (rclR16Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 16 imm.toBitVec) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcl_r16_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcl_r16_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 5 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 5 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rclFlags_allows

theorem rcl_r16_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm imm : UInt8) (cf : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0x66, rex, 0xC1, modrm, imm])
      (Effect.post (rclR16Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 16 imm.toBitVec) cf)) :=
  Triple.of_effect (fun s _ => rclR16Effect_avoids p _ _ _ _ s _)
    (rcl_r16_imm8_rex_effect_step p rex modrm imm cf hrex hmod hreg)

theorem rcl_r64_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) (cf : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p (encodeRclR64Imm8 dst imm))
      (Effect.post (rclR64Effect p
        4 (dst.setWidth 5)
        (shiftCount 64 imm) cf)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeRclR64Imm8_spec imm dst
  rw [hbytes, ← hdst, immBytes_eight]
  exact rcl_r64_imm8_triple_of_bytes p rex modrm (UInt8.ofBitVec imm) cf hrex hmod hreg

theorem rcl_r32_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) (cf : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p (encodeRclR32Imm8 dst imm))
      (Effect.post (rclR32Effect p
        (encodeRclR32Imm8 dst imm).length (dst.setWidth 5)
        (shiftCount 32 imm) cf)) := by
  rcases encodeRclR32Imm8_spec imm dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst, immBytes_eight]
    exact rcl_r32_imm8_triple_of_bytes p modrm (UInt8.ofBitVec imm) cf hmod hreg
  · rw [hbytes, ← hdst, immBytes_eight]
    exact rcl_r32_imm8_rex_triple_of_bytes p rex modrm (UInt8.ofBitVec imm) cf hrex hmod hreg

theorem rcl_r16_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) (cf : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p (encodeRclR16Imm8 dst imm))
      (Effect.post (rclR16Effect p
        (encodeRclR16Imm8 dst imm).length (dst.setWidth 5)
        (shiftCount 16 imm) cf)) := by
  rcases encodeRclR16Imm8_spec imm dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst, immBytes_eight]
    exact rcl_r16_imm8_triple_of_bytes p modrm (UInt8.ofBitVec imm) cf hmod hreg
  · rw [hbytes, ← hdst, immBytes_eight]
    exact rcl_r16_imm8_rex_triple_of_bytes p rex modrm (UInt8.ofBitVec imm) cf hrex hmod hreg

theorem rcl_r64_one_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8) (cf : Bool)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [rex, 0xD1, modrm])
      (rclR64Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcl_r64_one_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcl_r64_one_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rclFlags_allows

theorem rcl_r64_one_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8) (cf : Bool)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [rex, 0xD1, modrm])
      (Effect.post (rclR64Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1) cf)) :=
  Triple.of_effect (fun s _ => rclR64Effect_avoids p _ _ _ _ s _)
    (rcl_r64_one_effect_step p rex modrm cf hrex hmod hreg)

theorem rcl_r32_one_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0xD1, modrm])
      (rclR32Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (1) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcl_r32_one_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcl_r32_one_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rclFlags_allows

theorem rcl_r32_one_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0xD1, modrm])
      (Effect.post (rclR32Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (1) cf)) :=
  Triple.of_effect (fun s _ => rclR32Effect_avoids p _ _ _ _ s _)
    (rcl_r32_one_effect_step p modrm cf hmod hreg)

theorem rcl_r32_one_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8) (cf : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [rex, 0xD1, modrm])
      (rclR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcl_r32_one_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcl_r32_one_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rclFlags_allows

theorem rcl_r32_one_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8) (cf : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [rex, 0xD1, modrm])
      (Effect.post (rclR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1) cf)) :=
  Triple.of_effect (fun s _ => rclR32Effect_avoids p _ _ _ _ s _)
    (rcl_r32_one_rex_effect_step p rex modrm cf hrex hmod hreg)

theorem rcl_r16_one_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0x66, 0xD1, modrm])
      (rclR16Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (1) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcl_r16_one_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcl_r16_one_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rclFlags_allows

theorem rcl_r16_one_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0x66, 0xD1, modrm])
      (Effect.post (rclR16Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (1) cf)) :=
  Triple.of_effect (fun s _ => rclR16Effect_avoids p _ _ _ _ s _)
    (rcl_r16_one_effect_step p modrm cf hmod hreg)

theorem rcl_r16_one_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8) (cf : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0x66, rex, 0xD1, modrm])
      (rclR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcl_r16_one_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcl_r16_one_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rclFlags_allows

theorem rcl_r16_one_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8) (cf : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0x66, rex, 0xD1, modrm])
      (Effect.post (rclR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1) cf)) :=
  Triple.of_effect (fun s _ => rclR16Effect_avoids p _ _ _ _ s _)
    (rcl_r16_one_rex_effect_step p rex modrm cf hrex hmod hreg)

theorem rcl_r64_one_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (cf : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p (encodeRclR64One dst))
      (Effect.post (rclR64Effect p
        3 (dst.setWidth 5)
        (1) cf)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeRclR64One_spec dst
  rw [hbytes, ← hdst]
  exact rcl_r64_one_triple_of_bytes p rex modrm cf hrex hmod hreg

theorem rcl_r32_one_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (cf : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p (encodeRclR32One dst))
      (Effect.post (rclR32Effect p
        (encodeRclR32One dst).length (dst.setWidth 5)
        (1) cf)) := by
  rcases encodeRclR32One_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact rcl_r32_one_triple_of_bytes p modrm cf hmod hreg
  · rw [hbytes, ← hdst]
    exact rcl_r32_one_rex_triple_of_bytes p rex modrm cf hrex hmod hreg

theorem rcl_r16_one_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (cf : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p (encodeRclR16One dst))
      (Effect.post (rclR16Effect p
        (encodeRclR16One dst).length (dst.setWidth 5)
        (1) cf)) := by
  rcases encodeRclR16One_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact rcl_r16_one_triple_of_bytes p modrm cf hmod hreg
  · rw [hbytes, ← hdst]
    exact rcl_r16_one_rex_triple_of_bytes p rex modrm cf hrex hmod hreg

attribute [x86_compose] rclR64Effect rclR32Effect rclR16Effect

@[x86_local] theorem rclR64Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {c : Nat} {cf : Bool} :
    Effect.Local (rclR64Effect p len dst c cf) := by
  effect_local [rclR64Effect, rclFlags]

@[x86_local] theorem rclR32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {c : Nat} {cf : Bool} :
    Effect.Local (rclR32Effect p len dst c cf) := by
  effect_local [rclR32Effect, rclFlags]

@[x86_local] theorem rclR16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {c : Nat} {cf : Bool} :
    Effect.Local (rclR16Effect p len dst c cf) := by
  effect_local [rclR16Effect, rclFlags]

end X86Proofs
