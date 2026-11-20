import X86Proofs.Instructions.Rcl.Generated.R8.Step
import X86Proofs.Instructions.Rcl.Generated.R8.Encode
import X86Proofs.Program.Compose
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def rclR8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (cf : Bool) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (((BitVec.cons cf a).rotateLeft c).setWidth 8) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (rclFlags (StatusFlags.ofRFLAGS s.RFLAGS) cf c a) }

@[simp] theorem rclR8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (cf : Bool)
    (s : RamState) : (rclR8Effect p len dst c cf s).components = [.reg dst, .flags, .rip] := rfl

theorem rclR8Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (cf : Bool) (s : RamState)
    (code : CodeMap) : (rclR8Effect p len dst c cf s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem rcl_r8_imm8_effect_step [Bindings] (p : BitVec 64) (modrm imm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0xC0, modrm, imm])
      (rclR8Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 8 imm.toBitVec) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcl_r8_imm8_step s h modrm imm hmod hreg hrm8 hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcl_r8_imm8_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rclFlags_allows

theorem rcl_r8_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm imm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0xC0, modrm, imm])
      (Effect.post (rclR8Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (shiftCount 8 imm.toBitVec) cf)) :=
  Triple.of_effect (fun s _ => rclR8Effect_avoids p _ _ _ _ s _)
    (rcl_r8_imm8_effect_step p modrm imm cf hmod hreg hrm8)

theorem rcl_r8_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8) (cf : Bool)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [rex, 0xC0, modrm, imm])
      (rclR8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 8 imm.toBitVec) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcl_r8_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcl_r8_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rclFlags_allows

theorem rcl_r8_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm imm : UInt8) (cf : Bool)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [rex, 0xC0, modrm, imm])
      (Effect.post (rclR8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 8 imm.toBitVec) cf)) :=
  Triple.of_effect (fun s _ => rclR8Effect_avoids p _ _ _ _ s _)
    (rcl_r8_imm8_rex_effect_step p rex modrm imm cf hrex hmod hreg)

theorem rcl_r8_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) (cf : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p (encodeRclR8Imm8 dst imm))
      (Effect.post (rclR8Effect p
        (encodeRclR8Imm8 dst imm).length (dst.setWidth 5)
        (shiftCount 8 imm) cf)) := by
  rcases encodeRclR8Imm8_spec imm dst with ⟨modrm, hbytes, hmod, hreg, hrm8, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst, immBytes_eight]
    exact rcl_r8_imm8_triple_of_bytes p modrm (UInt8.ofBitVec imm) cf hmod hreg hrm8
  · rw [hbytes, ← hdst, immBytes_eight]
    exact rcl_r8_imm8_rex_triple_of_bytes p rex modrm (UInt8.ofBitVec imm) cf hrex hmod hreg

theorem rcl_r8_one_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0xD0, modrm])
      (rclR8Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (1) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcl_r8_one_step s h modrm hmod hreg hrm8 hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcl_r8_one_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rclFlags_allows

theorem rcl_r8_one_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0xD0, modrm])
      (Effect.post (rclR8Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (1) cf)) :=
  Triple.of_effect (fun s _ => rclR8Effect_avoids p _ _ _ _ s _)
    (rcl_r8_one_effect_step p modrm cf hmod hreg hrm8)

theorem rcl_r8_one_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8) (cf : Bool)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [rex, 0xD0, modrm])
      (rclR8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcl_r8_one_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcl_r8_one_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rclFlags_allows

theorem rcl_r8_one_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8) (cf : Bool)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [rex, 0xD0, modrm])
      (Effect.post (rclR8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1) cf)) :=
  Triple.of_effect (fun s _ => rclR8Effect_avoids p _ _ _ _ s _)
    (rcl_r8_one_rex_effect_step p rex modrm cf hrex hmod hreg)

theorem rcl_r8_one_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (cf : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p (encodeRclR8One dst))
      (Effect.post (rclR8Effect p
        (encodeRclR8One dst).length (dst.setWidth 5)
        (1) cf)) := by
  rcases encodeRclR8One_spec dst with ⟨modrm, hbytes, hmod, hreg, hrm8, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact rcl_r8_one_triple_of_bytes p modrm cf hmod hreg hrm8
  · rw [hbytes, ← hdst]
    exact rcl_r8_one_rex_triple_of_bytes p rex modrm cf hrex hmod hreg

def rclR8NoRexEffect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (c : Nat) (cf : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.byteReg dst).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (byteRegGpr dst) : Operand 64),
      mergeByteReg dst (((BitVec.cons cf a).rotateLeft c).setWidth 8)
        ((Operand.reg (byteRegGpr dst) : Operand 64).read s)⟩]
    flags := some (rclFlags (StatusFlags.ofRFLAGS s.RFLAGS) cf c a) }

@[simp] theorem rclR8NoRexEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (c : Nat) (cf : Bool) (s : RamState) :
    (rclR8NoRexEffect p len dst c cf s).components = [.reg (byteRegGpr dst), .flags, .rip] :=
  rfl

theorem rclR8NoRexEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 3) (c : Nat) (cf : Bool)
    (s : RamState) (code : CodeMap) : (rclR8NoRexEffect p len dst c cf s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem rcl_r8_imm8_norex_effect_step [Bindings] (p : BitVec 64) (modrm imm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p [0xC0, modrm, imm])
      (rclR8NoRexEffect p 3 (modrmRm modrm) (shiftCount 8 imm.toBitVec) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  have hs := rcl_r8_imm8_norex_step s h modrm imm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp))
  have hr := rcl_r8_imm8_norex_ready h modrm imm
  simp only [writeOutputs_byteReg] at hs hr
  refine ⟨_, hs, hr,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_RFLAGS,
      beforeFetch_RFLAGS]
    apply rclFlags_allows

theorem rcl_r8_imm8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm imm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p [0xC0, modrm, imm])
      (Effect.post (rclR8NoRexEffect p 3 (modrmRm modrm) (shiftCount 8 imm.toBitVec) cf)) :=
  Triple.of_effect (fun s _ => rclR8NoRexEffect_avoids p _ _ _ _ s _)
    (rcl_r8_imm8_norex_effect_step p modrm imm cf hmod hreg)

theorem rcl_r8_imm8_norex_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (imm : BitVec 8)
    (cf : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (encodeRclR8Imm8NoRex dst imm))
      (Effect.post (rclR8NoRexEffect p 3 dst (shiftCount 8 imm) cf)) := by
  unfold encodeRclR8Imm8NoRex
  rw [immBytes_eight]
  have h := rcl_r8_imm8_norex_triple_of_bytes p (modrmRegs 2 dst) (UInt8.ofBitVec imm) cf
    (modrmMod_modrmRegs _ _) (modrmReg_modrmRegs _ _)
  rwa [modrmRm_modrmRegs] at h

theorem rcl_r8_one_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p [0xD0, modrm])
      (rclR8NoRexEffect p 2 (modrmRm modrm) (1) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  have hs := rcl_r8_one_norex_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp))
  have hr := rcl_r8_one_norex_ready h modrm
  simp only [writeOutputs_byteReg] at hs hr
  refine ⟨_, hs, hr,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_RFLAGS,
      beforeFetch_RFLAGS]
    apply rclFlags_allows

theorem rcl_r8_one_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p [0xD0, modrm])
      (Effect.post (rclR8NoRexEffect p 2 (modrmRm modrm) (1) cf)) :=
  Triple.of_effect (fun s _ => rclR8NoRexEffect_avoids p _ _ _ _ s _)
    (rcl_r8_one_norex_effect_step p modrm cf hmod hreg)

theorem rcl_r8_one_norex_triple [Bindings] (p : BitVec 64) (dst : BitVec 3)
    (cf : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (encodeRclR8OneNoRex dst))
      (Effect.post (rclR8NoRexEffect p 2 dst (1) cf)) := by
  have h := rcl_r8_one_norex_triple_of_bytes p (modrmRegs 2 dst) cf
    (modrmMod_modrmRegs _ _) (modrmReg_modrmRegs _ _)
  rwa [modrmRm_modrmRegs] at h

attribute [x86_compose] rclR8Effect rclR8NoRexEffect

@[x86_local] theorem rclR8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {c : Nat} {cf : Bool} :
    Effect.Local (rclR8Effect p len dst c cf) := by
  effect_local [rclR8Effect, rclFlags]

@[x86_local] theorem rclR8NoRexEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3} {c : Nat}
    {cf : Bool} :
    Effect.Local (rclR8NoRexEffect p len dst c cf) := by
  effect_local [rclR8NoRexEffect, rclFlags]

end X86Proofs
