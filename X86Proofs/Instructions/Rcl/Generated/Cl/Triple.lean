import X86Proofs.Instructions.Rcl.Generated.Cl.Step
import X86Proofs.Instructions.Rcl.Generated.Cl.Encode
import X86Proofs.Instructions.Rcl.Generated.R.Triple
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def rclR64ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cf : Bool) (s : RamState) : Effect :=
  rclR64Effect p len dst (shiftCount 64 ((Operand.reg 1 : Operand 8).read s)) cf s

@[simp] theorem rclR64ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cf : Bool)
    (s : RamState) : (rclR64ClEffect p len dst cf s).components = [.reg dst, .flags, .rip] := rfl

theorem rclR64ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cf : Bool) (s : RamState)
    (code : CodeMap) : (rclR64ClEffect p len dst cf s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def rclR32ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cf : Bool) (s : RamState) : Effect :=
  rclR32Effect p len dst (shiftCount 32 ((Operand.reg 1 : Operand 8).read s)) cf s

@[simp] theorem rclR32ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cf : Bool)
    (s : RamState) : (rclR32ClEffect p len dst cf s).components = [.reg dst, .flags, .rip] := rfl

theorem rclR32ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cf : Bool) (s : RamState)
    (code : CodeMap) : (rclR32ClEffect p len dst cf s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def rclR16ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cf : Bool) (s : RamState) : Effect :=
  rclR16Effect p len dst (shiftCount 16 ((Operand.reg 1 : Operand 8).read s)) cf s

@[simp] theorem rclR16ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cf : Bool)
    (s : RamState) : (rclR16ClEffect p len dst cf s).components = [.reg dst, .flags, .rip] := rfl

theorem rclR16ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cf : Bool) (s : RamState)
    (code : CodeMap) : (rclR16ClEffect p len dst cf s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem rcl_r64_cl_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8) (cf : Bool)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [rex, 0xD3, modrm])
      (rclR64ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcl_r64_cl_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcl_r64_cl_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rclFlags_allows

theorem rcl_r64_cl_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8) (cf : Bool)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [rex, 0xD3, modrm])
      (Effect.post (rclR64ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) cf)) :=
  Triple.of_effect (fun s _ => rclR64ClEffect_avoids p _ _ _ s _)
    (rcl_r64_cl_effect_step p rex modrm cf hrex hmod hreg)

theorem rcl_r32_cl_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0xD3, modrm])
      (rclR32ClEffect p 2 (gprNumber 0 0 (modrmRm modrm)) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcl_r32_cl_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcl_r32_cl_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rclFlags_allows

theorem rcl_r32_cl_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0xD3, modrm])
      (Effect.post (rclR32ClEffect p 2 (gprNumber 0 0 (modrmRm modrm)) cf)) :=
  Triple.of_effect (fun s _ => rclR32ClEffect_avoids p _ _ _ s _)
    (rcl_r32_cl_effect_step p modrm cf hmod hreg)

theorem rcl_r32_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8) (cf : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [rex, 0xD3, modrm])
      (rclR32ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcl_r32_cl_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcl_r32_cl_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rclFlags_allows

theorem rcl_r32_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8) (cf : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [rex, 0xD3, modrm])
      (Effect.post (rclR32ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) cf)) :=
  Triple.of_effect (fun s _ => rclR32ClEffect_avoids p _ _ _ s _)
    (rcl_r32_cl_rex_effect_step p rex modrm cf hrex hmod hreg)

theorem rcl_r16_cl_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0x66, 0xD3, modrm])
      (rclR16ClEffect p 3 (gprNumber 0 0 (modrmRm modrm)) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcl_r16_cl_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcl_r16_cl_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rclFlags_allows

theorem rcl_r16_cl_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0x66, 0xD3, modrm])
      (Effect.post (rclR16ClEffect p 3 (gprNumber 0 0 (modrmRm modrm)) cf)) :=
  Triple.of_effect (fun s _ => rclR16ClEffect_avoids p _ _ _ s _)
    (rcl_r16_cl_effect_step p modrm cf hmod hreg)

theorem rcl_r16_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8) (cf : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0x66, rex, 0xD3, modrm])
      (rclR16ClEffect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcl_r16_cl_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcl_r16_cl_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rclFlags_allows

theorem rcl_r16_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8) (cf : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0x66, rex, 0xD3, modrm])
      (Effect.post (rclR16ClEffect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) cf)) :=
  Triple.of_effect (fun s _ => rclR16ClEffect_avoids p _ _ _ s _)
    (rcl_r16_cl_rex_effect_step p rex modrm cf hrex hmod hreg)

theorem rcl_r64_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (cf : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p (encodeRclR64Cl dst))
      (Effect.post (rclR64ClEffect p
        3 (dst.setWidth 5) cf)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeRclR64Cl_spec dst
  rw [hbytes, ← hdst]
  exact rcl_r64_cl_triple_of_bytes p rex modrm cf hrex hmod hreg

theorem rcl_r32_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (cf : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p (encodeRclR32Cl dst))
      (Effect.post (rclR32ClEffect p
        (encodeRclR32Cl dst).length (dst.setWidth 5) cf)) := by
  rcases encodeRclR32Cl_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact rcl_r32_cl_triple_of_bytes p modrm cf hmod hreg
  · rw [hbytes, ← hdst]
    exact rcl_r32_cl_rex_triple_of_bytes p rex modrm cf hrex hmod hreg

theorem rcl_r16_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (cf : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p (encodeRclR16Cl dst))
      (Effect.post (rclR16ClEffect p
        (encodeRclR16Cl dst).length (dst.setWidth 5) cf)) := by
  rcases encodeRclR16Cl_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact rcl_r16_cl_triple_of_bytes p modrm cf hmod hreg
  · rw [hbytes, ← hdst]
    exact rcl_r16_cl_rex_triple_of_bytes p rex modrm cf hrex hmod hreg

attribute [x86_compose] rclR64ClEffect rclR32ClEffect rclR16ClEffect

@[x86_local] theorem rclR64ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {cf : Bool} :
    Effect.Local (rclR64ClEffect p len dst cf) :=
  Effect.Local.of_param (e := fun c => rclR64Effect p len dst c cf)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => rclR64Effect_local

@[x86_local] theorem rclR32ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {cf : Bool} :
    Effect.Local (rclR32ClEffect p len dst cf) :=
  Effect.Local.of_param (e := fun c => rclR32Effect p len dst c cf)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => rclR32Effect_local

@[x86_local] theorem rclR16ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {cf : Bool} :
    Effect.Local (rclR16ClEffect p len dst cf) :=
  Effect.Local.of_param (e := fun c => rclR16Effect p len dst c cf)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => rclR16Effect_local

end X86Proofs
