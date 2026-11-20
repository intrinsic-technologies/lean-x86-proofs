import X86Proofs.Instructions.Rcr.Generated.Cl.Step
import X86Proofs.Instructions.Rcr.Generated.Cl.Encode
import X86Proofs.Instructions.Rcr.Generated.R.Triple
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def rcrR64ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cf : Bool) (s : RamState) : Effect :=
  rcrR64Effect p len dst (shiftCount 64 ((Operand.reg 1 : Operand 8).read s)) cf s

@[simp] theorem rcrR64ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cf : Bool)
    (s : RamState) : (rcrR64ClEffect p len dst cf s).components = [.reg dst, .flags, .rip] := rfl

theorem rcrR64ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cf : Bool) (s : RamState)
    (code : CodeMap) : (rcrR64ClEffect p len dst cf s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def rcrR32ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cf : Bool) (s : RamState) : Effect :=
  rcrR32Effect p len dst (shiftCount 32 ((Operand.reg 1 : Operand 8).read s)) cf s

@[simp] theorem rcrR32ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cf : Bool)
    (s : RamState) : (rcrR32ClEffect p len dst cf s).components = [.reg dst, .flags, .rip] := rfl

theorem rcrR32ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cf : Bool) (s : RamState)
    (code : CodeMap) : (rcrR32ClEffect p len dst cf s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def rcrR16ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cf : Bool) (s : RamState) : Effect :=
  rcrR16Effect p len dst (shiftCount 16 ((Operand.reg 1 : Operand 8).read s)) cf s

@[simp] theorem rcrR16ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cf : Bool)
    (s : RamState) : (rcrR16ClEffect p len dst cf s).components = [.reg dst, .flags, .rip] := rfl

theorem rcrR16ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cf : Bool) (s : RamState)
    (code : CodeMap) : (rcrR16ClEffect p len dst cf s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem rcr_r64_cl_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8) (cf : Bool)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [rex, 0xD3, modrm])
      (rcrR64ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcr_r64_cl_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcr_r64_cl_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, rcrSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rcrFlags_allows

theorem rcr_r64_cl_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8) (cf : Bool)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [rex, 0xD3, modrm])
      (Effect.post (rcrR64ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) cf)) :=
  Triple.of_effect (fun s _ => rcrR64ClEffect_avoids p _ _ _ s _)
    (rcr_r64_cl_effect_step p rex modrm cf hrex hmod hreg)

theorem rcr_r32_cl_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0xD3, modrm])
      (rcrR32ClEffect p 2 (gprNumber 0 0 (modrmRm modrm)) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcr_r32_cl_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcr_r32_cl_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, rcrSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rcrFlags_allows

theorem rcr_r32_cl_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0xD3, modrm])
      (Effect.post (rcrR32ClEffect p 2 (gprNumber 0 0 (modrmRm modrm)) cf)) :=
  Triple.of_effect (fun s _ => rcrR32ClEffect_avoids p _ _ _ s _)
    (rcr_r32_cl_effect_step p modrm cf hmod hreg)

theorem rcr_r32_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8) (cf : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [rex, 0xD3, modrm])
      (rcrR32ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcr_r32_cl_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcr_r32_cl_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, rcrSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rcrFlags_allows

theorem rcr_r32_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8) (cf : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [rex, 0xD3, modrm])
      (Effect.post (rcrR32ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) cf)) :=
  Triple.of_effect (fun s _ => rcrR32ClEffect_avoids p _ _ _ s _)
    (rcr_r32_cl_rex_effect_step p rex modrm cf hrex hmod hreg)

theorem rcr_r16_cl_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0x66, 0xD3, modrm])
      (rcrR16ClEffect p 3 (gprNumber 0 0 (modrmRm modrm)) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcr_r16_cl_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcr_r16_cl_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rcrSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rcrFlags_allows

theorem rcr_r16_cl_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0x66, 0xD3, modrm])
      (Effect.post (rcrR16ClEffect p 3 (gprNumber 0 0 (modrmRm modrm)) cf)) :=
  Triple.of_effect (fun s _ => rcrR16ClEffect_avoids p _ _ _ s _)
    (rcr_r16_cl_effect_step p modrm cf hmod hreg)

theorem rcr_r16_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8) (cf : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0x66, rex, 0xD3, modrm])
      (rcrR16ClEffect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcr_r16_cl_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcr_r16_cl_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rcrSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rcrFlags_allows

theorem rcr_r16_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8) (cf : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0x66, rex, 0xD3, modrm])
      (Effect.post (rcrR16ClEffect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) cf)) :=
  Triple.of_effect (fun s _ => rcrR16ClEffect_avoids p _ _ _ s _)
    (rcr_r16_cl_rex_effect_step p rex modrm cf hrex hmod hreg)

theorem rcr_r64_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (cf : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p (encodeRcrR64Cl dst))
      (Effect.post (rcrR64ClEffect p
        3 (dst.setWidth 5) cf)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeRcrR64Cl_spec dst
  rw [hbytes, ← hdst]
  exact rcr_r64_cl_triple_of_bytes p rex modrm cf hrex hmod hreg

theorem rcr_r32_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (cf : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p (encodeRcrR32Cl dst))
      (Effect.post (rcrR32ClEffect p
        (encodeRcrR32Cl dst).length (dst.setWidth 5) cf)) := by
  rcases encodeRcrR32Cl_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact rcr_r32_cl_triple_of_bytes p modrm cf hmod hreg
  · rw [hbytes, ← hdst]
    exact rcr_r32_cl_rex_triple_of_bytes p rex modrm cf hrex hmod hreg

theorem rcr_r16_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (cf : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p (encodeRcrR16Cl dst))
      (Effect.post (rcrR16ClEffect p
        (encodeRcrR16Cl dst).length (dst.setWidth 5) cf)) := by
  rcases encodeRcrR16Cl_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact rcr_r16_cl_triple_of_bytes p modrm cf hmod hreg
  · rw [hbytes, ← hdst]
    exact rcr_r16_cl_rex_triple_of_bytes p rex modrm cf hrex hmod hreg

attribute [x86_compose] rcrR64ClEffect rcrR32ClEffect rcrR16ClEffect

@[x86_local] theorem rcrR64ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {cf : Bool} :
    Effect.Local (rcrR64ClEffect p len dst cf) :=
  Effect.Local.of_param (e := fun c => rcrR64Effect p len dst c cf)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => rcrR64Effect_local

@[x86_local] theorem rcrR32ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {cf : Bool} :
    Effect.Local (rcrR32ClEffect p len dst cf) :=
  Effect.Local.of_param (e := fun c => rcrR32Effect p len dst c cf)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => rcrR32Effect_local

@[x86_local] theorem rcrR16ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {cf : Bool} :
    Effect.Local (rcrR16ClEffect p len dst cf) :=
  Effect.Local.of_param (e := fun c => rcrR16Effect p len dst c cf)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => rcrR16Effect_local

end X86Proofs
