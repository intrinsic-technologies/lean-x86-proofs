import X86Proofs.Instructions.Rcl.Generated.R8Cl.Step
import X86Proofs.Instructions.Rcl.Generated.R8Cl.Encode
import X86Proofs.Instructions.Rcl.Generated.R8.Triple
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def rclR8ClEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cf : Bool) (s : RamState) : Effect :=
  rclR8Effect p len dst (shiftCount 8 ((Operand.reg 1 : Operand 8).read s)) cf s

@[simp] theorem rclR8ClEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cf : Bool)
    (s : RamState) : (rclR8ClEffect p len dst cf s).components = [.reg dst, .flags, .rip] := rfl

theorem rclR8ClEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cf : Bool) (s : RamState)
    (code : CodeMap) : (rclR8ClEffect p len dst cf s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem rcl_r8_cl_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0xD2, modrm])
      (rclR8ClEffect p 2 (gprNumber 0 0 (modrmRm modrm)) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcl_r8_cl_step s h modrm hmod hreg hrm8 hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcl_r8_cl_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rclFlags_allows

theorem rcl_r8_cl_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [0xD2, modrm])
      (Effect.post (rclR8ClEffect p 2 (gprNumber 0 0 (modrmRm modrm)) cf)) :=
  Triple.of_effect (fun s _ => rclR8ClEffect_avoids p _ _ _ s _)
    (rcl_r8_cl_effect_step p modrm cf hmod hreg hrm8)

theorem rcl_r8_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8) (cf : Bool)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [rex, 0xD2, modrm])
      (rclR8ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, rcl_r8_cl_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), rcl_r8_cl_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, rclSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · apply rclFlags_allows

theorem rcl_r8_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8) (cf : Bool)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p [rex, 0xD2, modrm])
      (Effect.post (rclR8ClEffect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) cf)) :=
  Triple.of_effect (fun s _ => rclR8ClEffect_avoids p _ _ _ s _)
    (rcl_r8_cl_rex_effect_step p rex modrm cf hrex hmod hreg)

theorem rcl_r8_cl_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (cf : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf) (codeRange p (encodeRclR8Cl dst))
      (Effect.post (rclR8ClEffect p
        (encodeRclR8Cl dst).length (dst.setWidth 5) cf)) := by
  rcases encodeRclR8Cl_spec dst with ⟨modrm, hbytes, hmod, hreg, hrm8, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact rcl_r8_cl_triple_of_bytes p modrm cf hmod hreg hrm8
  · rw [hbytes, ← hdst]
    exact rcl_r8_cl_rex_triple_of_bytes p rex modrm cf hrex hmod hreg

def rclR8ClNoRexEffect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (cf : Bool) (s : RamState) :
    Effect :=
  rclR8NoRexEffect p len dst (shiftCount 8 ((Operand.reg 1 : Operand 8).read s)) cf s

@[simp] theorem rclR8ClNoRexEffect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 3) (cf : Bool) (s : RamState) :
    (rclR8ClNoRexEffect p len dst cf s).components = [.reg (byteRegGpr dst), .flags, .rip] :=
  rfl

theorem rclR8ClNoRexEffect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 3) (cf : Bool)
    (s : RamState) (code : CodeMap) : (rclR8ClNoRexEffect p len dst cf s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem rcl_r8_cl_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p [0xD2, modrm])
      (rclR8ClNoRexEffect p 2 (modrmRm modrm) cf) := by
  rintro s h hcode ⟨rfl, rfl⟩
  have hs := rcl_r8_cl_norex_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp))
  have hr := rcl_r8_cl_norex_ready h modrm
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

theorem rcl_r8_cl_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8) (cf : Bool)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p [0xD2, modrm])
      (Effect.post (rclR8ClNoRexEffect p 2 (modrmRm modrm) cf)) :=
  Triple.of_effect (fun s _ => rclR8ClNoRexEffect_avoids p _ _ _ s _)
    (rcl_r8_cl_norex_effect_step p modrm cf hmod hreg)

theorem rcl_r8_cl_norex_triple [Bindings] (p : BitVec 64) (dst : BitVec 3)
    (cf : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (encodeRclR8ClNoRex dst))
      (Effect.post (rclR8ClNoRexEffect p 2 dst cf)) := by
  have h := rcl_r8_cl_norex_triple_of_bytes p (modrmRegs 2 dst) cf
    (modrmMod_modrmRegs _ _) (modrmReg_modrmRegs _ _)
  rwa [modrmRm_modrmRegs] at h

attribute [x86_compose] rclR8ClEffect rclR8ClNoRexEffect

@[x86_local] theorem rclR8ClEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {cf : Bool} :
    Effect.Local (rclR8ClEffect p len dst cf) :=
  Effect.Local.of_param (e := fun c => rclR8Effect p len dst c cf)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => rclR8Effect_local

@[x86_local] theorem rclR8ClNoRexEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {cf : Bool} :
    Effect.Local (rclR8ClNoRexEffect p len dst cf) :=
  Effect.Local.of_param (e := fun c => rclR8NoRexEffect p len dst c cf)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => rclR8NoRexEffect_local

end X86Proofs
