import X86Proofs.Instructions.Sbb.Generated.Rev.Step
import X86Proofs.Instructions.Sbb.Generated.Rev.Encode
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Sbb.Generated.RR.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem sbb_r64_r64_rev_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8) (c : Bool)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [rex, 0x1B, modrm])
      (sbbR64R64Effect p (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, sbb_r64_r64_rev_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), sbb_r64_r64_rev_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, sbbSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sbb_r64_r64_rev_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8) (c : Bool)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [rex, 0x1B, modrm])
      (Effect.post (sbbR64R64Effect p (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) c)) :=
  Triple.of_effect (fun s _ => sbbR64R64Effect_avoids p _ _ _ s _)
    (sbb_r64_r64_rev_effect_step p rex modrm c hrex hmod)

theorem sbb_r32_r32_rev_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (c : Bool)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x1B, modrm])
      (sbbR32R32Effect p 2 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, sbb_r32_r32_rev_step s h modrm hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), sbb_r32_r32_rev_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, sbbSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sbb_r32_r32_rev_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8) (c : Bool)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x1B, modrm])
      (Effect.post (sbbR32R32Effect p 2 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) c)) :=
  Triple.of_effect (fun s _ => sbbR32R32Effect_avoids p _ _ _ _ s _)
    (sbb_r32_r32_rev_effect_step p modrm c hmod)

theorem sbb_r32_r32_rev_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8) (c : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [rex, 0x1B, modrm])
      (sbbR32R32Effect p 3 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, sbb_r32_r32_rev_rex_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), sbb_r32_r32_rev_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, sbbSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sbb_r32_r32_rev_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8) (c : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [rex, 0x1B, modrm])
      (Effect.post (sbbR32R32Effect p 3 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) c)) :=
  Triple.of_effect (fun s _ => sbbR32R32Effect_avoids p _ _ _ _ s _)
    (sbb_r32_r32_rev_rex_effect_step p rex modrm c hrex hmod)

theorem sbb_r16_r16_rev_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (c : Bool)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x66, 0x1B, modrm])
      (sbbR16R16Effect p 3 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, sbb_r16_r16_rev_step s h modrm hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), sbb_r16_r16_rev_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, sbbSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sbb_r16_r16_rev_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8) (c : Bool)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x66, 0x1B, modrm])
      (Effect.post (sbbR16R16Effect p 3 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) c)) :=
  Triple.of_effect (fun s _ => sbbR16R16Effect_avoids p _ _ _ _ s _)
    (sbb_r16_r16_rev_effect_step p modrm c hmod)

theorem sbb_r16_r16_rev_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8) (c : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x66, rex, 0x1B, modrm])
      (sbbR16R16Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, sbb_r16_r16_rev_rex_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), sbb_r16_r16_rev_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, sbbSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sbb_r16_r16_rev_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8) (c : Bool)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p [0x66, rex, 0x1B, modrm])
      (Effect.post (sbbR16R16Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) c)) :=
  Triple.of_effect (fun s _ => sbbR16R16Effect_avoids p _ _ _ _ s _)
    (sbb_r16_r16_rev_rex_effect_step p rex modrm c hrex hmod)

theorem sbb_r64_r64_rev_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeSbbR64R64Rev dst src))
      (Effect.post (sbbR64R64Effect p (dst.setWidth 5) (src.setWidth 5) c)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeSbbR64R64Rev_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact sbb_r64_r64_rev_triple_of_bytes p rex modrm c hrex hmod

theorem sbb_r32_r32_rev_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeSbbR32R32Rev dst src))
      (Effect.post (sbbR32R32Effect p (encodeSbbR32R32Rev dst src).length (dst.setWidth 5)
        (src.setWidth 5) c)) := by
  rcases encodeSbbR32R32Rev_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact sbb_r32_r32_rev_triple_of_bytes p modrm c hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact sbb_r32_r32_rev_rex_triple_of_bytes p rex modrm c hrex hmod

theorem sbb_r16_r16_rev_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeSbbR16R16Rev dst src))
      (Effect.post (sbbR16R16Effect p (encodeSbbR16R16Rev dst src).length (dst.setWidth 5)
        (src.setWidth 5) c)) := by
  rcases encodeSbbR16R16Rev_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact sbb_r16_r16_rev_triple_of_bytes p modrm c hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact sbb_r16_r16_rev_rex_triple_of_bytes p rex modrm c hrex hmod

end X86Proofs
