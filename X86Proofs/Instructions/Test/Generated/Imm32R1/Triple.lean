import X86Proofs.Instructions.Test.Generated.Imm32R1.Step
import X86Proofs.Instructions.Test.Generated.Imm32R1.Encode
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Test.Generated.Imm32.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem test_r1_r64_imm32_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 32) (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0xF7 :: modrm :: immBytes 32 imm))
      (testR64Imm32Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, test_r1_r64_imm32_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), test_r1_r64_imm32_ready h rex modrm imm,
    ⟨afterStep_writeFlagsOutputs_rip h 7 _ 1 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 7 _ 1 _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_r64_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 32) (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0xF7 :: modrm :: immBytes 32 imm))
      (Effect.post (testR64Imm32Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => testR64Imm32Effect_avoids p _ _ s _)
    (test_r1_r64_imm32_effect_step p rex modrm imm hrex hmod hreg)

theorem test_r1_r64_imm32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeTestR1R64Imm32 dst imm))
      (Effect.post (testR64Imm32Effect p (dst.setWidth 5) imm)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeTestR1R64Imm32_spec dst imm
  rw [hbytes, ← hdst]
  exact test_r1_r64_imm32_triple_of_bytes p rex modrm imm hrex hmod hreg

theorem test_r1_r32_imm32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 32) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0xF7 :: modrm :: immBytes 32 imm))
      (testR32Imm32Effect p 6 (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, test_r1_r32_imm32_step s h modrm imm hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), test_r1_r32_imm32_ready h modrm imm,
    ⟨afterStep_writeFlagsOutputs_rip h 6 _ 1 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 6 _ 1 _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_r32_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 32) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p (0xF7 :: modrm :: immBytes 32 imm))
      (Effect.post (testR32Imm32Effect p 6 (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => testR32Imm32Effect_avoids p _ _ _ s _)
    (test_r1_r32_imm32_effect_step p modrm imm hmod hreg)

theorem test_r1_r32_imm32_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 32) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0xF7 :: modrm :: immBytes 32 imm))
      (testR32Imm32Effect p 7 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, test_r1_r32_imm32_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), test_r1_r32_imm32_rex_ready h rex modrm imm,
    ⟨afterStep_writeFlagsOutputs_rip h 7 _ 1 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 7 _ 1 _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_r32_imm32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 32) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0xF7 :: modrm :: immBytes 32 imm))
      (Effect.post (testR32Imm32Effect p 7 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => testR32Imm32Effect_avoids p _ _ _ s _)
    (test_r1_r32_imm32_rex_effect_step p rex modrm imm hrex hmod hreg)

theorem test_r1_r32_imm32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeTestR1R32Imm32 dst imm))
      (Effect.post (testR32Imm32Effect p (encodeTestR1R32Imm32 dst imm).length (dst.setWidth 5) imm)) := by
  rcases encodeTestR1R32Imm32_spec dst imm with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    simpa using test_r1_r32_imm32_triple_of_bytes p modrm imm hmod hreg
  · rw [hbytes, ← hdst]
    simpa using test_r1_r32_imm32_rex_triple_of_bytes p rex modrm imm hrex hmod hreg

theorem test_r1_r16_imm16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 16) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x66 :: 0xF7 :: modrm :: immBytes 16 imm))
      (testR16Imm16Effect p 5 (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, test_r1_r16_imm16_step s h modrm imm hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), test_r1_r16_imm16_ready h modrm imm,
    ⟨afterStep_writeFlagsOutputs_rip h 5 _ 1 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 5 _ 1 _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_r16_imm16_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 16) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p (0x66 :: 0xF7 :: modrm :: immBytes 16 imm))
      (Effect.post (testR16Imm16Effect p 5 (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => testR16Imm16Effect_avoids p _ _ _ s _)
    (test_r1_r16_imm16_effect_step p modrm imm hmod hreg)

theorem test_r1_r16_imm16_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 16) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x66 :: rex :: 0xF7 :: modrm :: immBytes 16 imm))
      (testR16Imm16Effect p 6 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, test_r1_r16_imm16_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), test_r1_r16_imm16_rex_ready h rex modrm imm,
    ⟨afterStep_writeFlagsOutputs_rip h 6 _ 1 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 6 _ 1 _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_r16_imm16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 16) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p (0x66 :: rex :: 0xF7 :: modrm :: immBytes 16 imm))
      (Effect.post (testR16Imm16Effect p 6 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => testR16Imm16Effect_avoids p _ _ _ s _)
    (test_r1_r16_imm16_rex_effect_step p rex modrm imm hrex hmod hreg)

theorem test_r1_r16_imm16_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 16) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeTestR1R16Imm16 dst imm))
      (Effect.post (testR16Imm16Effect p (encodeTestR1R16Imm16 dst imm).length (dst.setWidth 5) imm)) := by
  rcases encodeTestR1R16Imm16_spec dst imm with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    simpa using test_r1_r16_imm16_triple_of_bytes p modrm imm hmod hreg
  · rw [hbytes, ← hdst]
    simpa using test_r1_r16_imm16_rex_triple_of_bytes p rex modrm imm hrex hmod hreg

end X86Proofs
