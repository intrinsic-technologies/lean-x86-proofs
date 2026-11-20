import X86Proofs.Instructions.Test.Generated.R8Imm8R1.Step
import X86Proofs.Instructions.Test.Generated.R8Imm8R1.Encode
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Test.Generated.R8Imm8.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem test_r1_r8_imm8_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0xF6 :: modrm :: immBytes 8 imm))
      (testR8Imm8Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, test_r1_r8_imm8_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), test_r1_r8_imm8_ready h rex modrm imm,
    ⟨afterStep_writeFlagsOutputs_rip h 4 _ 1 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 4 _ 1 _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_r8_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0xF6 :: modrm :: immBytes 8 imm))
      (Effect.post (testR8Imm8Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => testR8Imm8Effect_avoids p _ _ s _)
    (test_r1_r8_imm8_effect_step p rex modrm imm hrex hmod hreg)

theorem test_r1_r8_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeTestR1R8Imm8 dst imm))
      (Effect.post (testR8Imm8Effect p (dst.setWidth 5) imm)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeTestR1R8Imm8_spec dst imm
  rw [hbytes, ← hdst]
  exact test_r1_r8_imm8_triple_of_bytes p rex modrm imm hrex hmod hreg

theorem test_r1_r8_imm8_low_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 1) (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0xF6 :: modrm :: immBytes 8 imm))
      (testR8Imm8LowEffect p (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, test_r1_r8_imm8_low_step s h modrm imm hmod hreg hrm8 hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), test_r1_r8_imm8_low_ready h modrm imm,
    ⟨afterStep_writeFlagsOutputs_rip h 3 _ 1 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 3 _ 1 _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_r8_imm8_low_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 1) (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p) (codeRange p (0xF6 :: modrm :: immBytes 8 imm))
      (Effect.post (testR8Imm8LowEffect p (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => testR8Imm8LowEffect_avoids p _ _ s _)
    (test_r1_r8_imm8_low_effect_step p modrm imm hmod hreg hrm8)

theorem test_r1_r8_imm8_low_triple [Bindings] (p : BitVec 64) (dst : BitVec 2) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeTestR1R8Imm8Low dst imm))
      (Effect.post (testR8Imm8LowEffect p (dst.setWidth 5) imm)) := by
  obtain ⟨modrm, hbytes, hmod, hreg, hrm8, hdst⟩ := encodeTestR1R8Imm8Low_spec dst imm
  rw [hbytes, ← hdst]
  exact test_r1_r8_imm8_low_triple_of_bytes p modrm imm hmod hreg hrm8

theorem test_r1_r8_imm8_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0xF6 :: modrm :: immBytes 8 imm))
      (testR8Imm8NoRexEffect p 3 (modrmRm modrm) imm) := by
  rintro s h hcode rfl
  have hs := test_r1_r8_imm8_norex_step s h modrm imm hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp))
  have hr := test_r1_r8_imm8_norex_ready h modrm imm
  refine ⟨_, hs, hr,
    ⟨afterStep_writeFlagsOutputs_rip h 3 _ 1 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 3 _ 1 _⟩⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_r8_imm8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    Triple (fun s => s.RIP = p) (codeRange p (0xF6 :: modrm :: immBytes 8 imm))
      (Effect.post (testR8Imm8NoRexEffect p 3 (modrmRm modrm) imm)) :=
  Triple.of_effect (fun s _ => testR8Imm8NoRexEffect_avoids p _ _ _ s _)
    (test_r1_r8_imm8_norex_effect_step p modrm imm hmod hreg)

theorem test_r1_r8_imm8_norex_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeTestR1R8Imm8NoRex dst imm))
      (Effect.post (testR8Imm8NoRexEffect p 3 dst imm)) := by
  have h := test_r1_r8_imm8_norex_triple_of_bytes p (modrmRegs 1 dst) imm
    (modrmMod_modrmRegs _ _) (modrmReg_modrmRegs _ _)
  rwa [modrmRm_modrmRegs] at h

end X86Proofs
