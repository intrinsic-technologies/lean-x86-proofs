import X86Proofs.Instructions.Mov.Generated.R8Imm8C6.Step
import X86Proofs.Instructions.Mov.Generated.R8Imm8C6.Encode
import X86Proofs.Instructions.Mov.Generated.R8Imm8.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem mov_r8_imm8_c6_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) (hrm8 : (modrmRm modrm).toNat < 4)
    (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0xC6 :: modrm :: immBytes 8 imm))
      (movR8Imm8Effect p 3 (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := mov_r8_imm8_c6_step s h [] (by simp)
    (by simp)
    (by rfl) (by rfl)
    modrm hmod hreg (.inr (gprNumber_zero_lt_four hrm8))
    imm hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, movSpec]

theorem mov_r8_imm8_c6_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) (hrm8 : (modrmRm modrm).toNat < 4)
    (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (0xC6 :: modrm :: immBytes 8 imm))
      (Effect.post (movR8Imm8Effect p 3 (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movR8Imm8Effect_components]; simp [Component.Covers]) _)
    (mov_r8_imm8_c6_effect_step p modrm hmod hreg hrm8 imm)

theorem mov_r8_imm8_c6_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0xC6 :: modrm :: immBytes 8 imm))
      (movR8Imm8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := mov_r8_imm8_c6_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    modrm hmod hreg (.inl (by rw [scanContext_rex _ _ hr]; rfl))
    imm hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, movSpec]

theorem mov_r8_imm8_c6_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0xC6 :: modrm :: immBytes 8 imm))
      (Effect.post (movR8Imm8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movR8Imm8Effect_components]; simp [Component.Covers]) _)
    (mov_r8_imm8_c6_rex_effect_step p rex hr modrm hmod hreg imm)

theorem mov_r8_imm8_c6_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0xC6 :: modrm :: immBytes 8 imm))
      (movR8Imm8NoRexEffect p 3 (modrmRm modrm) imm) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := mov_r8_imm8_c6_gpr8_step s h [] (by simp) (by simp) rfl rfl
    modrm hmod hreg imm hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : Operand.gpr8 (gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm))
      (byteRex (scanContext s.DS (PrefixSegments.ofState s) [])) = Operand.byteReg (modrmRm modrm) := rfl
  rw [hdst] at hstep
  simp only [writeResult_byteReg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, Operand.read_afterFetches,
    Operand.read_beforeFetch, movSpec]

theorem mov_r8_imm8_c6_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (0xC6 :: modrm :: immBytes 8 imm))
      (Effect.post (movR8Imm8NoRexEffect p 3 (modrmRm modrm) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movR8Imm8NoRexEffect_components]; simp [Component.Covers]) _)
    (mov_r8_imm8_c6_norex_effect_step p modrm hmod hreg imm)

theorem mov_r8_imm8_c6_norex_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovR8Imm8C6NoRex dst imm))
      (Effect.post (movR8Imm8NoRexEffect p 3 dst imm)) := by
  have h := mov_r8_imm8_c6_norex_triple_of_bytes p (modrmRegs 0 dst) (modrmMod_modrmRegs _ _)
    (modrmReg_modrmRegs _ _) imm
  rwa [modrmRm_modrmRegs] at h

theorem mov_r8_imm8_c6_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovR8Imm8C6 dst imm))
      (Effect.post (movR8Imm8Effect p (encodeMovR8Imm8C6 dst imm).length (dst.setWidth 5)
        imm)) := by
  rcases encodeMovR8Imm8C6_spec dst imm with ⟨modrm, hbytes, hmod, hreg, hrm8, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact mov_r8_imm8_c6_triple_of_bytes p modrm hmod hreg hrm8 imm
  · rw [hbytes, ← hdst]
    exact mov_r8_imm8_c6_rex_triple_of_bytes p rex hrex modrm hmod hreg imm

end X86Proofs
