import X86Proofs.Instructions.Mov.Generated.RImmC7.Step
import X86Proofs.Instructions.Mov.Generated.RImmC7.Encode
import X86Proofs.Instructions.Mov.Generated.R16Imm16.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem mov_r32_imm32_c7_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (imm : BitVec 32) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0xC7 :: modrm :: immBytes 32 imm))
      (movR32Imm32Effect p 6 (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 6 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := mov_r32_imm32_c7_step s h [] (by simp)
    (by simp)
    (by exact rfl)
    (by rfl) (by rfl)
    modrm hmod hreg
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
  simp only [Operand.read_writeResult_self32, movSpec, BitVec.signExtend_eq]

theorem mov_r32_imm32_c7_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (0xC7 :: modrm :: immBytes 32 imm))
      (Effect.post (movR32Imm32Effect p 6 (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movR32Imm32Effect_components]; simp [Component.Covers]) _)
    (mov_r32_imm32_c7_effect_step p modrm hmod hreg imm)

theorem mov_r32_imm32_c7_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (imm : BitVec 32) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0xC7 :: modrm :: immBytes 32 imm))
      (movR32Imm32Effect p 7 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 7 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := mov_r32_imm32_c7_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    modrm hmod hreg
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
  simp only [Operand.read_writeResult_self32, movSpec, BitVec.signExtend_eq]

theorem mov_r32_imm32_c7_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0xC7 :: modrm :: immBytes 32 imm))
      (Effect.post (movR32Imm32Effect p 7 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movR32Imm32Effect_components]; simp [Component.Covers]) _)
    (mov_r32_imm32_c7_rex_effect_step p rex hrex modrm hmod hreg imm)

theorem mov_r16_imm16_c7_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (imm : BitVec 16) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x66 :: 0xC7 :: modrm :: immBytes 16 imm))
      (movR16Imm16Effect p 5 (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := mov_r16_imm16_c7_step s h [0x66] (by simpa using scanPrefix_66)
    (by simp)
    (by exact rfl)
    (by rfl) (by rfl)
    modrm hmod hreg
    imm hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, movSpec, BitVec.signExtend_eq]

theorem mov_r16_imm16_c7_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (imm : BitVec 16) :
    Triple (fun s => s.RIP = p) (codeRange p (0x66 :: 0xC7 :: modrm :: immBytes 16 imm))
      (Effect.post (movR16Imm16Effect p 5 (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movR16Imm16Effect_components]; simp [Component.Covers]) _)
    (mov_r16_imm16_c7_effect_step p modrm hmod hreg imm)

theorem mov_r16_imm16_c7_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (imm : BitVec 16) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x66 :: rex :: 0xC7 :: modrm :: immBytes 16 imm))
      (movR16Imm16Effect p 6 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 6 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := mov_r16_imm16_c7_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix])
    (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    modrm hmod hreg
    imm hcode.bytesAt hlow
  simp only [scanContext_66_rex _ _ hr] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_b4
      (oszRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, movSpec, BitVec.signExtend_eq]

theorem mov_r16_imm16_c7_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (imm : BitVec 16) :
    Triple (fun s => s.RIP = p) (codeRange p (0x66 :: rex :: 0xC7 :: modrm :: immBytes 16 imm))
      (Effect.post (movR16Imm16Effect p 6 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movR16Imm16Effect_components]; simp [Component.Covers]) _)
    (mov_r16_imm16_c7_rex_effect_step p rex hrex modrm hmod hreg imm)

theorem mov_r32_imm32_c7_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovR32Imm32C7 dst imm))
      (Effect.post (movR32Imm32Effect p (encodeMovR32Imm32C7 dst imm).length (dst.setWidth 5)
        imm)) := by
  rcases encodeMovR32Imm32C7_spec dst imm with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact mov_r32_imm32_c7_triple_of_bytes p modrm hmod hreg imm
  · rw [hbytes, ← hdst]
    exact mov_r32_imm32_c7_rex_triple_of_bytes p rex hrex modrm hmod hreg imm

theorem mov_r16_imm16_c7_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 16) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovR16Imm16C7 dst imm))
      (Effect.post (movR16Imm16Effect p (encodeMovR16Imm16C7 dst imm).length (dst.setWidth 5)
        imm)) := by
  rcases encodeMovR16Imm16C7_spec dst imm with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact mov_r16_imm16_c7_triple_of_bytes p modrm hmod hreg imm
  · rw [hbytes, ← hdst]
    exact mov_r16_imm16_c7_rex_triple_of_bytes p rex hrex modrm hmod hreg imm

end X86Proofs
