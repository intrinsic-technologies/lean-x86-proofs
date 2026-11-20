import X86Proofs.Instructions.Bt.Generated.Imm8.Step
import X86Proofs.Instructions.Bt.Generated.Imm8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def btR64Imm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (btFlags (StatusFlags.ofRFLAGS s.RFLAGS) a b) }

@[simp] theorem btR64Imm8Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (imm : BitVec 8) (s : RamState) :
    (btR64Imm8Effect p len dst imm s).components =
      [.flags, .rip] := rfl

def btR32Imm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (btFlags (StatusFlags.ofRFLAGS s.RFLAGS) a b) }

@[simp] theorem btR32Imm8Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (imm : BitVec 8) (s : RamState) :
    (btR32Imm8Effect p len dst imm s).components =
      [.flags, .rip] := rfl

def btR16Imm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (btFlags (StatusFlags.ofRFLAGS s.RFLAGS) a b) }

@[simp] theorem btR16Imm8Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (imm : BitVec 8) (s : RamState) :
    (btR16Imm8Effect p len dst imm s).components =
      [.flags, .rip] := rfl

theorem bt_r64_imm8_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p (rex :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm))
      (btR64Imm8Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := bt_r_imm8_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) modrm hmod hreg imm
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeFlagsOutputs h _ _ _ _,
    ⟨afterStep_writeFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s _ _ _ _⟩⟩
  simp only [afterFetches_RFLAGS,
    beforeFetch_RFLAGS]
  exact btFlags_allows _ _ _ _

theorem bt_r64_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p)
      (codeRange p (rex :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm))
      (Effect.post (btR64Imm8Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btR64Imm8Effect_components]; simp [Component.Covers]) _)
    (bt_r64_imm8_effect_step p rex hrex modrm hmod hreg imm)

theorem bt_r32_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p (0x0F :: 0xBA :: modrm :: immBytes 8 imm))
      (btR32Imm8Effect p 4 (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := bt_r_imm8_step s h [] (by simp) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl) modrm hmod hreg imm
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeFlagsOutputs h _ _ _ _,
    ⟨afterStep_writeFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s _ _ _ _⟩⟩
  simp only [afterFetches_RFLAGS,
    beforeFetch_RFLAGS]
  exact btFlags_allows _ _ _ _

theorem bt_r32_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p)
      (codeRange p (0x0F :: 0xBA :: modrm :: immBytes 8 imm))
      (Effect.post (btR32Imm8Effect p 4 (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btR32Imm8Effect_components]; simp [Component.Covers]) _)
    (bt_r32_imm8_effect_step p modrm hmod hreg imm)

theorem bt_r32_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p (rex :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm))
      (btR32Imm8Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := bt_r_imm8_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) modrm hmod hreg imm
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeFlagsOutputs h _ _ _ _,
    ⟨afterStep_writeFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s _ _ _ _⟩⟩
  simp only [afterFetches_RFLAGS,
    beforeFetch_RFLAGS]
  exact btFlags_allows _ _ _ _

theorem bt_r32_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p)
      (codeRange p (rex :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm))
      (Effect.post (btR32Imm8Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btR32Imm8Effect_components]; simp [Component.Covers]) _)
    (bt_r32_imm8_rex_effect_step p rex hrex modrm hmod hreg imm)

theorem bt_r16_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p (0x66 :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm))
      (btR16Imm8Effect p 5 (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := bt_r16_imm8_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by exact rfl)
    (by rfl) (by rfl) modrm hmod hreg imm
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeFlagsOutputs h _ _ _ _,
    ⟨afterStep_writeFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s _ _ _ _⟩⟩
  simp only [afterFetches_RFLAGS,
    beforeFetch_RFLAGS]
  exact btFlags_allows _ _ _ _

theorem bt_r16_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p)
      (codeRange p (0x66 :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm))
      (Effect.post (btR16Imm8Effect p 5 (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btR16Imm8Effect_components]; simp [Component.Covers]) _)
    (bt_r16_imm8_effect_step p modrm hmod hreg imm)

theorem bt_r16_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p (0x66 :: rex :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm))
      (btR16Imm8Effect p 6 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 6 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := bt_r16_imm8_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl) modrm hmod hreg imm
    hcode.bytesAt hlow
  simp only [scanContext_66_rex _ _ hr] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_b4
      (oszRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeFlagsOutputs h _ _ _ _,
    ⟨afterStep_writeFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s _ _ _ _⟩⟩
  simp only [afterFetches_RFLAGS,
    beforeFetch_RFLAGS]
  exact btFlags_allows _ _ _ _

theorem bt_r16_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p)
      (codeRange p (0x66 :: rex :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm))
      (Effect.post (btR16Imm8Effect p 6 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btR16Imm8Effect_components]; simp [Component.Covers]) _)
    (bt_r16_imm8_rex_effect_step p rex hrex modrm hmod hreg imm)

theorem bt_r64_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeBtR64Imm8 dst imm))
      (Effect.post (btR64Imm8Effect p (encodeBtR64Imm8 dst imm).length (dst.setWidth 5)
        imm)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeBtR64Imm8_spec dst imm
  rw [hbytes, ← hdst]
  exact bt_r64_imm8_triple_of_bytes p rex hrex modrm hmod hreg imm

theorem bt_r32_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeBtR32Imm8 dst imm))
      (Effect.post (btR32Imm8Effect p (encodeBtR32Imm8 dst imm).length (dst.setWidth 5)
        imm)) := by
  rcases encodeBtR32Imm8_spec dst imm with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact bt_r32_imm8_triple_of_bytes p modrm hmod hreg imm
  · rw [hbytes, ← hdst]
    exact bt_r32_imm8_rex_triple_of_bytes p rex hrex modrm hmod hreg imm

theorem bt_r16_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeBtR16Imm8 dst imm))
      (Effect.post (btR16Imm8Effect p (encodeBtR16Imm8 dst imm).length (dst.setWidth 5)
        imm)) := by
  rcases encodeBtR16Imm8_spec dst imm with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact bt_r16_imm8_triple_of_bytes p modrm hmod hreg imm
  · rw [hbytes, ← hdst]
    exact bt_r16_imm8_rex_triple_of_bytes p rex hrex modrm hmod hreg imm

attribute [x86_compose] btR64Imm8Effect btR32Imm8Effect btR16Imm8Effect

@[x86_local] theorem btR64Imm8Effect_local {p : BitVec 64} {len : Nat}
    {dst : BitVec 5} {imm : BitVec 8} :
    Effect.Local (btR64Imm8Effect p len dst imm) := by
  effect_local [btR64Imm8Effect, btFlags]

@[x86_local] theorem btR32Imm8Effect_local {p : BitVec 64} {len : Nat}
    {dst : BitVec 5} {imm : BitVec 8} :
    Effect.Local (btR32Imm8Effect p len dst imm) := by
  effect_local [btR32Imm8Effect, btFlags]

@[x86_local] theorem btR16Imm8Effect_local {p : BitVec 64} {len : Nat}
    {dst : BitVec 5} {imm : BitVec 8} :
    Effect.Local (btR16Imm8Effect p len dst imm) := by
  effect_local [btR16Imm8Effect, btFlags]

end X86Proofs
