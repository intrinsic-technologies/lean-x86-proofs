import X86Proofs.Instructions.Btc.Generated.Imm8.Step
import X86Proofs.Instructions.Btc.Generated.Imm8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def btcR64Imm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      a ^^^ BitVec.twoPow 64 (bitOffset b)⟩]
    flags := some (btFlags (StatusFlags.ofRFLAGS s.RFLAGS) a b) }

@[simp] theorem btcR64Imm8Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (imm : BitVec 8) (s : RamState) :
    (btcR64Imm8Effect p len dst imm s).components =
      [.reg dst, .flags, .rip] := rfl

def btcR32Imm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      (a ^^^ BitVec.twoPow 32 (bitOffset b)).setWidth 64⟩]
    flags := some (btFlags (StatusFlags.ofRFLAGS s.RFLAGS) a b) }

@[simp] theorem btcR32Imm8Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (imm : BitVec 8) (s : RamState) :
    (btcR32Imm8Effect p len dst imm s).components =
      [.reg dst, .flags, .rip] := rfl

def btcR16Imm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (a ^^^ BitVec.twoPow 16 (bitOffset b))
        ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (btFlags (StatusFlags.ofRFLAGS s.RFLAGS) a b) }

@[simp] theorem btcR16Imm8Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (imm : BitVec 8) (s : RamState) :
    (btcR16Imm8Effect p len dst imm s).components =
      [.reg dst, .flags, .rip] := rfl

theorem btc_r64_imm8_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p (rex :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm))
      (btcR64Imm8Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := btc_r_imm8_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) modrm hmod hreg imm
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, btcSpec]
  · simp only [afterFetches_RFLAGS, beforeFetch_RFLAGS]
    exact btFlags_allows _ _ _ _

theorem btc_r64_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p)
      (codeRange p (rex :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm))
      (Effect.post (btcR64Imm8Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btcR64Imm8Effect_components]; simp [Component.Covers]) _)
    (btc_r64_imm8_effect_step p rex hrex modrm hmod hreg imm)

theorem btc_r32_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p (0x0F :: 0xBA :: modrm :: immBytes 8 imm))
      (btcR32Imm8Effect p 4 (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := btc_r_imm8_step s h [] (by simp) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl) modrm hmod hreg imm
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, btcSpec]
  · simp only [afterFetches_RFLAGS, beforeFetch_RFLAGS]
    exact btFlags_allows _ _ _ _

theorem btc_r32_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p)
      (codeRange p (0x0F :: 0xBA :: modrm :: immBytes 8 imm))
      (Effect.post (btcR32Imm8Effect p 4 (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btcR32Imm8Effect_components]; simp [Component.Covers]) _)
    (btc_r32_imm8_effect_step p modrm hmod hreg imm)

theorem btc_r32_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p (rex :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm))
      (btcR32Imm8Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := btc_r_imm8_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) modrm hmod hreg imm
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, btcSpec]
  · simp only [afterFetches_RFLAGS, beforeFetch_RFLAGS]
    exact btFlags_allows _ _ _ _

theorem btc_r32_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p)
      (codeRange p (rex :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm))
      (Effect.post (btcR32Imm8Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btcR32Imm8Effect_components]; simp [Component.Covers]) _)
    (btc_r32_imm8_rex_effect_step p rex hrex modrm hmod hreg imm)

theorem btc_r16_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p (0x66 :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm))
      (btcR16Imm8Effect p 5 (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := btc_r16_imm8_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by exact rfl)
    (by rfl) (by rfl) modrm hmod hreg imm
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, btcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · simp only [afterFetches_RFLAGS,
      beforeFetch_RFLAGS]
    exact btFlags_allows _ _ _ _

theorem btc_r16_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p)
      (codeRange p (0x66 :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm))
      (Effect.post (btcR16Imm8Effect p 5 (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btcR16Imm8Effect_components]; simp [Component.Covers]) _)
    (btc_r16_imm8_effect_step p modrm hmod hreg imm)

theorem btc_r16_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p (0x66 :: rex :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm))
      (btcR16Imm8Effect p 6 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 6 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := btc_r16_imm8_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl) modrm hmod hreg imm
    hcode.bytesAt hlow
  simp only [scanContext_66_rex _ _ hr] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_b4
      (oszRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, btcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · simp only [afterFetches_RFLAGS,
      beforeFetch_RFLAGS]
    exact btFlags_allows _ _ _ _

theorem btc_r16_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p)
      (codeRange p (0x66 :: rex :: 0x0F :: 0xBA :: modrm :: immBytes 8 imm))
      (Effect.post (btcR16Imm8Effect p 6 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btcR16Imm8Effect_components]; simp [Component.Covers]) _)
    (btc_r16_imm8_rex_effect_step p rex hrex modrm hmod hreg imm)

theorem btc_r64_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeBtcR64Imm8 dst imm))
      (Effect.post (btcR64Imm8Effect p (encodeBtcR64Imm8 dst imm).length (dst.setWidth 5)
        imm)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeBtcR64Imm8_spec dst imm
  rw [hbytes, ← hdst]
  exact btc_r64_imm8_triple_of_bytes p rex hrex modrm hmod hreg imm

theorem btc_r32_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeBtcR32Imm8 dst imm))
      (Effect.post (btcR32Imm8Effect p (encodeBtcR32Imm8 dst imm).length (dst.setWidth 5)
        imm)) := by
  rcases encodeBtcR32Imm8_spec dst imm with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact btc_r32_imm8_triple_of_bytes p modrm hmod hreg imm
  · rw [hbytes, ← hdst]
    exact btc_r32_imm8_rex_triple_of_bytes p rex hrex modrm hmod hreg imm

theorem btc_r16_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeBtcR16Imm8 dst imm))
      (Effect.post (btcR16Imm8Effect p (encodeBtcR16Imm8 dst imm).length (dst.setWidth 5)
        imm)) := by
  rcases encodeBtcR16Imm8_spec dst imm with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact btc_r16_imm8_triple_of_bytes p modrm hmod hreg imm
  · rw [hbytes, ← hdst]
    exact btc_r16_imm8_rex_triple_of_bytes p rex hrex modrm hmod hreg imm

attribute [x86_compose] btcR64Imm8Effect btcR32Imm8Effect btcR16Imm8Effect

@[x86_local] theorem btcR64Imm8Effect_local {p : BitVec 64} {len : Nat}
    {dst : BitVec 5} {imm : BitVec 8} :
    Effect.Local (btcR64Imm8Effect p len dst imm) := by
  effect_local [btcR64Imm8Effect, btFlags]

@[x86_local] theorem btcR32Imm8Effect_local {p : BitVec 64} {len : Nat}
    {dst : BitVec 5} {imm : BitVec 8} :
    Effect.Local (btcR32Imm8Effect p len dst imm) := by
  effect_local [btcR32Imm8Effect, btFlags]

@[x86_local] theorem btcR16Imm8Effect_local {p : BitVec 64} {len : Nat}
    {dst : BitVec 5} {imm : BitVec 8} :
    Effect.Local (btcR16Imm8Effect p len dst imm) := by
  effect_local [btcR16Imm8Effect, btFlags]

end X86Proofs
