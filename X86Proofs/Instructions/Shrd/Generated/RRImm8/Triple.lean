import X86Proofs.Instructions.Shrd.Generated.RRImm8.Step
import X86Proofs.Instructions.Shrd.Generated.RRImm8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def shrdR64R64Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (c : Nat)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := (Operand.reg src : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), shrdResult c a b⟩]
    flags := some (shrdFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a b) }

@[simp] theorem shrdR64R64Effect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (c : Nat) (s : RamState) :
    (shrdR64R64Effect p len dst src c s).components =
      [.reg dst, .flags, .rip] := rfl

def shrdR32R32Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (c : Nat)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := (Operand.reg src : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (shrdResult c a b).setWidth 64⟩]
    flags := some (shrdFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a b) }

@[simp] theorem shrdR32R32Effect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (c : Nat) (s : RamState) :
    (shrdR32R32Effect p len dst src c s).components =
      [.reg dst, .flags, .rip] := rfl

def shrdR16R16Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (c : Nat)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := (Operand.reg src : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), mergeGPR 16 (shrdResult c a b)
        ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (shrdFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a b) }

@[simp] theorem shrdR16R16Effect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (c : Nat) (s : RamState) :
    (shrdR16R16Effect p len dst src c s).components =
      [.reg dst, .flags, .rip] := rfl

theorem shrd_r64_r64_imm8_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p (rex :: 0x0F :: 0xAC :: modrm :: immBytes 8 imm))
      (shrdR64R64Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) (shiftCount 64 imm)) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := shrd_r_r_imm8_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) modrm hmod imm
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self]
    rw [shrdSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega)]
  · simp only [afterFetches_RFLAGS, beforeFetch_RFLAGS]
    exact shrdFlags_allows _ _ _ _ _ _

theorem shrd_r64_r64_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p)
      (codeRange p (rex :: 0x0F :: 0xAC :: modrm :: immBytes 8 imm))
      (Effect.post (shrdR64R64Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) (shiftCount 64 imm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [shrdR64R64Effect_components]; simp [Component.Covers]) _)
    (shrd_r64_r64_imm8_effect_step p rex hrex modrm hmod imm)

theorem shrd_r32_r32_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p (0x0F :: 0xAC :: modrm :: immBytes 8 imm))
      (shrdR32R32Effect p 4 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)) (shiftCount 32 imm)) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := shrd_r_r_imm8_step s h [] (by simp) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl) modrm hmod imm
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32]
    rw [shrdSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega)]
  · simp only [afterFetches_RFLAGS, beforeFetch_RFLAGS]
    exact shrdFlags_allows _ _ _ _ _ _

theorem shrd_r32_r32_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p)
      (codeRange p (0x0F :: 0xAC :: modrm :: immBytes 8 imm))
      (Effect.post (shrdR32R32Effect p 4 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)) (shiftCount 32 imm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [shrdR32R32Effect_components]; simp [Component.Covers]) _)
    (shrd_r32_r32_imm8_effect_step p modrm hmod imm)

theorem shrd_r32_r32_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p (rex :: 0x0F :: 0xAC :: modrm :: immBytes 8 imm))
      (shrdR32R32Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) (shiftCount 32 imm)) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := shrd_r_r_imm8_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) modrm hmod imm
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32]
    rw [shrdSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega)]
  · simp only [afterFetches_RFLAGS, beforeFetch_RFLAGS]
    exact shrdFlags_allows _ _ _ _ _ _

theorem shrd_r32_r32_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p)
      (codeRange p (rex :: 0x0F :: 0xAC :: modrm :: immBytes 8 imm))
      (Effect.post (shrdR32R32Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) (shiftCount 32 imm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [shrdR32R32Effect_components]; simp [Component.Covers]) _)
    (shrd_r32_r32_imm8_rex_effect_step p rex hrex modrm hmod imm)

theorem shrd_r16_r16_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) (hc : shiftCount 16 imm ≤ 16) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p (0x66 :: 0x0F :: 0xAC :: modrm :: immBytes 8 imm))
      (shrdR16R16Effect p 5 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)) (shiftCount 16 imm)) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := shrd_r16_r16_imm8_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by exact rfl)
    (by rfl) (by rfl) modrm hmod imm
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, Operand.read_afterFetches, Operand.read_beforeFetch]
    rw [shrdSpec_fst _ _ _ _ hc]
  · simp only [afterFetches_RFLAGS, beforeFetch_RFLAGS]
    exact shrdFlags_allows _ _ _ _ _ _

theorem shrd_r16_r16_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) (hc : shiftCount 16 imm ≤ 16) :
    Triple (fun s => s.RIP = p)
      (codeRange p (0x66 :: 0x0F :: 0xAC :: modrm :: immBytes 8 imm))
      (Effect.post (shrdR16R16Effect p 5 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)) (shiftCount 16 imm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [shrdR16R16Effect_components]; simp [Component.Covers]) _)
    (shrd_r16_r16_imm8_effect_step p modrm hmod imm hc)

theorem shrd_r16_r16_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) (hc : shiftCount 16 imm ≤ 16) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p (0x66 :: rex :: 0x0F :: 0xAC :: modrm :: immBytes 8 imm))
      (shrdR16R16Effect p 6 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) (shiftCount 16 imm)) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 6 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := shrd_r16_r16_imm8_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl) modrm hmod imm
    hcode.bytesAt hlow
  simp only [scanContext_66_rex _ _ hr] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_b4
      (oszRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  have hsrc : gprNumber (oszRexContext s.DS rex.toBitVec).rex_r4
      (oszRexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, Operand.read_afterFetches, Operand.read_beforeFetch]
    rw [shrdSpec_fst _ _ _ _ hc]
  · simp only [afterFetches_RFLAGS, beforeFetch_RFLAGS]
    exact shrdFlags_allows _ _ _ _ _ _

theorem shrd_r16_r16_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) (hc : shiftCount 16 imm ≤ 16) :
    Triple (fun s => s.RIP = p)
      (codeRange p (0x66 :: rex :: 0x0F :: 0xAC :: modrm :: immBytes 8 imm))
      (Effect.post (shrdR16R16Effect p 6 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) (shiftCount 16 imm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [shrdR16R16Effect_components]; simp [Component.Covers]) _)
    (shrd_r16_r16_imm8_rex_effect_step p rex hrex modrm hmod imm hc)

theorem shrd_r64_r64_imm8_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p)
      (codeRange p (encodeShrdR64R64Imm8 dst src imm))
      (Effect.post (shrdR64R64Effect p (encodeShrdR64R64Imm8 dst src imm).length (dst.setWidth 5)
        (src.setWidth 5) (shiftCount 64 imm))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeShrdR64R64Imm8_spec dst src imm
  rw [hbytes, ← hdst, ← hsrc]
  exact shrd_r64_r64_imm8_triple_of_bytes p rex hrex modrm hmod imm

theorem shrd_r32_r32_imm8_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p)
      (codeRange p (encodeShrdR32R32Imm8 dst src imm))
      (Effect.post (shrdR32R32Effect p (encodeShrdR32R32Imm8 dst src imm).length (dst.setWidth 5)
        (src.setWidth 5) (shiftCount 32 imm))) := by
  rcases encodeShrdR32R32Imm8_spec dst src imm with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact shrd_r32_r32_imm8_triple_of_bytes p modrm hmod imm
  · rw [hbytes, ← hdst, ← hsrc]
    exact shrd_r32_r32_imm8_rex_triple_of_bytes p rex hrex modrm hmod imm

theorem shrd_r16_r16_imm8_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) (imm : BitVec 8)
    (hc : shiftCount 16 imm ≤ 16) :
    Triple (fun s => s.RIP = p)
      (codeRange p (encodeShrdR16R16Imm8 dst src imm))
      (Effect.post (shrdR16R16Effect p (encodeShrdR16R16Imm8 dst src imm).length (dst.setWidth 5)
        (src.setWidth 5) (shiftCount 16 imm))) := by
  rcases encodeShrdR16R16Imm8_spec dst src imm with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact shrd_r16_r16_imm8_triple_of_bytes p modrm hmod imm hc
  · rw [hbytes, ← hdst, ← hsrc]
    exact shrd_r16_r16_imm8_rex_triple_of_bytes p rex hrex modrm hmod imm hc

attribute [x86_compose] shrdR64R64Effect shrdR32R32Effect shrdR16R16Effect

@[x86_local] theorem shrdR64R64Effect_local {p : BitVec 64} {len : Nat}
    {dst src : BitVec 5} {c : Nat} :
    Effect.Local (shrdR64R64Effect p len dst src c) := by
  effect_local [shrdR64R64Effect, shrdFlags]

@[x86_local] theorem shrdR32R32Effect_local {p : BitVec 64} {len : Nat}
    {dst src : BitVec 5} {c : Nat} :
    Effect.Local (shrdR32R32Effect p len dst src c) := by
  effect_local [shrdR32R32Effect, shrdFlags]

@[x86_local] theorem shrdR16R16Effect_local {p : BitVec 64} {len : Nat}
    {dst src : BitVec 5} {c : Nat} :
    Effect.Local (shrdR16R16Effect p len dst src c) := by
  effect_local [shrdR16R16Effect, shrdFlags]

end X86Proofs
