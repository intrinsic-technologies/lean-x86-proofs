import X86Proofs.Instructions.Imul.Generated.RRImm8.Step
import X86Proofs.Instructions.Imul.Generated.RRImm8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def imulR64R64Imm8Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.reg src : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      BitVec.ofInt 64 (a.toInt * b.toInt)⟩]
    flags := some (imulFlags a b) }

@[simp] theorem imulR64R64Imm8Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (imm : BitVec 8) (s : RamState) :
    (imulR64R64Imm8Effect p len dst src imm s).components = [.reg dst, .flags, .rip] := rfl

def imulR32R32Imm8Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.reg src : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      (BitVec.ofInt 32 (a.toInt * b.toInt)).setWidth 64⟩]
    flags := some (imulFlags a b) }

@[simp] theorem imulR32R32Imm8Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (imm : BitVec 8) (s : RamState) :
    (imulR32R32Imm8Effect p len dst src imm s).components = [.reg dst, .flags, .rip] := rfl

def imulR16R16Imm8Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.reg src : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (BitVec.ofInt 16 (a.toInt * b.toInt)) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (imulFlags a b) }

@[simp] theorem imulR16R16Imm8Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (imm : BitVec 8) (s : RamState) :
    (imulR16R16Imm8Effect p len dst src imm s).components = [.reg dst, .flags, .rip] := rfl

theorem imul_r64_r64_imm8_effect_step [Bindings] (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p (rex :: 0x6B :: modrm :: immBytes 8 imm))
      (imulR64R64Imm8Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := imul_r_r_imm8_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) modrm hmod imm
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_r4 (rexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_b4 (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, imulSpec]
  · exact imulFlags_allows _ _ _

theorem imul_r64_r64_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p)
      (codeRange p (rex :: 0x6B :: modrm :: immBytes 8 imm))
      (Effect.post (imulR64R64Imm8Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulR64R64Imm8Effect_components]; simp [Component.Covers]) _)
    (imul_r64_r64_imm8_effect_step p rex hrex modrm hmod imm)

theorem imul_r32_r32_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p (0x6B :: modrm :: immBytes 8 imm))
      (imulR32R32Imm8Effect p 3 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := imul_r_r_imm8_step s h [] (by simp) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl) modrm hmod imm
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4 (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4 (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, imulSpec]
  · exact imulFlags_allows _ _ _

theorem imul_r32_r32_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p)
      (codeRange p (0x6B :: modrm :: immBytes 8 imm))
      (Effect.post (imulR32R32Imm8Effect p 3 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulR32R32Imm8Effect_components]; simp [Component.Covers]) _)
    (imul_r32_r32_imm8_effect_step p modrm hmod imm)

theorem imul_r32_r32_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8) (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p (rex :: 0x6B :: modrm :: immBytes 8 imm))
      (imulR32R32Imm8Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := imul_r_r_imm8_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) modrm hmod imm
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_r4 (rexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_b4 (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, imulSpec]
  · exact imulFlags_allows _ _ _

theorem imul_r32_r32_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8) (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p)
      (codeRange p (rex :: 0x6B :: modrm :: immBytes 8 imm))
      (Effect.post (imulR32R32Imm8Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulR32R32Imm8Effect_components]; simp [Component.Covers]) _)
    (imul_r32_r32_imm8_rex_effect_step p rex hrex modrm hmod imm)

theorem imul_r16_r16_imm8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p (0x66 :: 0x6B :: modrm :: immBytes 8 imm))
      (imulR16R16Imm8Effect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := imul_r16_r16_imm8_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by exact rfl)
    (by rfl) (by rfl) modrm hmod imm
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r4 (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b4 (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, imulSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact imulFlags_allows _ _ _

theorem imul_r16_r16_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p)
      (codeRange p (0x66 :: 0x6B :: modrm :: immBytes 8 imm))
      (Effect.post (imulR16R16Imm8Effect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulR16R16Imm8Effect_components]; simp [Component.Covers]) _)
    (imul_r16_r16_imm8_effect_step p modrm hmod imm)

theorem imul_r16_r16_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8) (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p (0x66 :: rex :: 0x6B :: modrm :: immBytes 8 imm))
      (imulR16R16Imm8Effect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := imul_r16_r16_imm8_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl) modrm hmod imm
    hcode.bytesAt hlow
  simp only [scanContext_66_rex _ _ hr] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_r4 (oszRexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  have hsrc : gprNumber (oszRexContext s.DS rex.toBitVec).rex_b4 (oszRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, imulSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact imulFlags_allows _ _ _

theorem imul_r16_r16_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8) (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p)
      (codeRange p (0x66 :: rex :: 0x6B :: modrm :: immBytes 8 imm))
      (Effect.post (imulR16R16Imm8Effect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulR16R16Imm8Effect_components]; simp [Component.Covers]) _)
    (imul_r16_r16_imm8_rex_effect_step p rex hrex modrm hmod imm)

theorem imul_r64_r64_imm8_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeImulR64R64Imm8 dst src imm))
      (Effect.post (imulR64R64Imm8Effect p (encodeImulR64R64Imm8 dst src imm).length (dst.setWidth 5)
        (src.setWidth 5) imm)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeImulR64R64Imm8_spec dst src imm
  rw [hbytes, ← hdst, ← hsrc]
  exact imul_r64_r64_imm8_triple_of_bytes p rex hrex modrm hmod imm

theorem imul_r32_r32_imm8_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeImulR32R32Imm8 dst src imm))
      (Effect.post (imulR32R32Imm8Effect p (encodeImulR32R32Imm8 dst src imm).length (dst.setWidth 5)
        (src.setWidth 5) imm)) := by
  rcases encodeImulR32R32Imm8_spec dst src imm with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact imul_r32_r32_imm8_triple_of_bytes p modrm hmod imm
  · rw [hbytes, ← hdst, ← hsrc]
    exact imul_r32_r32_imm8_rex_triple_of_bytes p rex hrex modrm hmod imm

theorem imul_r16_r16_imm8_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeImulR16R16Imm8 dst src imm))
      (Effect.post (imulR16R16Imm8Effect p (encodeImulR16R16Imm8 dst src imm).length (dst.setWidth 5)
        (src.setWidth 5) imm)) := by
  rcases encodeImulR16R16Imm8_spec dst src imm with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact imul_r16_r16_imm8_triple_of_bytes p modrm hmod imm
  · rw [hbytes, ← hdst, ← hsrc]
    exact imul_r16_r16_imm8_rex_triple_of_bytes p rex hrex modrm hmod imm

attribute [x86_compose] imulR64R64Imm8Effect imulR32R32Imm8Effect imulR16R16Imm8Effect

@[x86_local] theorem imulR64R64Imm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 5} {imm : BitVec 8} :
    Effect.Local (imulR64R64Imm8Effect p len dst src imm) := by
  effect_local [imulR64R64Imm8Effect, imulFlags]

@[x86_local] theorem imulR32R32Imm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 5} {imm : BitVec 8} :
    Effect.Local (imulR32R32Imm8Effect p len dst src imm) := by
  effect_local [imulR32R32Imm8Effect, imulFlags]

@[x86_local] theorem imulR16R16Imm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 5} {imm : BitVec 8} :
    Effect.Local (imulR16R16Imm8Effect p len dst src imm) := by
  effect_local [imulR16R16Imm8Effect, imulFlags]

end X86Proofs
