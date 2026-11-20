import X86Proofs.Instructions.Movsx.Generated.RR8.Step
import X86Proofs.Instructions.Movsx.Generated.RR8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movsxR64R8Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : Effect :=
  let x := (Operand.reg src : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      (x).signExtend 64⟩] }

@[simp] theorem movsxR64R8Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (s : RamState) :
    (movsxR64R8Effect p len dst src s).components = [.reg dst, .rip] := rfl

def movsxR32R8Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : Effect :=
  let x := (Operand.reg src : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      ((x).signExtend 32).setWidth 64⟩] }

@[simp] theorem movsxR32R8Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (s : RamState) :
    (movsxR32R8Effect p len dst src s).components = [.reg dst, .rip] := rfl

def movsxR16R8Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : Effect :=
  let x := (Operand.reg src : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 ((x).signExtend 16) ((Operand.reg dst : Operand 64).read s)⟩] }

@[simp] theorem movsxR16R8Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (s : RamState) :
    (movsxR16R8Effect p len dst src s).components = [.reg dst, .rip] := rfl

theorem movsx_r64_r8_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([rex, 0x0F, 0xBE, modrm]))
      (movsxR64R8Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := movsx_r_r8_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) modrm hmod
    (.inl (by rw [scanContext_rex _ _ hr]; rfl))
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, movsxSpec]

theorem movsx_r64_r8_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([rex, 0x0F, 0xBE, modrm]))
      (Effect.post (movsxR64R8Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxR64R8Effect_components]; simp [Component.Covers]) _)
    (movsx_r64_r8_effect_step p rex hrex modrm hmod)

theorem movsx_r32_r8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([0x0F, 0xBE, modrm]))
      (movsxR32R8Effect p 3 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := movsx_r_r8_step s h [] (by simp)
    (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl) modrm hmod
    (.inr (gprNumber_zero_lt_four hrm8))
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movsxSpec]

theorem movsx_r32_r8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([0x0F, 0xBE, modrm]))
      (Effect.post (movsxR32R8Effect p 3 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxR32R8Effect_components]; simp [Component.Covers]) _)
    (movsx_r32_r8_effect_step p modrm hmod hrm8)

theorem movsx_r32_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([rex, 0x0F, 0xBE, modrm]))
      (movsxR32R8Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := movsx_r_r8_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) modrm hmod
    (.inl (by rw [scanContext_rex _ _ hr]; rfl))
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movsxSpec]

theorem movsx_r32_r8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([rex, 0x0F, 0xBE, modrm]))
      (Effect.post (movsxR32R8Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxR32R8Effect_components]; simp [Component.Covers]) _)
    (movsx_r32_r8_rex_effect_step p rex hrex modrm hmod)

theorem movsx_r16_r8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([0x66, 0x0F, 0xBE, modrm]))
      (movsxR16R8Effect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := movsx_r16_r8_step s h [0x66] (by simpa using scanPrefix_66)
    (by simp)
    (by exact rfl)
    (by rfl) (by rfl) modrm hmod
    (.inr (gprNumber_zero_lt_four hrm8))
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, movsxSpec]

theorem movsx_r16_r8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([0x66, 0x0F, 0xBE, modrm]))
      (Effect.post (movsxR16R8Effect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxR16R8Effect_components]; simp [Component.Covers]) _)
    (movsx_r16_r8_effect_step p modrm hmod hrm8)

theorem movsx_r16_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([0x66, rex, 0x0F, 0xBE, modrm]))
      (movsxR16R8Effect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := movsx_r16_r8_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix])
    (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl) modrm hmod
    (.inl (by rw [scanContext_66_rex _ _ hr]; rfl))
    hcode.bytesAt hlow
  simp only [scanContext_66_rex _ _ hr] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_r4
      (oszRexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  have hsrc : gprNumber (oszRexContext s.DS rex.toBitVec).rex_b4
      (oszRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, movsxSpec]

theorem movsx_r16_r8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([0x66, rex, 0x0F, 0xBE, modrm]))
      (Effect.post (movsxR16R8Effect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxR16R8Effect_components]; simp [Component.Covers]) _)
    (movsx_r16_r8_rex_effect_step p rex hrex modrm hmod)

theorem movsx_r64_r8_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovsxR64R8 dst src))
      (Effect.post (movsxR64R8Effect p (encodeMovsxR64R8 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeMovsxR64R8_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact movsx_r64_r8_triple_of_bytes p rex hrex modrm hmod

theorem movsx_r32_r8_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovsxR32R8 dst src))
      (Effect.post (movsxR32R8Effect p (encodeMovsxR32R8 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  rcases encodeMovsxR32R8_spec dst src with ⟨modrm, hbytes, hmod, hrm8, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact movsx_r32_r8_triple_of_bytes p modrm hmod hrm8
  · rw [hbytes, ← hdst, ← hsrc]
    exact movsx_r32_r8_rex_triple_of_bytes p rex hrex modrm hmod

theorem movsx_r16_r8_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovsxR16R8 dst src))
      (Effect.post (movsxR16R8Effect p (encodeMovsxR16R8 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  rcases encodeMovsxR16R8_spec dst src with ⟨modrm, hbytes, hmod, hrm8, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact movsx_r16_r8_triple_of_bytes p modrm hmod hrm8
  · rw [hbytes, ← hdst, ← hsrc]
    exact movsx_r16_r8_rex_triple_of_bytes p rex hrex modrm hmod

def movsxR32R8NoRexEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 3)
    (s : RamState) : Effect :=
  let x := (Operand.byteReg src).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      ((x).signExtend 32).setWidth 64⟩] }

@[simp] theorem movsxR32R8NoRexEffect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (src : BitVec 3) (s : RamState) :
    (movsxR32R8NoRexEffect p len dst src s).components = [.reg dst, .rip] := rfl

theorem movsx_r32_r8_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([0x0F, 0xBE, modrm]))
      (movsxR32R8NoRexEffect p 3 (gprNumber 0 0 (modrmReg modrm)) (modrmRm modrm)) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := movsx_r_r8_gpr8_step s h [] (by simp)
    (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl) modrm hmod
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  have hsrc : Operand.gpr8 (gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm))
      (byteRex (scanContext s.DS (PrefixSegments.ofState s) [])) = Operand.byteReg (modrmRm modrm) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movsxSpec]

theorem movsx_r32_r8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([0x0F, 0xBE, modrm]))
      (Effect.post (movsxR32R8NoRexEffect p 3 (gprNumber 0 0 (modrmReg modrm))
        (modrmRm modrm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxR32R8NoRexEffect_components]; simp [Component.Covers]) _)
    (movsx_r32_r8_norex_effect_step p modrm hmod)

theorem movsx_r32_r8_norex_triple [Bindings] (p : BitVec 64) (dst src : BitVec 3) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovsxR32R8NoRex dst src))
      (Effect.post (movsxR32R8NoRexEffect p 3 (dst.setWidth 5) src)) := by
  have h := movsx_r32_r8_norex_triple_of_bytes p (modrmRegs dst src) (modrmMod_modrmRegs _ _)
  rwa [modrmRm_modrmRegs, modrmReg_modrmRegs, gprNumber_zero_zero] at h

def movsxR16R8NoRexEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 3)
    (s : RamState) : Effect :=
  let x := (Operand.byteReg src).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 ((x).signExtend 16) ((Operand.reg dst : Operand 64).read s)⟩] }

@[simp] theorem movsxR16R8NoRexEffect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (src : BitVec 3) (s : RamState) :
    (movsxR16R8NoRexEffect p len dst src s).components = [.reg dst, .rip] := rfl

theorem movsx_r16_r8_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([0x66, 0x0F, 0xBE, modrm]))
      (movsxR16R8NoRexEffect p 4 (gprNumber 0 0 (modrmReg modrm)) (modrmRm modrm)) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := movsx_r16_r8_gpr8_step s h [0x66] (by simpa using scanPrefix_66)
    (by simp)
    (by exact rfl)
    (by rfl) (by rfl) modrm hmod
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  have hsrc : Operand.gpr8 (gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b3 (modrmRm modrm))
      (byteRex (scanContext s.DS (PrefixSegments.ofState s) [0x66])) = Operand.byteReg (modrmRm modrm) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, movsxSpec]

theorem movsx_r16_r8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([0x66, 0x0F, 0xBE, modrm]))
      (Effect.post (movsxR16R8NoRexEffect p 4 (gprNumber 0 0 (modrmReg modrm))
        (modrmRm modrm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxR16R8NoRexEffect_components]; simp [Component.Covers]) _)
    (movsx_r16_r8_norex_effect_step p modrm hmod)

theorem movsx_r16_r8_norex_triple [Bindings] (p : BitVec 64) (dst src : BitVec 3) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovsxR16R8NoRex dst src))
      (Effect.post (movsxR16R8NoRexEffect p 4 (dst.setWidth 5) src)) := by
  have h := movsx_r16_r8_norex_triple_of_bytes p (modrmRegs dst src) (modrmMod_modrmRegs _ _)
  rwa [modrmRm_modrmRegs, modrmReg_modrmRegs, gprNumber_zero_zero] at h

attribute [x86_compose] movsxR64R8Effect movsxR32R8Effect movsxR16R8Effect

attribute [x86_compose] movsxR32R8NoRexEffect movsxR16R8NoRexEffect

@[x86_local] theorem movsxR64R8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 5} :
    Effect.Local (movsxR64R8Effect p len dst src) := by
  effect_local [movsxR64R8Effect]

@[x86_local] theorem movsxR32R8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 5} :
    Effect.Local (movsxR32R8Effect p len dst src) := by
  effect_local [movsxR32R8Effect]

@[x86_local] theorem movsxR16R8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 5} :
    Effect.Local (movsxR16R8Effect p len dst src) := by
  effect_local [movsxR16R8Effect]

@[x86_local] theorem movsxR32R8NoRexEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 3} :
    Effect.Local (movsxR32R8NoRexEffect p len dst src) := by
  effect_local [movsxR32R8NoRexEffect]

@[x86_local] theorem movsxR16R8NoRexEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 3} :
    Effect.Local (movsxR16R8NoRexEffect p len dst src) := by
  effect_local [movsxR16R8NoRexEffect]

end X86Proofs
