import X86Proofs.Instructions.Mov.Generated.R8.Step
import X86Proofs.Instructions.Mov.Generated.R8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movR8R8Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 ((Operand.reg src : Operand 8).read s)
        ((Operand.reg dst : Operand 64).read s)⟩] }

@[simp] theorem movR8R8Effect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : (movR8R8Effect p len dst src s).components = [.reg dst, .rip] := rfl

def movR8R8NoRexEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 3) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (byteRegGpr dst) : Operand 64),
      mergeByteReg dst ((Operand.byteReg src).read s)
        ((Operand.reg (byteRegGpr dst) : Operand 64).read s)⟩] }

@[simp] theorem movR8R8NoRexEffect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 3)
    (s : RamState) :
    (movR8R8NoRexEffect p len dst src s).components = [.reg (byteRegGpr dst), .rip] := rfl

theorem mov_r8_r8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg8 : (modrmReg modrm).toNat < 4)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([0x88, modrm]))
      (movR8R8Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm))) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := mov_r8_r8_step s h [] (by simp)
    (by simp)
    (by rfl) (by rfl) modrm hmod
    (.inr (gprNumber_zero_lt_four hreg8)) (.inr (gprNumber_zero_lt_four hrm8))
    hcode.bytesAt hlow
  dsimp only at hstep
  have hrmf : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  have hregf : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  rw [hrmf, hregf] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, movSpec, Operand.read_afterFetches,
    Operand.read_beforeFetch]

theorem mov_r8_r8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg8 : (modrmReg modrm).toNat < 4)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([0x88, modrm]))
      (Effect.post (movR8R8Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movR8R8Effect_components]; simp [Component.Covers]) _)
    (mov_r8_r8_effect_step p modrm hmod hreg8 hrm8)

theorem mov_r8_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([rex, 0x88, modrm]))
      (movR8R8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := mov_r8_r8_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) modrm hmod
    (.inl (by rw [scanContext_rex _ _ hr]; rfl)) (.inl (by rw [scanContext_rex _ _ hr]; rfl))
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hrmf : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  have hregf : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  rw [hrmf, hregf] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, movSpec, Operand.read_afterFetches,
    Operand.read_beforeFetch]

theorem mov_r8_r8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([rex, 0x88, modrm]))
      (Effect.post (movR8R8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movR8R8Effect_components]; simp [Component.Covers]) _)
    (mov_r8_r8_rex_effect_step p rex hr modrm hmod)

theorem mov_r8_r8_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([0x88, modrm]))
      (movR8R8NoRexEffect p 2 (modrmRm modrm) (modrmReg modrm)) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := mov_r8_r8_gpr8_step s h [] (by simp) (by simp) rfl rfl modrm hmod
    hcode.bytesAt hlow
  dsimp only at hstep
  have hrmf : Operand.gpr8 (gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm))
      (byteRex (scanContext s.DS (PrefixSegments.ofState s) [])) = Operand.byteReg (modrmRm modrm) := rfl
  have hregf : Operand.gpr8 (gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 (modrmReg modrm))
      (byteRex (scanContext s.DS (PrefixSegments.ofState s) [])) = Operand.byteReg (modrmReg modrm) := rfl
  rw [hrmf, hregf] at hstep
  simp only [writeResult_byteReg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, movSpec, Operand.read_afterFetches,
    Operand.read_beforeFetch]

theorem mov_r8_r8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([0x88, modrm]))
      (Effect.post (movR8R8NoRexEffect p 2 (modrmRm modrm) (modrmReg modrm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movR8R8NoRexEffect_components]; simp [Component.Covers]) _)
    (mov_r8_r8_norex_effect_step p modrm hmod)

theorem mov_r8_r8_norex_triple [Bindings] (p : BitVec 64) (dst src : BitVec 3) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovR8R8NoRex dst src))
      (Effect.post (movR8R8NoRexEffect p 2 dst src)) := by
  have h := mov_r8_r8_norex_triple_of_bytes p (modrmRegs src dst)
    (modrmMod_modrmRegs _ _)
  rwa [modrmRm_modrmRegs, modrmReg_modrmRegs] at h

theorem mov_r8_r8_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovR8R8 dst src))
      (Effect.post (movR8R8Effect p (encodeMovR8R8 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  rcases encodeMovR8R8_spec dst src with ⟨modrm, hbytes, hmod, hreg8, hrm8, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact mov_r8_r8_triple_of_bytes p modrm hmod hreg8 hrm8
  · rw [hbytes, ← hdst, ← hsrc]
    exact mov_r8_r8_rex_triple_of_bytes p rex hrex modrm hmod

attribute [x86_compose] movR8R8Effect

@[x86_local] theorem movR8R8Effect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5} :
    Effect.Local (movR8R8Effect p len dst src) := by
  effect_local [movR8R8Effect]

attribute [x86_compose] movR8R8NoRexEffect

@[x86_local] theorem movR8R8NoRexEffect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 3} :
    Effect.Local (movR8R8NoRexEffect p len dst src) := by
  effect_local [movR8R8NoRexEffect]

end X86Proofs
