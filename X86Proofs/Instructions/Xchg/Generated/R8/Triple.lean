import X86Proofs.Instructions.Xchg.Generated.R8.Step
import X86Proofs.Instructions.Xchg.Generated.R8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def xchgR8R8Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) :
    Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  let b := (Operand.reg src : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg src : Operand 64),
        mergeGPR 8 (a) ((Operand.reg src : Operand 64).read s)⟩,
      ⟨(Operand.reg dst : Operand 64), mergeGPR 8 (b) ((Operand.reg dst : Operand 64).read s)⟩] }

@[simp] theorem xchgR8R8Effect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) :
    (xchgR8R8Effect p len dst src s).components = [.reg src, .reg dst, .rip] := rfl

theorem xchg_r8_r8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg8 : (modrmReg modrm).toNat < 4)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([0x86, modrm]))
      (xchgR8R8Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm))) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := xchg_r8_r8_step s h [] (by simp)
    (by simp)
    (by rfl) (by rfl) modrm hmod
    (.inr (gprNumber_zero_lt_four hreg8)) (.inr (gprNumber_zero_lt_four hrm8))
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResultPair h _ _ _ _ _ _,
    ⟨afterStep_writeResultPair_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResultPair s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_afterStep]
  by_cases heq : (gprNumber 0 0 (modrmReg modrm)) =
      (gprNumber 0 0 (modrmRm modrm))
  · rw [heq, Operand.read_writeResultPair_same (by decide)]
    simp only [xchgSpec, Operand.read_afterFetches, Operand.read_beforeFetch, and_self]
  · rw [Operand.read_writeResultPair_fst _ heq, Operand.read_writeResultPair_snd _ heq]
    simp only [xchgSpec, Operand.read_afterFetches, Operand.read_beforeFetch, and_self]

theorem xchg_r8_r8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg8 : (modrmReg modrm).toNat < 4)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([0x86, modrm]))
      (Effect.post (xchgR8R8Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [xchgR8R8Effect_components]; simp [Component.Covers]) _)
    (xchg_r8_r8_effect_step p modrm hmod hreg8 hrm8)

theorem xchg_r8_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([rex, 0x86, modrm]))
      (xchgR8R8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := xchg_r8_r8_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) modrm hmod
    (.inl (by rw [scanContext_rex _ _ hr]; rfl)) (.inl (by rw [scanContext_rex _ _ hr]; rfl))
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResultPair h _ _ _ _ _ _,
    ⟨afterStep_writeResultPair_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResultPair s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_afterStep]
  by_cases heq : (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
  · rw [heq, Operand.read_writeResultPair_same (by decide)]
    simp only [xchgSpec, Operand.read_afterFetches, Operand.read_beforeFetch, and_self]
  · rw [Operand.read_writeResultPair_fst _ heq, Operand.read_writeResultPair_snd _ heq]
    simp only [xchgSpec, Operand.read_afterFetches, Operand.read_beforeFetch, and_self]

theorem xchg_r8_r8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([rex, 0x86, modrm]))
      (Effect.post (xchgR8R8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [xchgR8R8Effect_components]; simp [Component.Covers]) _)
    (xchg_r8_r8_rex_effect_step p rex hr modrm hmod)

def xchgR8R8NoRexEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 3)
    (s : RamState) : Effect :=
  let a := (Operand.byteReg dst).read s
  let b := (Operand.byteReg src).read s
  let x := (Operand.reg (byteRegGpr src) : Operand 64).read s
  let y := (Operand.reg (byteRegGpr dst) : Operand 64).read s
  let w := mergeByteRegPair src dst a b x y
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (byteRegGpr src) : Operand 64),
        if byteRegGpr src = byteRegGpr dst then w else mergeByteReg src a x⟩,
      ⟨(Operand.reg (byteRegGpr dst) : Operand 64), w⟩] }

@[simp] theorem xchgR8R8NoRexEffect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 3)
    (s : RamState) :
    (xchgR8R8NoRexEffect p len dst src s).components =
      [.reg (byteRegGpr src), .reg (byteRegGpr dst), .rip] := rfl

theorem xchg_r8_r8_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([0x86, modrm]))
      (xchgR8R8NoRexEffect p 2 (modrmRm modrm) (modrmReg modrm)) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := xchg_r8_r8_gpr8_step s h [] (by simp) (by simp) rfl rfl modrm hmod
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : Operand.gpr8 (gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm))
      (byteRex (scanContext s.DS (PrefixSegments.ofState s) [])) = Operand.byteReg (modrmRm modrm) := rfl
  have hsrc : Operand.gpr8 (gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 (modrmReg modrm))
      (byteRex (scanContext s.DS (PrefixSegments.ofState s) [])) = Operand.byteReg (modrmReg modrm) := rfl
  rw [hdst, hsrc] at hstep
  simp only [writeResultPair8_byteReg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResultPair h _ _ _ _ _ _,
    ⟨afterStep_writeResultPair_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResultPair s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_afterStep]
  by_cases heq : byteRegGpr (modrmReg modrm) = byteRegGpr (modrmRm modrm)
  · rw [heq, Operand.read_writeResultPair_same (by decide)]
    simp only [xchgSpec, Operand.read_afterFetches, Operand.read_beforeFetch, mergeGPR_64,
      ↓reduceIte, and_self]
  · rw [Operand.read_writeResultPair_fst _ heq, Operand.read_writeResultPair_snd _ heq]
    simp only [xchgSpec, Operand.read_afterFetches, Operand.read_beforeFetch, mergeGPR_64, heq,
      ↓reduceIte, and_self]

theorem xchg_r8_r8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([0x86, modrm]))
      (Effect.post (xchgR8R8NoRexEffect p 2 (modrmRm modrm) (modrmReg modrm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [xchgR8R8NoRexEffect_components]; simp [Component.Covers]) _)
    (xchg_r8_r8_norex_effect_step p modrm hmod)

theorem xchg_r8_r8_norex_triple [Bindings] (p : BitVec 64) (dst src : BitVec 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p (encodeXchgR8R8NoRex dst src))
      (Effect.post (xchgR8R8NoRexEffect p 2 dst src)) := by
  have h := xchg_r8_r8_norex_triple_of_bytes p (modrmRegs src dst) (modrmMod_modrmRegs _ _)
  rwa [modrmRm_modrmRegs, modrmReg_modrmRegs] at h

theorem xchg_r8_r8_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p)
      (codeRange p (encodeXchgR8R8 dst src))
      (Effect.post (xchgR8R8Effect p (encodeXchgR8R8 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  rcases encodeXchgR8R8_spec dst src with ⟨modrm, hbytes, hmod, hreg8, hrm8, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact xchg_r8_r8_triple_of_bytes p modrm hmod hreg8 hrm8
  · rw [hbytes, ← hdst, ← hsrc]
    exact xchg_r8_r8_rex_triple_of_bytes p rex hrex modrm hmod

attribute [x86_compose] xchgR8R8Effect

@[x86_local] theorem xchgR8R8Effect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5} :
    Effect.Local (xchgR8R8Effect p len dst src) := by
  effect_local [xchgR8R8Effect]

attribute [x86_compose] xchgR8R8NoRexEffect

@[x86_local] theorem xchgR8R8NoRexEffect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 3} :
    Effect.Local (xchgR8R8NoRexEffect p len dst src) := by
  effect_local [xchgR8R8NoRexEffect]

end X86Proofs
