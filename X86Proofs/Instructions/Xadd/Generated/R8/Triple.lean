import X86Proofs.Instructions.Xadd.Generated.R8.Step
import X86Proofs.Instructions.Xadd.Generated.R8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def xaddR8R8Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) :
    Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  let b := (Operand.reg src : Operand 8).read s
  let r := xaddSpec a b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg src : Operand 64),
        mergeGPR 8 (if src = dst then r.1 else r.2.1) ((Operand.reg src : Operand 64).read s)⟩,
      ⟨(Operand.reg dst : Operand 64), mergeGPR 8 (r.1) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags r.2.2) }

@[simp] theorem xaddR8R8Effect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) :
    (xaddR8R8Effect p len dst src s).components = [.reg src, .reg dst, .flags, .rip] := rfl

theorem xadd_r8_r8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg8 : (modrmReg modrm).toNat < 4)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([0x0F, 0xC0, modrm]))
      (xaddR8R8Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm))) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := xadd_r8_r8_step s h [] (by simp)
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
  refine ⟨_, hstep, ReadyToStep.afterStep_writePairOutputs h _ _ _ _ _ _ _ _,
    ⟨afterStep_writePairOutputs_rip h _ _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writePairOutputs s _ _ _ _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep]
    by_cases heq : (gprNumber 0 0 (modrmReg modrm)) =
      (gprNumber 0 0 (modrmRm modrm))
    · rw [heq, Operand.read_writePairOutputs_same (by decide)]
      simp only [Operand.read_afterFetches, Operand.read_beforeFetch, ↓reduceIte,
        and_self]
    · rw [Operand.read_writePairOutputs_fst _ heq, Operand.read_writePairOutputs_snd _ heq]
      simp only [Operand.read_afterFetches, Operand.read_beforeFetch, heq, ↓reduceIte,
        and_self]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem xadd_r8_r8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg8 : (modrmReg modrm).toNat < 4)
    (hrm8 : (modrmRm modrm).toNat < 4) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([0x0F, 0xC0, modrm]))
      (Effect.post (xaddR8R8Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [xaddR8R8Effect_components]; simp [Component.Covers]) _)
    (xadd_r8_r8_effect_step p modrm hmod hreg8 hrm8)

theorem xadd_r8_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([rex, 0x0F, 0xC0, modrm]))
      (xaddR8R8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := xadd_r8_r8_step s h [rex] (by simpa using hr.scanPrefix)
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
  refine ⟨_, hstep, ReadyToStep.afterStep_writePairOutputs h _ _ _ _ _ _ _ _,
    ⟨afterStep_writePairOutputs_rip h _ _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writePairOutputs s _ _ _ _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep]
    by_cases heq : (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    · rw [heq, Operand.read_writePairOutputs_same (by decide)]
      simp only [Operand.read_afterFetches, Operand.read_beforeFetch, ↓reduceIte,
        and_self]
    · rw [Operand.read_writePairOutputs_fst _ heq, Operand.read_writePairOutputs_snd _ heq]
      simp only [Operand.read_afterFetches, Operand.read_beforeFetch, heq, ↓reduceIte,
        and_self]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem xadd_r8_r8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([rex, 0x0F, 0xC0, modrm]))
      (Effect.post (xaddR8R8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [xaddR8R8Effect_components]; simp [Component.Covers]) _)
    (xadd_r8_r8_rex_effect_step p rex hr modrm hmod)

def xaddR8R8NoRexEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 3)
    (s : RamState) : Effect :=
  let a := (Operand.byteReg dst).read s
  let b := (Operand.byteReg src).read s
  let x := (Operand.reg (byteRegGpr src) : Operand 64).read s
  let y := (Operand.reg (byteRegGpr dst) : Operand 64).read s
  let r := xaddSpec a b
  let w := mergeByteRegPair src dst r.2.1 r.1 x y
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (byteRegGpr src) : Operand 64),
        if byteRegGpr src = byteRegGpr dst then w else mergeByteReg src r.2.1 x⟩,
      ⟨(Operand.reg (byteRegGpr dst) : Operand 64), w⟩]
    flags := some (.ofStatusFlags r.2.2) }

@[simp] theorem xaddR8R8NoRexEffect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 3)
    (s : RamState) :
    (xaddR8R8NoRexEffect p len dst src s).components =
      [.reg (byteRegGpr src), .reg (byteRegGpr dst), .flags, .rip] := rfl

theorem xadd_r8_r8_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([0x0F, 0xC0, modrm]))
      (xaddR8R8NoRexEffect p 3 (modrmRm modrm) (modrmReg modrm)) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := xadd_r8_r8_gpr8_step s h [] (by simp) (by simp) rfl rfl modrm hmod
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : Operand.gpr8 (gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm))
      (byteRex (scanContext s.DS (PrefixSegments.ofState s) [])) = Operand.byteReg (modrmRm modrm) := rfl
  have hsrc : Operand.gpr8 (gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 (modrmReg modrm))
      (byteRex (scanContext s.DS (PrefixSegments.ofState s) [])) = Operand.byteReg (modrmReg modrm) := rfl
  rw [hdst, hsrc] at hstep
  simp only [writePairOutputs8_byteReg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writePairOutputs h _ _ _ _ _ _ _ _,
    ⟨afterStep_writePairOutputs_rip h _ _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writePairOutputs s _ _ _ _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep]
    by_cases heq : byteRegGpr (modrmReg modrm) = byteRegGpr (modrmRm modrm)
    · rw [heq, Operand.read_writePairOutputs_same (by decide)]
      simp only [Operand.read_afterFetches, Operand.read_beforeFetch, mergeGPR_64, ↓reduceIte,
        and_self]
    · rw [Operand.read_writePairOutputs_fst _ heq, Operand.read_writePairOutputs_snd _ heq]
      simp only [Operand.read_afterFetches, Operand.read_beforeFetch, mergeGPR_64, heq,
        ↓reduceIte, and_self]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem xadd_r8_r8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([0x0F, 0xC0, modrm]))
      (Effect.post (xaddR8R8NoRexEffect p 3 (modrmRm modrm) (modrmReg modrm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [xaddR8R8NoRexEffect_components]; simp [Component.Covers]) _)
    (xadd_r8_r8_norex_effect_step p modrm hmod)

theorem xadd_r8_r8_norex_triple [Bindings] (p : BitVec 64) (dst src : BitVec 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p (encodeXaddR8R8NoRex dst src))
      (Effect.post (xaddR8R8NoRexEffect p 3 dst src)) := by
  have h := xadd_r8_r8_norex_triple_of_bytes p (modrmRegs src dst) (modrmMod_modrmRegs _ _)
  rwa [modrmRm_modrmRegs, modrmReg_modrmRegs] at h

theorem xadd_r8_r8_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p)
      (codeRange p (encodeXaddR8R8 dst src))
      (Effect.post (xaddR8R8Effect p (encodeXaddR8R8 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  rcases encodeXaddR8R8_spec dst src with ⟨modrm, hbytes, hmod, hreg8, hrm8, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact xadd_r8_r8_triple_of_bytes p modrm hmod hreg8 hrm8
  · rw [hbytes, ← hdst, ← hsrc]
    exact xadd_r8_r8_rex_triple_of_bytes p rex hrex modrm hmod

attribute [x86_compose] xaddR8R8Effect

@[x86_local] theorem xaddR8R8Effect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5} :
    Effect.Local (xaddR8R8Effect p len dst src) := by
  effect_local [xaddR8R8Effect]

attribute [x86_compose] xaddR8R8NoRexEffect

@[x86_local] theorem xaddR8R8NoRexEffect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 3} :
    Effect.Local (xaddR8R8NoRexEffect p len dst src) := by
  effect_local [xaddR8R8NoRexEffect]

end X86Proofs
