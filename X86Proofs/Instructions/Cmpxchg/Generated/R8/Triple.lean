import X86Proofs.Instructions.Cmpxchg.Generated.R8.Step
import X86Proofs.Instructions.Cmpxchg.Generated.R8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cmpxchgR8R8Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (c : Bool) (s : RamState) :
    Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  let b := (Operand.reg src : Operand 8).read s
  let acc := (Operand.reg 0 : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (if c then dst else 0) : Operand 64),
      if c then mergeGPR 8 (b) ((Operand.reg dst : Operand 64).read s)
      else mergeGPR 8 (a) ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (cmpSpec acc a)) }

@[simp] theorem cmpxchgR8R8Effect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (c : Bool) (s : RamState) :
    (cmpxchgR8R8Effect p len dst src c s).components =
      [.reg (if c then dst else 0), .flags, .rip] := rfl

theorem cmpxchg_r8_r8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg8 : (modrmReg modrm).toNat < 4)
    (hrm8 : (modrmRm modrm).toNat < 4) (c : Bool) :
    StepEffect (fun s => s.RIP = p ∧
        ((Operand.reg 0 : Operand 8).read s ==
          (Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 8).read s) = c)
      (codeRange p ([0x0F, 0xB0, modrm]))
      (cmpxchgR8R8Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)) c) := by
  rintro s h hcode ⟨hp, hc⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cmpxchg_r8_r8_step s h [] (by simp)
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
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 8).read s =
        (Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 8).read s := by
      simpa using hc
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
      ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [Operand.read_afterStep]
      simp only [Operand.read_writeOutputs_self_merge, Operand.read_afterFetches,
        Operand.read_beforeFetch]
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 8).read s =
        (Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 8).read s := by
      simpa using hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
      ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _
      simp only [↓reduceIte]
      rw [Operand.read_afterStep]
      simp only [Operand.read_writeOutputs_self_merge, Operand.read_afterFetches,
        Operand.read_beforeFetch]
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_r8_r8_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg8 : (modrmReg modrm).toNat < 4)
    (hrm8 : (modrmRm modrm).toNat < 4) (c : Bool) :
    Triple (fun s => s.RIP = p ∧
        ((Operand.reg 0 : Operand 8).read s ==
          (Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 8).read s) = c)
      (codeRange p ([0x0F, 0xB0, modrm]))
      (Effect.post (cmpxchgR8R8Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)) c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpxchgR8R8Effect_components]; simp [Component.Covers]) _)
    (cmpxchg_r8_r8_effect_step p modrm hmod hreg8 hrm8 c)

theorem cmpxchg_r8_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    StepEffect (fun s => s.RIP = p ∧
        ((Operand.reg 0 : Operand 8).read s ==
          (Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 8).read s) = c)
      (codeRange p ([rex, 0x0F, 0xB0, modrm]))
      (cmpxchgR8R8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) c) := by
  rintro s h hcode ⟨hp, hc⟩
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cmpxchg_r8_r8_step s h [rex] (by simpa using hr.scanPrefix)
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
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 8).read s =
        (Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 8).read s := by
      simpa using hc
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
      ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [Operand.read_afterStep]
      simp only [Operand.read_writeOutputs_self_merge, Operand.read_afterFetches,
        Operand.read_beforeFetch]
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 8).read s =
        (Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 8).read s := by
      simpa using hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
      ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _
      simp only [↓reduceIte]
      rw [Operand.read_afterStep]
      simp only [Operand.read_writeOutputs_self_merge, Operand.read_afterFetches,
        Operand.read_beforeFetch]
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_r8_r8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    Triple (fun s => s.RIP = p ∧
        ((Operand.reg 0 : Operand 8).read s ==
          (Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 8).read s) = c)
      (codeRange p ([rex, 0x0F, 0xB0, modrm]))
      (Effect.post (cmpxchgR8R8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpxchgR8R8Effect_components]; simp [Component.Covers]) _)
    (cmpxchg_r8_r8_rex_effect_step p rex hr modrm hmod c)

def cmpxchgR8R8NoRexEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 3) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.byteReg dst).read s
  let b := (Operand.byteReg src).read s
  let acc := (Operand.reg 0 : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (if c then byteRegGpr dst else 0) : Operand 64),
      if c then mergeByteReg dst b ((Operand.reg (byteRegGpr dst) : Operand 64).read s)
      else mergeGPR 8 a ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (cmpSpec acc a)) }

@[simp] theorem cmpxchgR8R8NoRexEffect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 3)
    (c : Bool) (s : RamState) :
    (cmpxchgR8R8NoRexEffect p len dst src c s).components =
      [.reg (if c then byteRegGpr dst else 0), .flags, .rip] := rfl

theorem cmpxchg_r8_r8_norex_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    StepEffect (fun s => s.RIP = p ∧
        ((Operand.reg 0 : Operand 8).read s ==
          (Operand.byteReg (modrmRm modrm)).read s) = c)
      (codeRange p ([0x0F, 0xB0, modrm]))
      (cmpxchgR8R8NoRexEffect p 3 (modrmRm modrm) (modrmReg modrm) c) := by
  rintro s h hcode ⟨hp, hc⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cmpxchg_r8_r8_gpr8_step s h [] (by simp) (by simp) rfl rfl modrm hmod
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : Operand.gpr8 (gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm))
      (byteRex (scanContext s.DS (PrefixSegments.ofState s) [])) = Operand.byteReg (modrmRm modrm) := rfl
  have hsrc : Operand.gpr8 (gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 (modrmReg modrm))
      (byteRex (scanContext s.DS (PrefixSegments.ofState s) [])) = Operand.byteReg (modrmReg modrm) := rfl
  rw [hdst, hsrc] at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 8).read s = (Operand.byteReg (modrmRm modrm)).read s := by
      simpa using hc
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
      ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [Operand.read_afterStep]
      simp only [Operand.read_writeOutputs_self_merge, Operand.read_afterFetches,
        Operand.read_beforeFetch]
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 8).read s = (Operand.byteReg (modrmRm modrm)).read s := by
      simpa using hc
    simp only [eq_true heq, ↓reduceIte, writeOutputs_byteReg] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
      ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _
      simp only [↓reduceIte]
      rw [Operand.read_afterStep]
      simp only [Operand.read_writeOutputs_self, Operand.read_afterFetches,
        Operand.read_beforeFetch]
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_r8_r8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    Triple (fun s => s.RIP = p ∧
        ((Operand.reg 0 : Operand 8).read s ==
          (Operand.byteReg (modrmRm modrm)).read s) = c)
      (codeRange p ([0x0F, 0xB0, modrm]))
      (Effect.post (cmpxchgR8R8NoRexEffect p 3 (modrmRm modrm) (modrmReg modrm) c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpxchgR8R8NoRexEffect_components]; simp [Component.Covers]) _)
    (cmpxchg_r8_r8_norex_effect_step p modrm hmod c)

theorem cmpxchg_r8_r8_norex_triple [Bindings] (p : BitVec 64) (dst src : BitVec 3) (c : Bool) :
    Triple (fun s => s.RIP = p ∧
        ((Operand.reg 0 : Operand 8).read s == (Operand.byteReg dst).read s) = c)
      (codeRange p (encodeCmpxchgR8R8NoRex dst src))
      (Effect.post (cmpxchgR8R8NoRexEffect p 3 dst src c)) := by
  have h := cmpxchg_r8_r8_norex_triple_of_bytes p (modrmRegs src dst) (modrmMod_modrmRegs _ _) c
  rwa [modrmRm_modrmRegs, modrmReg_modrmRegs] at h

theorem cmpxchg_r8_r8_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) (c : Bool) :
    Triple (fun s => s.RIP = p ∧
        ((Operand.reg 0 : Operand 8).read s ==
          (Operand.reg (dst.setWidth 5) : Operand 8).read s) = c)
      (codeRange p (encodeCmpxchgR8R8 dst src))
      (Effect.post (cmpxchgR8R8Effect p (encodeCmpxchgR8R8 dst src).length (dst.setWidth 5)
        (src.setWidth 5) c)) := by
  rcases encodeCmpxchgR8R8_spec dst src with ⟨modrm, hbytes, hmod, hreg8, hrm8, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact cmpxchg_r8_r8_triple_of_bytes p modrm hmod hreg8 hrm8 c
  · rw [hbytes, ← hdst, ← hsrc]
    exact cmpxchg_r8_r8_rex_triple_of_bytes p rex hrex modrm hmod c

attribute [x86_compose] cmpxchgR8R8Effect

@[x86_local] theorem cmpxchgR8R8Effect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5}
    {c : Bool} :
    Effect.Local (cmpxchgR8R8Effect p len dst src c) := by
  effect_local [cmpxchgR8R8Effect]

attribute [x86_compose] cmpxchgR8R8NoRexEffect

@[x86_local] theorem cmpxchgR8R8NoRexEffect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 3}
    {c : Bool} :
    Effect.Local (cmpxchgR8R8NoRexEffect p len dst src c) := by
  effect_local [cmpxchgR8R8NoRexEffect]

end X86Proofs
