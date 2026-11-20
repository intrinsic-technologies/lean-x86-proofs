import X86Proofs.Instructions.Cmpxchg.Generated.RR.Step
import X86Proofs.Instructions.Cmpxchg.Generated.RR.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cmpxchgR64R64Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (c : Bool) (s : RamState) :
    Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := (Operand.reg src : Operand 64).read s
  let acc := (Operand.reg 0 : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (if c then dst else 0) : Operand 64),
      if c then b
      else a⟩]
    flags := some (.ofStatusFlags (cmpSpec acc a)) }

@[simp] theorem cmpxchgR64R64Effect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (c : Bool) (s : RamState) :
    (cmpxchgR64R64Effect p len dst src c s).components =
      [.reg (if c then dst else 0), .flags, .rip] := rfl

def cmpxchgR32R32Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (c : Bool) (s : RamState) :
    Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := (Operand.reg src : Operand 32).read s
  let acc := (Operand.reg 0 : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (if c then dst else 0) : Operand 64),
      if c then (b).setWidth 64
      else (a).setWidth 64⟩]
    flags := some (.ofStatusFlags (cmpSpec acc a)) }

@[simp] theorem cmpxchgR32R32Effect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (c : Bool) (s : RamState) :
    (cmpxchgR32R32Effect p len dst src c s).components =
      [.reg (if c then dst else 0), .flags, .rip] := rfl

def cmpxchgR16R16Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (c : Bool) (s : RamState) :
    Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := (Operand.reg src : Operand 16).read s
  let acc := (Operand.reg 0 : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (if c then dst else 0) : Operand 64),
      if c then mergeGPR 16 (b) ((Operand.reg dst : Operand 64).read s)
      else mergeGPR 16 (a) ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (cmpSpec acc a)) }

@[simp] theorem cmpxchgR16R16Effect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (c : Bool) (s : RamState) :
    (cmpxchgR16R16Effect p len dst src c s).components =
      [.reg (if c then dst else 0), .flags, .rip] := rfl

theorem cmpxchg_r64_r64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    StepEffect (fun s => s.RIP = p ∧
        ((Operand.reg 0 : Operand 64).read s ==
          (Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 64).read s) = c)
      (codeRange p ([rex, 0x0F, 0xB1, modrm]))
      (cmpxchgR64R64Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) c) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hc⟩
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cmpxchg_r_r_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) modrm hmod
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
  · have hne : ¬(Operand.reg 0 : Operand 64).read s =
        (Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 64).read s := by
      simpa using hc
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
      ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [Operand.read_afterStep]
      simp only [Operand.read_writeOutputs_self]
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 64).read s =
        (Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 64).read s := by
      simpa using hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
      ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _
      simp only [↓reduceIte]
      rw [Operand.read_afterStep]
      simp only [Operand.read_writeOutputs_self]
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_r64_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    Triple (fun s => s.RIP = p ∧
        ((Operand.reg 0 : Operand 64).read s ==
          (Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 64).read s) = c)
      (codeRange p ([rex, 0x0F, 0xB1, modrm]))
      (Effect.post (cmpxchgR64R64Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpxchgR64R64Effect_components]; simp [Component.Covers]) _)
    (cmpxchg_r64_r64_effect_step p rex hrex modrm hmod c)

theorem cmpxchg_r32_r32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    StepEffect (fun s => s.RIP = p ∧
        ((Operand.reg 0 : Operand 32).read s ==
          (Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 32).read s) = c)
      (codeRange p ([0x0F, 0xB1, modrm]))
      (cmpxchgR32R32Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)) c) := by
  rintro s h hcode ⟨hp, hc⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cmpxchg_r_r_step s h [] (by simp)
    (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl) modrm hmod
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
  · have hne : ¬(Operand.reg 0 : Operand 32).read s =
        (Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 32).read s := by
      simpa using hc
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
      ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [Operand.read_afterStep]
      simp only [Operand.read_writeOutputs_self32]
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 32).read s =
        (Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 32).read s := by
      simpa using hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
      ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _
      simp only [↓reduceIte]
      rw [Operand.read_afterStep]
      simp only [Operand.read_writeOutputs_self32]
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_r32_r32_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    Triple (fun s => s.RIP = p ∧
        ((Operand.reg 0 : Operand 32).read s ==
          (Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 32).read s) = c)
      (codeRange p ([0x0F, 0xB1, modrm]))
      (Effect.post (cmpxchgR32R32Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)) c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpxchgR32R32Effect_components]; simp [Component.Covers]) _)
    (cmpxchg_r32_r32_effect_step p modrm hmod c)

theorem cmpxchg_r32_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    StepEffect (fun s => s.RIP = p ∧
        ((Operand.reg 0 : Operand 32).read s ==
          (Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 32).read s) = c)
      (codeRange p ([rex, 0x0F, 0xB1, modrm]))
      (cmpxchgR32R32Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) c) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hc⟩
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cmpxchg_r_r_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) modrm hmod
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
  · have hne : ¬(Operand.reg 0 : Operand 32).read s =
        (Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 32).read s := by
      simpa using hc
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
      ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [Operand.read_afterStep]
      simp only [Operand.read_writeOutputs_self32]
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 32).read s =
        (Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 32).read s := by
      simpa using hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
      ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _
      simp only [↓reduceIte]
      rw [Operand.read_afterStep]
      simp only [Operand.read_writeOutputs_self32]
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_r32_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    Triple (fun s => s.RIP = p ∧
        ((Operand.reg 0 : Operand 32).read s ==
          (Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 32).read s) = c)
      (codeRange p ([rex, 0x0F, 0xB1, modrm]))
      (Effect.post (cmpxchgR32R32Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpxchgR32R32Effect_components]; simp [Component.Covers]) _)
    (cmpxchg_r32_r32_rex_effect_step p rex hrex modrm hmod c)

theorem cmpxchg_r16_r16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    StepEffect (fun s => s.RIP = p ∧
        ((Operand.reg 0 : Operand 16).read s ==
          (Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 16).read s) = c)
      (codeRange p ([0x66, 0x0F, 0xB1, modrm]))
      (cmpxchgR16R16Effect p 4 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)) c) := by
  rintro s h hcode ⟨hp, hc⟩
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cmpxchg_r16_r16_step s h [0x66] (by simpa using scanPrefix_66)
    (by simp)
    (by exact rfl)
    (by rfl) (by rfl) modrm hmod
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  rw [hdst, hsrc] at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 16).read s =
        (Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 16).read s := by
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
  · have heq : (Operand.reg 0 : Operand 16).read s =
        (Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 16).read s := by
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

theorem cmpxchg_r16_r16_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    Triple (fun s => s.RIP = p ∧
        ((Operand.reg 0 : Operand 16).read s ==
          (Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 16).read s) = c)
      (codeRange p ([0x66, 0x0F, 0xB1, modrm]))
      (Effect.post (cmpxchgR16R16Effect p 4 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)) c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpxchgR16R16Effect_components]; simp [Component.Covers]) _)
    (cmpxchg_r16_r16_effect_step p modrm hmod c)

theorem cmpxchg_r16_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    StepEffect (fun s => s.RIP = p ∧
        ((Operand.reg 0 : Operand 16).read s ==
          (Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 16).read s) = c)
      (codeRange p ([0x66, rex, 0x0F, 0xB1, modrm]))
      (cmpxchgR16R16Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) c) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hc⟩
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cmpxchg_r16_r16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix])
    (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl) modrm hmod
    hcode.bytesAt hlow
  simp only [scanContext_66_rex _ _ hr] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_b4
      (oszRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  have hsrc : gprNumber (oszRexContext s.DS rex.toBitVec).rex_r4
      (oszRexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  rw [hdst, hsrc] at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 16).read s =
        (Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 16).read s := by
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
  · have heq : (Operand.reg 0 : Operand 16).read s =
        (Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 16).read s := by
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

theorem cmpxchg_r16_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    Triple (fun s => s.RIP = p ∧
        ((Operand.reg 0 : Operand 16).read s ==
          (Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 16).read s) = c)
      (codeRange p ([0x66, rex, 0x0F, 0xB1, modrm]))
      (Effect.post (cmpxchgR16R16Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpxchgR16R16Effect_components]; simp [Component.Covers]) _)
    (cmpxchg_r16_r16_rex_effect_step p rex hrex modrm hmod c)

theorem cmpxchg_r64_r64_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) (c : Bool) :
    Triple (fun s => s.RIP = p ∧
        ((Operand.reg 0 : Operand 64).read s ==
          (Operand.reg (dst.setWidth 5) : Operand 64).read s) = c)
      (codeRange p (encodeCmpxchgR64R64 dst src))
      (Effect.post (cmpxchgR64R64Effect p (encodeCmpxchgR64R64 dst src).length (dst.setWidth 5)
        (src.setWidth 5) c)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeCmpxchgR64R64_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact cmpxchg_r64_r64_triple_of_bytes p rex hrex modrm hmod c

theorem cmpxchg_r32_r32_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) (c : Bool) :
    Triple (fun s => s.RIP = p ∧
        ((Operand.reg 0 : Operand 32).read s ==
          (Operand.reg (dst.setWidth 5) : Operand 32).read s) = c)
      (codeRange p (encodeCmpxchgR32R32 dst src))
      (Effect.post (cmpxchgR32R32Effect p (encodeCmpxchgR32R32 dst src).length (dst.setWidth 5)
        (src.setWidth 5) c)) := by
  rcases encodeCmpxchgR32R32_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact cmpxchg_r32_r32_triple_of_bytes p modrm hmod c
  · rw [hbytes, ← hdst, ← hsrc]
    exact cmpxchg_r32_r32_rex_triple_of_bytes p rex hrex modrm hmod c

theorem cmpxchg_r16_r16_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) (c : Bool) :
    Triple (fun s => s.RIP = p ∧
        ((Operand.reg 0 : Operand 16).read s ==
          (Operand.reg (dst.setWidth 5) : Operand 16).read s) = c)
      (codeRange p (encodeCmpxchgR16R16 dst src))
      (Effect.post (cmpxchgR16R16Effect p (encodeCmpxchgR16R16 dst src).length (dst.setWidth 5)
        (src.setWidth 5) c)) := by
  rcases encodeCmpxchgR16R16_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact cmpxchg_r16_r16_triple_of_bytes p modrm hmod c
  · rw [hbytes, ← hdst, ← hsrc]
    exact cmpxchg_r16_r16_rex_triple_of_bytes p rex hrex modrm hmod c

attribute [x86_compose] cmpxchgR64R64Effect cmpxchgR32R32Effect cmpxchgR16R16Effect

@[x86_local] theorem cmpxchgR64R64Effect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5}
    {c : Bool} :
    Effect.Local (cmpxchgR64R64Effect p len dst src c) := by
  effect_local [cmpxchgR64R64Effect]

@[x86_local] theorem cmpxchgR32R32Effect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5}
    {c : Bool} :
    Effect.Local (cmpxchgR32R32Effect p len dst src c) := by
  effect_local [cmpxchgR32R32Effect]

@[x86_local] theorem cmpxchgR16R16Effect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5}
    {c : Bool} :
    Effect.Local (cmpxchgR16R16Effect p len dst src c) := by
  effect_local [cmpxchgR16R16Effect]

end X86Proofs
