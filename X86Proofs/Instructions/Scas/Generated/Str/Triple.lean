import X86Proofs.Instructions.Scas.Generated.Str.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def scasqEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rdi, rdi.read s + 8⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 64).read s)
    ((Operand.mem (rdi.read s) : Operand 64).read s)))

@[simp] theorem scasqEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (scasqEffect p len s).components = [.reg 7, .flags, .rip] := by
  simp [scasqEffect, Effect.components]

theorem scasq_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (ScasPre p 8) (codeRange p [rex, 0xAF]) (scasqEffect p 2) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hdf, hrd⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := scasq_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    hdf hcode.bytesAt hlow hrd
  exact ⟨_, hstep, ReadyToStep.afterStep_scas h _ _ _,
    ⟨afterStep_scas_rip h _ _ _, Operand.read_afterStep_scas_rdi _ _ _ _,
      (by
        simp only [Effect.FlagsHold, scasqEffect]
        rw [afterStep_scas_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_scas _ _ _ _⟩⟩

theorem scasq_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (ScasPre p 8) (codeRange p [rex, 0xAF]) (Effect.post (scasqEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [scasqEffect_components]; simp [Component.Covers]) _)
    (scasq_effect_step p rex hrex)

theorem scasq_triple [Bindings] (p : BitVec 64) :
    Triple (ScasPre p 8) (codeRange p [0x48, 0xAF]) (Effect.post (scasqEffect p 2)) :=
  scasq_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide)

def scasdEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rdi, rdi.read s + 4⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 32).read s)
    ((Operand.mem (rdi.read s) : Operand 32).read s)))

@[simp] theorem scasdEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (scasdEffect p len s).components = [.reg 7, .flags, .rip] := by
  simp [scasdEffect, Effect.components]

theorem scasd_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (ScasPre p 4) (codeRange p [0xAF]) (scasdEffect p 1) := by
  rintro s h hcode ⟨hp, hdf, hrd⟩
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := scasd_step s h [] (by simp) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hrd
  exact ⟨_, hstep, ReadyToStep.afterStep_scas h _ _ _,
    ⟨afterStep_scas_rip h _ _ _, Operand.read_afterStep_scas_rdi _ _ _ _,
      (by
        simp only [Effect.FlagsHold, scasdEffect]
        rw [afterStep_scas_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_scas _ _ _ _⟩⟩

theorem scasd_triple [Bindings] (p : BitVec 64) :
    Triple (ScasPre p 4) (codeRange p [0xAF]) (Effect.post (scasdEffect p 1)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [scasdEffect_components]; simp [Component.Covers]) _)
    (scasd_effect_step p)

def scaswEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rdi, rdi.read s + 2⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 16).read s)
    ((Operand.mem (rdi.read s) : Operand 16).read s)))

@[simp] theorem scaswEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (scaswEffect p len s).components = [.reg 7, .flags, .rip] := by
  simp [scaswEffect, Effect.components]

theorem scasw_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (ScasPre p 2) (codeRange p [0x66, 0xAF]) (scaswEffect p 2) := by
  rintro s h hcode ⟨hp, hdf, hrd⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := scasw_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hrd
  exact ⟨_, hstep, ReadyToStep.afterStep_scas h _ _ _,
    ⟨afterStep_scas_rip h _ _ _, Operand.read_afterStep_scas_rdi _ _ _ _,
      (by
        simp only [Effect.FlagsHold, scaswEffect]
        rw [afterStep_scas_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_scas _ _ _ _⟩⟩

theorem scasw_triple [Bindings] (p : BitVec 64) :
    Triple (ScasPre p 2) (codeRange p [0x66, 0xAF]) (Effect.post (scaswEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [scaswEffect_components]; simp [Component.Covers]) _)
    (scasw_effect_step p)

def scasbEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rdi, rdi.read s + 1⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 8).read s)
    ((Operand.mem (rdi.read s) : Operand 8).read s)))

@[simp] theorem scasbEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (scasbEffect p len s).components = [.reg 7, .flags, .rip] := by
  simp [scasbEffect, Effect.components]

theorem scasb_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (ScasPre p 1) (codeRange p [0xAE]) (scasbEffect p 1) := by
  rintro s h hcode ⟨hp, hdf, hrd⟩
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := scasb_step s h [] (by simp) (by simp)
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hrd
  exact ⟨_, hstep, ReadyToStep.afterStep_scas h _ _ _,
    ⟨afterStep_scas_rip h _ _ _, Operand.read_afterStep_scas_rdi _ _ _ _,
      (by
        simp only [Effect.FlagsHold, scasbEffect]
        rw [afterStep_scas_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_scas _ _ _ _⟩⟩

theorem scasb_triple [Bindings] (p : BitVec 64) :
    Triple (ScasPre p 1) (codeRange p [0xAE]) (Effect.post (scasbEffect p 1)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [scasbEffect_components]; simp [Component.Covers]) _)
    (scasb_effect_step p)

theorem scasq_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (fun s => ScasPre p 8 s ∧ (rdi.read s).toNat + 8 < 2^32) (codeRange p [0x67, rex, 0xAF])
      (scasqEffect p 3) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hdf, hrd⟩, hdl⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := scasq_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    hdf hcode.bytesAt hlow hrd hdl
  exact ⟨_, hstep, ReadyToStep.afterStep_scas h _ _ _,
    ⟨afterStep_scas_rip h _ _ _, Operand.read_afterStep_scas_rdi _ _ _ _,
      (by
        simp only [Effect.FlagsHold, scasqEffect]
        rw [afterStep_scas_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_scas _ _ _ _⟩⟩

theorem scasq_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (fun s => ScasPre p 8 s ∧ (rdi.read s).toNat + 8 < 2^32) (codeRange p [0x67, rex, 0xAF])
      (Effect.post (scasqEffect p 3)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [scasqEffect_components]; simp [Component.Covers]) _)
    (scasq_a32_effect_step p rex hrex)

theorem scasq_a32_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => ScasPre p 8 s ∧ (rdi.read s).toNat + 8 < 2^32) (codeRange p [0x67, 0x48, 0xAF])
      (Effect.post (scasqEffect p 3)) :=
  scasq_a32_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide)

theorem scasd_a32_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => ScasPre p 4 s ∧ (rdi.read s).toNat + 4 < 2^32) (codeRange p [0x67, 0xAF])
      (scasdEffect p 2) := by
  rintro s h hcode ⟨⟨hp, hdf, hrd⟩, hdl⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := scasd_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    hdf hcode.bytesAt hlow hrd hdl
  exact ⟨_, hstep, ReadyToStep.afterStep_scas h _ _ _,
    ⟨afterStep_scas_rip h _ _ _, Operand.read_afterStep_scas_rdi _ _ _ _,
      (by
        simp only [Effect.FlagsHold, scasdEffect]
        rw [afterStep_scas_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_scas _ _ _ _⟩⟩

theorem scasd_a32_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => ScasPre p 4 s ∧ (rdi.read s).toNat + 4 < 2^32) (codeRange p [0x67, 0xAF])
      (Effect.post (scasdEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [scasdEffect_components]; simp [Component.Covers]) _)
    (scasd_a32_effect_step p)

theorem scasw_a32_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => ScasPre p 2 s ∧ (rdi.read s).toNat + 2 < 2^32) (codeRange p [0x67, 0x66, 0xAF])
      (scaswEffect p 3) := by
  rintro s h hcode ⟨⟨hp, hdf, hrd⟩, hdl⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := scasw_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    hdf hcode.bytesAt hlow hrd hdl
  exact ⟨_, hstep, ReadyToStep.afterStep_scas h _ _ _,
    ⟨afterStep_scas_rip h _ _ _, Operand.read_afterStep_scas_rdi _ _ _ _,
      (by
        simp only [Effect.FlagsHold, scaswEffect]
        rw [afterStep_scas_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_scas _ _ _ _⟩⟩

theorem scasw_a32_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => ScasPre p 2 s ∧ (rdi.read s).toNat + 2 < 2^32) (codeRange p [0x67, 0x66, 0xAF])
      (Effect.post (scaswEffect p 3)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [scaswEffect_components]; simp [Component.Covers]) _)
    (scasw_a32_effect_step p)

theorem scasb_a32_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => ScasPre p 1 s ∧ (rdi.read s).toNat + 1 < 2^32) (codeRange p [0x67, 0xAE])
      (scasbEffect p 2) := by
  rintro s h hcode ⟨⟨hp, hdf, hrd⟩, hdl⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := scasb_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    hdf hcode.bytesAt hlow hrd hdl
  exact ⟨_, hstep, ReadyToStep.afterStep_scas h _ _ _,
    ⟨afterStep_scas_rip h _ _ _, Operand.read_afterStep_scas_rdi _ _ _ _,
      (by
        simp only [Effect.FlagsHold, scasbEffect]
        rw [afterStep_scas_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_scas _ _ _ _⟩⟩

theorem scasb_a32_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => ScasPre p 1 s ∧ (rdi.read s).toNat + 1 < 2^32) (codeRange p [0x67, 0xAE])
      (Effect.post (scasbEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [scasbEffect_components]; simp [Component.Covers]) _)
    (scasb_a32_effect_step p)

attribute [x86_compose] scasqEffect scasdEffect scaswEffect scasbEffect

@[x86_local] theorem scasqEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (scasqEffect p len) := by
  effect_local [scasqEffect]

@[x86_local] theorem scasdEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (scasdEffect p len) := by
  effect_local [scasdEffect]

@[x86_local] theorem scaswEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (scaswEffect p len) := by
  effect_local [scaswEffect]

@[x86_local] theorem scasbEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (scasbEffect p len) := by
  effect_local [scasbEffect]

end X86Proofs
