import X86Proofs.Instructions.Scas.Generated.StrDown.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def scasqDownEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rdi, rdi.read s - 8⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 64).read s)
    ((Operand.mem (rdi.read s) : Operand 64).read s)))

@[simp] theorem scasqDownEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (scasqDownEffect p len s).components = [.reg 7, .flags, .rip] := by
  simp [scasqDownEffect, Effect.components]

theorem scasq_down_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (ScasDownPre p 8) (codeRange p [rex, 0xAF]) (scasqDownEffect p 2) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hdf, hrd⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := scasq_down_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    hdf hcode.bytesAt hlow hrd
  exact ⟨_, hstep, ReadyToStep.afterStep_scas_down h _ _ _,
    ⟨afterStep_scas_down_rip h _ _ _, Operand.read_afterStep_scas_down_rdi _ _ _ _,
      (by
        simp only [Effect.FlagsHold, scasqDownEffect]
        rw [afterStep_scas_down_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_scas_down _ _ _ _⟩⟩

theorem scasq_down_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (ScasDownPre p 8) (codeRange p [rex, 0xAF]) (Effect.post (scasqDownEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [scasqDownEffect_components]; simp [Component.Covers]) _)
    (scasq_down_effect_step p rex hrex)

theorem scasq_down_triple [Bindings] (p : BitVec 64) :
    Triple (ScasDownPre p 8) (codeRange p [0x48, 0xAF]) (Effect.post (scasqDownEffect p 2)) :=
  scasq_down_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide)

def scasdDownEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rdi, rdi.read s - 4⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 32).read s)
    ((Operand.mem (rdi.read s) : Operand 32).read s)))

@[simp] theorem scasdDownEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (scasdDownEffect p len s).components = [.reg 7, .flags, .rip] := by
  simp [scasdDownEffect, Effect.components]

theorem scasd_down_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (ScasDownPre p 4) (codeRange p [0xAF]) (scasdDownEffect p 1) := by
  rintro s h hcode ⟨hp, hdf, hrd⟩
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := scasd_down_step s h [] (by simp) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hrd
  exact ⟨_, hstep, ReadyToStep.afterStep_scas_down h _ _ _,
    ⟨afterStep_scas_down_rip h _ _ _, Operand.read_afterStep_scas_down_rdi _ _ _ _,
      (by
        simp only [Effect.FlagsHold, scasdDownEffect]
        rw [afterStep_scas_down_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_scas_down _ _ _ _⟩⟩

theorem scasd_down_triple [Bindings] (p : BitVec 64) :
    Triple (ScasDownPre p 4) (codeRange p [0xAF]) (Effect.post (scasdDownEffect p 1)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [scasdDownEffect_components]; simp [Component.Covers]) _)
    (scasd_down_effect_step p)

def scaswDownEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rdi, rdi.read s - 2⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 16).read s)
    ((Operand.mem (rdi.read s) : Operand 16).read s)))

@[simp] theorem scaswDownEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (scaswDownEffect p len s).components = [.reg 7, .flags, .rip] := by
  simp [scaswDownEffect, Effect.components]

theorem scasw_down_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (ScasDownPre p 2) (codeRange p [0x66, 0xAF]) (scaswDownEffect p 2) := by
  rintro s h hcode ⟨hp, hdf, hrd⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := scasw_down_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hrd
  exact ⟨_, hstep, ReadyToStep.afterStep_scas_down h _ _ _,
    ⟨afterStep_scas_down_rip h _ _ _, Operand.read_afterStep_scas_down_rdi _ _ _ _,
      (by
        simp only [Effect.FlagsHold, scaswDownEffect]
        rw [afterStep_scas_down_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_scas_down _ _ _ _⟩⟩

theorem scasw_down_triple [Bindings] (p : BitVec 64) :
    Triple (ScasDownPre p 2) (codeRange p [0x66, 0xAF]) (Effect.post (scaswDownEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [scaswDownEffect_components]; simp [Component.Covers]) _)
    (scasw_down_effect_step p)

def scasbDownEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rdi, rdi.read s - 1⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 8).read s)
    ((Operand.mem (rdi.read s) : Operand 8).read s)))

@[simp] theorem scasbDownEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (scasbDownEffect p len s).components = [.reg 7, .flags, .rip] := by
  simp [scasbDownEffect, Effect.components]

theorem scasb_down_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (ScasDownPre p 1) (codeRange p [0xAE]) (scasbDownEffect p 1) := by
  rintro s h hcode ⟨hp, hdf, hrd⟩
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := scasb_down_step s h [] (by simp) (by simp)
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hrd
  exact ⟨_, hstep, ReadyToStep.afterStep_scas_down h _ _ _,
    ⟨afterStep_scas_down_rip h _ _ _, Operand.read_afterStep_scas_down_rdi _ _ _ _,
      (by
        simp only [Effect.FlagsHold, scasbDownEffect]
        rw [afterStep_scas_down_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_scas_down _ _ _ _⟩⟩

theorem scasb_down_triple [Bindings] (p : BitVec 64) :
    Triple (ScasDownPre p 1) (codeRange p [0xAE]) (Effect.post (scasbDownEffect p 1)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [scasbDownEffect_components]; simp [Component.Covers]) _)
    (scasb_down_effect_step p)

attribute [x86_compose] scasqDownEffect scasdDownEffect scaswDownEffect scasbDownEffect

@[x86_local] theorem scasqDownEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (scasqDownEffect p len) := by
  effect_local [scasqDownEffect]

@[x86_local] theorem scasdDownEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (scasdDownEffect p len) := by
  effect_local [scasdDownEffect]

@[x86_local] theorem scaswDownEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (scaswDownEffect p len) := by
  effect_local [scaswDownEffect]

@[x86_local] theorem scasbDownEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (scasbDownEffect p len) := by
  effect_local [scasbDownEffect]

end X86Proofs
