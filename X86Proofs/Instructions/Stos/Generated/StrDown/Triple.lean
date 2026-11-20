import X86Proofs.Instructions.Stos.Generated.StrDown.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def stosqDownEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rdi, rdi.read s - 8⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 64), (Operand.reg 0 : Operand 64).read s⟩]

@[simp] theorem stosqDownEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (stosqDownEffect p len s).components = [.reg 7, .mem (rdi.read s) 8, .rip] := by
  simp [stosqDownEffect, Effect.components]

theorem stosq_down_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (StosDownPre p 2 8) (codeRange p [rex, 0xAB]) (stosqDownEffect p 2) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hdf, hwr, _⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := stosq_down_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    hdf hcode.bytesAt hlow hwr
  exact ⟨_, hstep, ReadyToStep.afterStep_stos_down h _ _ _ hwr,
    ⟨afterStep_stos_down_rip h _ _ _, ⟨Operand.read_afterStep_stos_down_rdi _ _ _ _,
      Operand.read_afterStep_stos_down_mem _ _ (n := 64) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_stos_down _ _ _ _⟩⟩

theorem stosq_down_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (StosDownPre p 2 8) (codeRange p [rex, 0xAB]) (Effect.post (stosqDownEffect p 2)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (stosq_down_effect_step p rex hrex)

theorem stosq_down_triple [Bindings] (p : BitVec 64) :
    Triple (StosDownPre p 2 8) (codeRange p [0x48, 0xAB]) (Effect.post (stosqDownEffect p 2)) :=
  stosq_down_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide)

def stosdDownEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rdi, rdi.read s - 4⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 32), (Operand.reg 0 : Operand 32).read s⟩]

@[simp] theorem stosdDownEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (stosdDownEffect p len s).components = [.reg 7, .mem (rdi.read s) 4, .rip] := by
  simp [stosdDownEffect, Effect.components]

theorem stosd_down_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (StosDownPre p 1 4) (codeRange p [0xAB]) (stosdDownEffect p 1) := by
  rintro s h hcode ⟨hp, hdf, hwr, _⟩
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := stosd_down_step s h [] (by simp) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hwr
  exact ⟨_, hstep, ReadyToStep.afterStep_stos_down h _ _ _ hwr,
    ⟨afterStep_stos_down_rip h _ _ _, ⟨Operand.read_afterStep_stos_down_rdi _ _ _ _,
      Operand.read_afterStep_stos_down_mem _ _ (n := 32) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_stos_down _ _ _ _⟩⟩

theorem stosd_down_triple [Bindings] (p : BitVec 64) :
    Triple (StosDownPre p 1 4) (codeRange p [0xAB]) (Effect.post (stosdDownEffect p 1)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (stosd_down_effect_step p)

def stoswDownEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rdi, rdi.read s - 2⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 16), (Operand.reg 0 : Operand 16).read s⟩]

@[simp] theorem stoswDownEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (stoswDownEffect p len s).components = [.reg 7, .mem (rdi.read s) 2, .rip] := by
  simp [stoswDownEffect, Effect.components]

theorem stosw_down_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (StosDownPre p 2 2) (codeRange p [0x66, 0xAB]) (stoswDownEffect p 2) := by
  rintro s h hcode ⟨hp, hdf, hwr, _⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := stosw_down_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hwr
  exact ⟨_, hstep, ReadyToStep.afterStep_stos_down h _ _ _ hwr,
    ⟨afterStep_stos_down_rip h _ _ _, ⟨Operand.read_afterStep_stos_down_rdi _ _ _ _,
      Operand.read_afterStep_stos_down_mem _ _ (n := 16) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_stos_down _ _ _ _⟩⟩

theorem stosw_down_triple [Bindings] (p : BitVec 64) :
    Triple (StosDownPre p 2 2) (codeRange p [0x66, 0xAB]) (Effect.post (stoswDownEffect p 2)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (stosw_down_effect_step p)

def stosbDownEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rdi, rdi.read s - 1⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 8), (Operand.reg 0 : Operand 8).read s⟩]

@[simp] theorem stosbDownEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (stosbDownEffect p len s).components = [.reg 7, .mem (rdi.read s) 1, .rip] := by
  simp [stosbDownEffect, Effect.components]

theorem stosb_down_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (StosDownPre p 1 1) (codeRange p [0xAA]) (stosbDownEffect p 1) := by
  rintro s h hcode ⟨hp, hdf, hwr, _⟩
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := stosb_down_step s h [] (by simp) (by simp)
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hwr
  exact ⟨_, hstep, ReadyToStep.afterStep_stos_down h _ _ _ hwr,
    ⟨afterStep_stos_down_rip h _ _ _, ⟨Operand.read_afterStep_stos_down_rdi _ _ _ _,
      Operand.read_afterStep_stos_down_mem _ _ (n := 8) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_stos_down _ _ _ _⟩⟩

theorem stosb_down_triple [Bindings] (p : BitVec 64) :
    Triple (StosDownPre p 1 1) (codeRange p [0xAA]) (Effect.post (stosbDownEffect p 1)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (stosb_down_effect_step p)

attribute [x86_compose] stosqDownEffect stosdDownEffect stoswDownEffect stosbDownEffect

@[x86_local] theorem stosqDownEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (stosqDownEffect p len) := by
  effect_local [stosqDownEffect]

@[x86_local] theorem stosdDownEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (stosdDownEffect p len) := by
  effect_local [stosdDownEffect]

@[x86_local] theorem stoswDownEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (stoswDownEffect p len) := by
  effect_local [stoswDownEffect]

@[x86_local] theorem stosbDownEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (stosbDownEffect p len) := by
  effect_local [stosbDownEffect]

end X86Proofs
