import X86Proofs.Instructions.Stos.Generated.Str.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def stosqEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rdi, rdi.read s + 8⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 64), (Operand.reg 0 : Operand 64).read s⟩]

@[simp] theorem stosqEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (stosqEffect p len s).components = [.reg 7, .mem (rdi.read s) 8, .rip] := by
  simp [stosqEffect, Effect.components]

theorem stosq_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (StosPre p 2 8) (codeRange p [rex, 0xAB]) (stosqEffect p 2) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hdf, hwr, _⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := stosq_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    hdf hcode.bytesAt hlow hwr
  exact ⟨_, hstep, ReadyToStep.afterStep_stos h _ _ _ hwr,
    ⟨afterStep_stos_rip h _ _ _, ⟨Operand.read_afterStep_stos_rdi _ _ _ _,
      Operand.read_afterStep_stos_mem _ _ (n := 64) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_stos _ _ _ _⟩⟩

theorem stosq_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (StosPre p 2 8) (codeRange p [rex, 0xAB]) (Effect.post (stosqEffect p 2)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (stosq_effect_step p rex hrex)

theorem stosq_triple [Bindings] (p : BitVec 64) :
    Triple (StosPre p 2 8) (codeRange p [0x48, 0xAB]) (Effect.post (stosqEffect p 2)) :=
  stosq_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide)

def stosdEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rdi, rdi.read s + 4⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 32), (Operand.reg 0 : Operand 32).read s⟩]

@[simp] theorem stosdEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (stosdEffect p len s).components = [.reg 7, .mem (rdi.read s) 4, .rip] := by
  simp [stosdEffect, Effect.components]

theorem stosd_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (StosPre p 1 4) (codeRange p [0xAB]) (stosdEffect p 1) := by
  rintro s h hcode ⟨hp, hdf, hwr, _⟩
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := stosd_step s h [] (by simp) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hwr
  exact ⟨_, hstep, ReadyToStep.afterStep_stos h _ _ _ hwr,
    ⟨afterStep_stos_rip h _ _ _, ⟨Operand.read_afterStep_stos_rdi _ _ _ _,
      Operand.read_afterStep_stos_mem _ _ (n := 32) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_stos _ _ _ _⟩⟩

theorem stosd_triple [Bindings] (p : BitVec 64) :
    Triple (StosPre p 1 4) (codeRange p [0xAB]) (Effect.post (stosdEffect p 1)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (stosd_effect_step p)

def stoswEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rdi, rdi.read s + 2⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 16), (Operand.reg 0 : Operand 16).read s⟩]

@[simp] theorem stoswEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (stoswEffect p len s).components = [.reg 7, .mem (rdi.read s) 2, .rip] := by
  simp [stoswEffect, Effect.components]

theorem stosw_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (StosPre p 2 2) (codeRange p [0x66, 0xAB]) (stoswEffect p 2) := by
  rintro s h hcode ⟨hp, hdf, hwr, _⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := stosw_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hwr
  exact ⟨_, hstep, ReadyToStep.afterStep_stos h _ _ _ hwr,
    ⟨afterStep_stos_rip h _ _ _, ⟨Operand.read_afterStep_stos_rdi _ _ _ _,
      Operand.read_afterStep_stos_mem _ _ (n := 16) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_stos _ _ _ _⟩⟩

theorem stosw_triple [Bindings] (p : BitVec 64) :
    Triple (StosPre p 2 2) (codeRange p [0x66, 0xAB]) (Effect.post (stoswEffect p 2)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (stosw_effect_step p)

def stosbEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rdi, rdi.read s + 1⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 8), (Operand.reg 0 : Operand 8).read s⟩]

@[simp] theorem stosbEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (stosbEffect p len s).components = [.reg 7, .mem (rdi.read s) 1, .rip] := by
  simp [stosbEffect, Effect.components]

theorem stosb_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (StosPre p 1 1) (codeRange p [0xAA]) (stosbEffect p 1) := by
  rintro s h hcode ⟨hp, hdf, hwr, _⟩
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := stosb_step s h [] (by simp) (by simp)
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hwr
  exact ⟨_, hstep, ReadyToStep.afterStep_stos h _ _ _ hwr,
    ⟨afterStep_stos_rip h _ _ _, ⟨Operand.read_afterStep_stos_rdi _ _ _ _,
      Operand.read_afterStep_stos_mem _ _ (n := 8) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_stos _ _ _ _⟩⟩

theorem stosb_triple [Bindings] (p : BitVec 64) :
    Triple (StosPre p 1 1) (codeRange p [0xAA]) (Effect.post (stosbEffect p 1)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (stosb_effect_step p)

theorem stosq_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (fun s => StosPre p 3 8 s ∧ (rdi.read s).toNat + 8 < 2^32) (codeRange p [0x67, rex, 0xAB])
      (stosqEffect p 3) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hdf, hwr, _⟩, hdl⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := stosq_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    hdf hcode.bytesAt hlow hwr hdl
  exact ⟨_, hstep, ReadyToStep.afterStep_stos h _ _ _ hwr,
    ⟨afterStep_stos_rip h _ _ _, ⟨Operand.read_afterStep_stos_rdi _ _ _ _,
      Operand.read_afterStep_stos_mem _ _ (n := 64) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_stos _ _ _ _⟩⟩

theorem stosq_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (fun s => StosPre p 3 8 s ∧ (rdi.read s).toNat + 8 < 2^32) (codeRange p [0x67, rex, 0xAB])
      (Effect.post (stosqEffect p 3)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.1.code rfl)
    (stosq_a32_effect_step p rex hrex)

theorem stosq_a32_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => StosPre p 3 8 s ∧ (rdi.read s).toNat + 8 < 2^32) (codeRange p [0x67, 0x48, 0xAB])
      (Effect.post (stosqEffect p 3)) :=
  stosq_a32_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide)

theorem stosd_a32_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => StosPre p 2 4 s ∧ (rdi.read s).toNat + 4 < 2^32) (codeRange p [0x67, 0xAB])
      (stosdEffect p 2) := by
  rintro s h hcode ⟨⟨hp, hdf, hwr, _⟩, hdl⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := stosd_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    hdf hcode.bytesAt hlow hwr hdl
  exact ⟨_, hstep, ReadyToStep.afterStep_stos h _ _ _ hwr,
    ⟨afterStep_stos_rip h _ _ _, ⟨Operand.read_afterStep_stos_rdi _ _ _ _,
      Operand.read_afterStep_stos_mem _ _ (n := 32) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_stos _ _ _ _⟩⟩

theorem stosd_a32_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => StosPre p 2 4 s ∧ (rdi.read s).toNat + 4 < 2^32) (codeRange p [0x67, 0xAB])
      (Effect.post (stosdEffect p 2)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.1.code rfl)
    (stosd_a32_effect_step p)

theorem stosw_a32_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => StosPre p 3 2 s ∧ (rdi.read s).toNat + 2 < 2^32) (codeRange p [0x67, 0x66, 0xAB])
      (stoswEffect p 3) := by
  rintro s h hcode ⟨⟨hp, hdf, hwr, _⟩, hdl⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := stosw_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    hdf hcode.bytesAt hlow hwr hdl
  exact ⟨_, hstep, ReadyToStep.afterStep_stos h _ _ _ hwr,
    ⟨afterStep_stos_rip h _ _ _, ⟨Operand.read_afterStep_stos_rdi _ _ _ _,
      Operand.read_afterStep_stos_mem _ _ (n := 16) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_stos _ _ _ _⟩⟩

theorem stosw_a32_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => StosPre p 3 2 s ∧ (rdi.read s).toNat + 2 < 2^32) (codeRange p [0x67, 0x66, 0xAB])
      (Effect.post (stoswEffect p 3)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.1.code rfl)
    (stosw_a32_effect_step p)

theorem stosb_a32_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => StosPre p 2 1 s ∧ (rdi.read s).toNat + 1 < 2^32) (codeRange p [0x67, 0xAA])
      (stosbEffect p 2) := by
  rintro s h hcode ⟨⟨hp, hdf, hwr, _⟩, hdl⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := stosb_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    hdf hcode.bytesAt hlow hwr hdl
  exact ⟨_, hstep, ReadyToStep.afterStep_stos h _ _ _ hwr,
    ⟨afterStep_stos_rip h _ _ _, ⟨Operand.read_afterStep_stos_rdi _ _ _ _,
      Operand.read_afterStep_stos_mem _ _ (n := 8) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_stos _ _ _ _⟩⟩

theorem stosb_a32_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => StosPre p 2 1 s ∧ (rdi.read s).toNat + 1 < 2^32) (codeRange p [0x67, 0xAA])
      (Effect.post (stosbEffect p 2)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.1.code rfl)
    (stosb_a32_effect_step p)

attribute [x86_compose] stosqEffect stosdEffect stoswEffect stosbEffect

@[x86_local] theorem stosqEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (stosqEffect p len) := by
  effect_local [stosqEffect]

@[x86_local] theorem stosdEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (stosdEffect p len) := by
  effect_local [stosdEffect]

@[x86_local] theorem stoswEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (stoswEffect p len) := by
  effect_local [stoswEffect]

@[x86_local] theorem stosbEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (stosbEffect p len) := by
  effect_local [stosbEffect]

end X86Proofs
