import X86Proofs.Instructions.PushSreg.Generated.Gs.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def pushGsEffect (p : BitVec 64) (len : Nat) (sel : BitVec 16) : RamState → Effect :=
  pushEffect (fun _ => p + BitVec.ofNat 64 len) fun _ => pushsregSpec 64 sel

@[simp] theorem pushGsEffect_components (p : BitVec 64) (len : Nat) (sel : BitVec 16) (s : RamState) :
    (pushGsEffect p len sel s).components = [.reg 4, .mem (pushAddr s) 8, .rip] :=
  pushEffect_components _ _ s

theorem push_gs_effect_step [Bindings] (p : BitVec 64) (sel : BitVec 16) :
    StepEffect (fun s => PushPre p 2 s ∧ s.GS.selector = sel)
      (codeRange p [0x0F, 0xA8]) (pushGsEffect p 2 sel) := by
  rintro s h hcode ⟨hpre, hsel⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := push_gs_step s h [] (by simp) (by simp) rfl rfl rfl rfl
    hcode.bytesAt hlow hpre.write
  rw [hsel] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_push h _ _ _ hpre.write.low hpre.write.tables,
    ⟨afterStep_push_rip h _ _ _, ⟨Operand.read_afterStep_push_rsp _ _ _ _,
      Operand.read_afterStep_push_mem _ _ _ _⟩, trivial,
      (pushEffect_components _ _ s).symm ▸ AgreesExcept.afterStep_push _ _ _ _⟩⟩

theorem push_gs_triple [Bindings] (p : BitVec 64) (sel : BitVec 16) :
    Triple (fun s => PushPre p 2 s ∧ s.GS.selector = sel)
      (codeRange p [0x0F, 0xA8]) (Effect.post (pushGsEffect p 2 sel)) :=
  Triple.of_effect (fun _ hpre => pushEffect_avoids (by simp) _ _ hpre.1)
    (push_gs_effect_step p sel)

attribute [x86_compose] pushGsEffect

@[x86_local] theorem pushGsEffect_local {p : BitVec 64} {len : Nat} {sel : BitVec 16} :
    Effect.Local (pushGsEffect p len sel) := by
  effect_local [pushGsEffect, pushEffect, pushAddr, stackPtr]

def push16GsEffect (p : BitVec 64) (len : Nat) (sel : BitVec 16) : RamState → Effect :=
  push16Effect (fun _ => p + BitVec.ofNat 64 len) fun _ => pushsregSpec 16 sel

@[simp] theorem push16GsEffect_components (p : BitVec 64) (len : Nat) (sel : BitVec 16) (s : RamState) :
    (push16GsEffect p len sel s).components = [.reg 4, .mem (pushAddr16 s) 2, .rip] :=
  push16Effect_components _ _ s

theorem push16_gs_effect_step [Bindings] (p : BitVec 64) (sel : BitVec 16) :
    StepEffect (fun s => Push16Pre p 3 s ∧ s.GS.selector = sel)
      (codeRange p [0x66, 0x0F, 0xA8]) (push16GsEffect p 3 sel) := by
  rintro s h hcode ⟨hpre, hsel⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := push16_gs_step s h [0x66] (by simpa using scanPrefix_66) (by simp) rfl rfl rfl rfl rfl
    hcode.bytesAt hlow hpre.write
  rw [hsel] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_push16 h _ _ _ hpre.write.low hpre.write.tables,
    ⟨afterStep_push16_rip h _ _ _, ⟨Operand.read_afterStep_push16_rsp _ _ _ _,
      Operand.read_afterStep_push16_mem _ _ _ _⟩, trivial,
      (push16Effect_components _ _ s).symm ▸ AgreesExcept.afterStep_push16 _ _ _ _⟩⟩

theorem push16_gs_triple [Bindings] (p : BitVec 64) (sel : BitVec 16) :
    Triple (fun s => Push16Pre p 3 s ∧ s.GS.selector = sel)
      (codeRange p [0x66, 0x0F, 0xA8]) (Effect.post (push16GsEffect p 3 sel)) :=
  Triple.of_effect (fun _ hpre => push16Effect_avoids (by simp) _ _ hpre.1)
    (push16_gs_effect_step p sel)

attribute [x86_compose] push16GsEffect

@[x86_local] theorem push16GsEffect_local {p : BitVec 64} {len : Nat} {sel : BitVec 16} :
    Effect.Local (push16GsEffect p len sel) := by
  effect_local [push16GsEffect, push16Effect, pushAddr16, stackPtr]

end X86Proofs
