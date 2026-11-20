import X86Proofs.Instructions.Leave.Generated.Frame.Step
import X86Proofs.Program.ReadWrite.Load
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def leaveEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg 4 : Operand 64), (Operand.reg 5 : Operand 64).read s + 8⟩,
    ⟨(Operand.reg 5 : Operand 64),
      (Operand.mem ((Operand.reg 5 : Operand 64).read s) : Operand 64).read s⟩]

@[simp] theorem leaveEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (leaveEffect p len s).components = [.reg 4, .reg 5, .rip] := rfl

abbrev LeavePre (p : BitVec 64) : RamState → Prop :=
  LoadPre p (fun s => (Operand.reg 5 : Operand 64).read s) 8

theorem leave_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (LeavePre p) (codeRange p [0xC9]) (leaveEffect p 1) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  exact ⟨_, leave_step s h [] (by simp) (by simp) rfl rfl rfl rfl hcode.bytesAt hlow hread,
    ReadyToStep.afterStep_leave h _ _,
    ⟨afterStep_leave_rip h _ _, ⟨Operand.read_afterStep_leave_rsp _ _ _,
      Operand.read_afterStep_leave_rbp _ _ _⟩, trivial, AgreesExcept.afterStep_leave _ _ _⟩⟩

theorem leave_triple [Bindings] (p : BitVec 64) :
    Triple (LeavePre p) (codeRange p [0xC9]) (Effect.post (leaveEffect p 1)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [leaveEffect_components]; simp [Component.Covers]) _)
    (leave_effect_step p)

attribute [x86_compose] leaveEffect

@[x86_local] theorem leaveEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (leaveEffect p len) := by
  effect_local [leaveEffect]

def leave16Effect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg 4 : Operand 64), (Operand.reg 5 : Operand 64).read s + 2⟩,
    ⟨(Operand.reg 5 : Operand 64),
      mergeGPR 16 ((Operand.mem ((Operand.reg 5 : Operand 64).read s) : Operand 16).read s)
        ((Operand.reg 5 : Operand 64).read s)⟩]

@[simp] theorem leave16Effect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (leave16Effect p len s).components = [.reg 4, .reg 5, .rip] := rfl

abbrev Leave16Pre (p : BitVec 64) : RamState → Prop :=
  LoadPre p (fun s => (Operand.reg 5 : Operand 64).read s) 2

theorem leave16_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (Leave16Pre p) (codeRange p [0x66, 0xC9]) (leave16Effect p 2) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  exact ⟨_, leave16_step s h [0x66] (by simpa using scanPrefix_66) (by simp) rfl rfl rfl rfl rfl
      hcode.bytesAt hlow hread,
    ReadyToStep.afterStep_leave16 h _ _,
    ⟨afterStep_leave16_rip h _ _, ⟨Operand.read_afterStep_leave16_rsp _ _ _,
      Operand.read_afterStep_leave16_rbp _ _ _⟩, trivial,
      AgreesExcept.afterStep_leave16 _ _ _⟩⟩

theorem leave16_triple [Bindings] (p : BitVec 64) :
    Triple (Leave16Pre p) (codeRange p [0x66, 0xC9]) (Effect.post (leave16Effect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [leave16Effect_components]; simp [Component.Covers]) _)
    (leave16_effect_step p)

attribute [x86_compose] leave16Effect

@[x86_local] theorem leave16Effect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (leave16Effect p len) := by
  effect_local [leave16Effect]

end X86Proofs
