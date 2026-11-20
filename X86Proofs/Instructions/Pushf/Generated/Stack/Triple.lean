import X86Proofs.Instructions.Pushf.Generated.Stack.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def pushfqEffect (p : BitVec 64) (len : Nat) (fl : StatusFlags) : RamState → Effect :=
  pushEffect (fun _ => p + BitVec.ofNat 64 len) fun s =>
    pushfSpec (fl.store (clearStatusFlags s.RFLAGS))

@[simp] theorem pushfqEffect_components (p : BitVec 64) (len : Nat) (fl : StatusFlags) (s : RamState) :
    (pushfqEffect p len fl s).components = [.reg 4, .mem (pushAddr s) 8, .rip] :=
  pushEffect_components _ _ s

theorem pushfq_effect_step [Bindings] (p : BitVec 64) (fl : StatusFlags) :
    StepEffect (fun s => PushPre p 1 s ∧ StatusFlags.ofRFLAGS s.RFLAGS = fl)
      (codeRange p [0x9C]) (pushfqEffect p 1 fl) := by
  rintro s h hcode ⟨hpre, rfl⟩
  have hp := hpre.rip
  subst hp
  have hstep := pushfq_step s h [] (by simp) (by simp) rfl rfl rfl rfl
    hcode.bytesAt (hcode.low (by simp) (by simp)) hpre.write
  refine ⟨_, hstep, ReadyToStep.afterStep_push h _ _ _ hpre.write.low hpre.write.tables,
    ⟨afterStep_push_rip h _ _ _, ⟨Operand.read_afterStep_push_rsp _ _ _ _, ?_⟩, trivial,
      (pushfqEffect_components _ _ _ s).symm ▸ AgreesExcept.afterStep_push _ _ _ _⟩⟩
  show (Operand.mem (pushAddr s) : Operand 64).read _ =
    pushfSpec ((StatusFlags.ofRFLAGS s.RFLAGS).store (clearStatusFlags s.RFLAGS))
  rw [StatusFlags.store_ofRFLAGS_clearStatusFlags]
  exact Operand.read_afterStep_push_mem _ _ _ _

theorem pushfq_triple [Bindings] (p : BitVec 64) (fl : StatusFlags) :
    Triple (fun s => PushPre p 1 s ∧ StatusFlags.ofRFLAGS s.RFLAGS = fl)
      (codeRange p [0x9C]) (Effect.post (pushfqEffect p 1 fl)) :=
  Triple.of_effect (fun _ hpre => pushEffect_avoids rfl _ _ hpre.1)
    (pushfq_effect_step p fl)

attribute [x86_compose] pushfqEffect

@[x86_local] theorem pushfqEffect_local {p : BitVec 64} {len : Nat} {fl : StatusFlags} :
    Effect.Local (pushfqEffect p len fl) := by
  effect_local [pushfqEffect, pushEffect, pushAddr, stackPtr]

def pushfEffect (p : BitVec 64) (len : Nat) (fl : StatusFlags) : RamState → Effect :=
  push16Effect (fun _ => p + BitVec.ofNat 64 len) fun s =>
    (pushfSpec (fl.store (clearStatusFlags s.RFLAGS))).setWidth 16

@[simp] theorem pushfEffect_components (p : BitVec 64) (len : Nat) (fl : StatusFlags) (s : RamState) :
    (pushfEffect p len fl s).components = [.reg 4, .mem (pushAddr16 s) 2, .rip] :=
  push16Effect_components _ _ s

theorem pushf_effect_step [Bindings] (p : BitVec 64) (fl : StatusFlags) :
    StepEffect (fun s => Push16Pre p 2 s ∧ StatusFlags.ofRFLAGS s.RFLAGS = fl)
      (codeRange p [0x66, 0x9C]) (pushfEffect p 2 fl) := by
  rintro s h hcode ⟨hpre, rfl⟩
  have hp := hpre.rip
  subst hp
  have hstep := pushf_step s h [0x66] (by simpa using scanPrefix_66) (by simp) rfl rfl rfl rfl
    hcode.bytesAt (hcode.low (by simp) (by simp)) hpre.write
  refine ⟨_, hstep, ReadyToStep.afterStep_push16 h _ _ _ hpre.write.low hpre.write.tables,
    ⟨afterStep_push16_rip h _ _ _, ⟨Operand.read_afterStep_push16_rsp _ _ _ _, ?_⟩, trivial,
      (pushfEffect_components _ _ _ s).symm ▸ AgreesExcept.afterStep_push16 _ _ _ _⟩⟩
  show (Operand.mem (pushAddr16 s) : Operand 16).read _ =
    (pushfSpec ((StatusFlags.ofRFLAGS s.RFLAGS).store (clearStatusFlags s.RFLAGS))).setWidth 16
  rw [StatusFlags.store_ofRFLAGS_clearStatusFlags]
  exact Operand.read_afterStep_push16_mem _ _ _ _

theorem pushf_triple [Bindings] (p : BitVec 64) (fl : StatusFlags) :
    Triple (fun s => Push16Pre p 2 s ∧ StatusFlags.ofRFLAGS s.RFLAGS = fl)
      (codeRange p [0x66, 0x9C]) (Effect.post (pushfEffect p 2 fl)) :=
  Triple.of_effect (fun _ hpre => push16Effect_avoids rfl _ _ hpre.1)
    (pushf_effect_step p fl)

attribute [x86_compose] pushfEffect

@[x86_local] theorem pushfEffect_local {p : BitVec 64} {len : Nat} {fl : StatusFlags} :
    Effect.Local (pushfEffect p len fl) := by
  effect_local [pushfEffect, push16Effect, pushAddr16, stackPtr]

theorem pushfq_rexw_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (fl : StatusFlags) :
    StepEffect (fun s => PushPre p 2 s ∧ StatusFlags.ofRFLAGS s.RFLAGS = fl)
      (codeRange p [rex, 0x9C]) (pushfqEffect p 2 fl) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hpre, rfl⟩
  have hp := hpre.rip
  subst hp
  have hstep := pushfq_rexw_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    hcode.bytesAt (hcode.low (by simp) (by simp)) hpre.write
  refine ⟨_, hstep, ReadyToStep.afterStep_push h _ _ _ hpre.write.low hpre.write.tables,
    ⟨afterStep_push_rip h _ _ _, ⟨Operand.read_afterStep_push_rsp _ _ _ _, ?_⟩, trivial,
      (pushfqEffect_components _ _ _ s).symm ▸ AgreesExcept.afterStep_push _ _ _ _⟩⟩
  show (Operand.mem (pushAddr s) : Operand 64).read _ =
    pushfSpec ((StatusFlags.ofRFLAGS s.RFLAGS).store (clearStatusFlags s.RFLAGS))
  rw [StatusFlags.store_ofRFLAGS_clearStatusFlags]
  exact Operand.read_afterStep_push_mem _ _ _ _

theorem pushfq_rexw_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (fl : StatusFlags) :
    Triple (fun s => PushPre p 2 s ∧ StatusFlags.ofRFLAGS s.RFLAGS = fl)
      (codeRange p [rex, 0x9C]) (Effect.post (pushfqEffect p 2 fl)) :=
  Triple.of_effect (fun _ hpre => pushEffect_avoids rfl _ _ hpre.1)
    (pushfq_rexw_effect_step p rex hrex fl)

theorem pushfq_rexw_triple [Bindings] (p : BitVec 64) (fl : StatusFlags) :
    Triple (fun s => PushPre p 2 s ∧ StatusFlags.ofRFLAGS s.RFLAGS = fl)
      (codeRange p [0x48, 0x9C]) (Effect.post (pushfqEffect p 2 fl)) :=
  pushfq_rexw_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide) fl

end X86Proofs
