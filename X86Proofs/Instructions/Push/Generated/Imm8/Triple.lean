import X86Proofs.Instructions.Push.Generated.Imm8.Step
import X86Proofs.Instructions.Push.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def pushImm8Effect (p : BitVec 64) (len : Nat) (imm : BitVec 8) : RamState → Effect :=
  pushEffect (fun _ => p + BitVec.ofNat 64 len) fun _ => imm.signExtend 64

@[simp] theorem pushImm8Effect_components (p : BitVec 64) (len : Nat) (imm : BitVec 8)
    (s : RamState) :
    (pushImm8Effect p len imm s).components = [.reg 4, .mem (pushAddr s) 8, .rip] :=
  pushEffect_components _ _ s

theorem push_imm8_effect_step [Bindings] (p : BitVec 64) (imm : BitVec 8) :
    StepEffect (PushPre p 2) (codeRange p (0x6A :: immBytes 8 imm)) (pushImm8Effect p 2 imm) := by
  refine StepEffect.of_push _ fun s h hcode hpre => ?_
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  exact push_imm8_step s h [] (by simp) (by simp) rfl rfl rfl rfl imm hcode.bytesAt hlow
    hpre.write

theorem push_imm8_triple [Bindings] (p : BitVec 64) (imm : BitVec 8) :
    Triple (PushPre p 2) (codeRange p (0x6A :: immBytes 8 imm)) (Effect.post (pushImm8Effect p 2 imm)) :=
  Triple.of_effect (fun _ hpre => pushEffect_avoids (by simp) _ _ hpre)
    (push_imm8_effect_step p imm)

attribute [x86_compose] pushImm8Effect

@[x86_local] theorem pushImm8Effect_local {p : BitVec 64} {len : Nat} {imm : BitVec 8} :
    Effect.Local (pushImm8Effect p len imm) := by
  effect_local [pushImm8Effect, pushEffect, pushAddr, stackPtr]

def push16Imm8Effect (p : BitVec 64) (len : Nat) (imm : BitVec 8) : RamState → Effect :=
  push16Effect (fun _ => p + BitVec.ofNat 64 len) fun _ => imm.signExtend 16

@[simp] theorem push16Imm8Effect_components (p : BitVec 64) (len : Nat) (imm : BitVec 8)
    (s : RamState) :
    (push16Imm8Effect p len imm s).components = [.reg 4, .mem (pushAddr16 s) 2, .rip] :=
  push16Effect_components _ _ s

theorem push16_imm8_effect_step [Bindings] (p : BitVec 64) (imm : BitVec 8) :
    StepEffect (Push16Pre p 3) (codeRange p (0x66 :: 0x6A :: immBytes 8 imm)) (push16Imm8Effect p 3 imm) := by
  refine StepEffect.of_push16 _ fun s h hcode hpre => ?_
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  exact push16_imm8_step s h [0x66] (by simpa using scanPrefix_66) (by simp) rfl rfl rfl rfl
    rfl imm hcode.bytesAt hlow hpre.write

theorem push16_imm8_triple [Bindings] (p : BitVec 64) (imm : BitVec 8) :
    Triple (Push16Pre p 3) (codeRange p (0x66 :: 0x6A :: immBytes 8 imm)) (Effect.post (push16Imm8Effect p 3 imm)) :=
  Triple.of_effect (fun _ hpre => push16Effect_avoids (by simp) _ _ hpre)
    (push16_imm8_effect_step p imm)

attribute [x86_compose] push16Imm8Effect

@[x86_local] theorem push16Imm8Effect_local {p : BitVec 64} {len : Nat} {imm : BitVec 8} :
    Effect.Local (push16Imm8Effect p len imm) := by
  effect_local [push16Imm8Effect, push16Effect, pushAddr16, stackPtr]

end X86Proofs
