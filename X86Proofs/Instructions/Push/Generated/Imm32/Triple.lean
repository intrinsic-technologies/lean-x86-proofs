import X86Proofs.Instructions.Push.Generated.Imm32.Step
import X86Proofs.Instructions.Push.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def pushImm32Effect (p : BitVec 64) (len : Nat) (imm : BitVec 32) : RamState → Effect :=
  pushEffect (fun _ => p + BitVec.ofNat 64 len) fun _ => imm.signExtend 64

@[simp] theorem pushImm32Effect_components (p : BitVec 64) (len : Nat) (imm : BitVec 32)
    (s : RamState) :
    (pushImm32Effect p len imm s).components = [.reg 4, .mem (pushAddr s) 8, .rip] :=
  pushEffect_components _ _ s

theorem push_imm32_effect_step [Bindings] (p : BitVec 64) (imm : BitVec 32) :
    StepEffect (PushPre p 5) (codeRange p (0x68 :: immBytes 32 imm)) (pushImm32Effect p 5 imm) := by
  refine StepEffect.of_push _ fun s h hcode hpre => ?_
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  exact push_imm32_step s h [] (by simp) (by simp) rfl rfl rfl rfl imm hcode.bytesAt hlow
    hpre.write

theorem push_imm32_triple [Bindings] (p : BitVec 64) (imm : BitVec 32) :
    Triple (PushPre p 5) (codeRange p (0x68 :: immBytes 32 imm)) (Effect.post (pushImm32Effect p 5 imm)) :=
  Triple.of_effect (fun _ hpre => pushEffect_avoids (by simp) _ _ hpre)
    (push_imm32_effect_step p imm)

attribute [x86_compose] pushImm32Effect

@[x86_local] theorem pushImm32Effect_local {p : BitVec 64} {len : Nat} {imm : BitVec 32} :
    Effect.Local (pushImm32Effect p len imm) := by
  effect_local [pushImm32Effect, pushEffect, pushAddr, stackPtr]

def push16Imm16Effect (p : BitVec 64) (len : Nat) (imm : BitVec 16) : RamState → Effect :=
  push16Effect (fun _ => p + BitVec.ofNat 64 len) fun _ => imm.signExtend 16

@[simp] theorem push16Imm16Effect_components (p : BitVec 64) (len : Nat) (imm : BitVec 16)
    (s : RamState) :
    (push16Imm16Effect p len imm s).components = [.reg 4, .mem (pushAddr16 s) 2, .rip] :=
  push16Effect_components _ _ s

theorem push16_imm16_effect_step [Bindings] (p : BitVec 64) (imm : BitVec 16) :
    StepEffect (Push16Pre p 4) (codeRange p (0x66 :: 0x68 :: immBytes 16 imm)) (push16Imm16Effect p 4 imm) := by
  refine StepEffect.of_push16 _ fun s h hcode hpre => ?_
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  exact push16_imm16_step s h [0x66] (by simpa using scanPrefix_66) (by simp) rfl rfl rfl rfl
    rfl imm hcode.bytesAt hlow hpre.write

theorem push16_imm16_triple [Bindings] (p : BitVec 64) (imm : BitVec 16) :
    Triple (Push16Pre p 4) (codeRange p (0x66 :: 0x68 :: immBytes 16 imm)) (Effect.post (push16Imm16Effect p 4 imm)) :=
  Triple.of_effect (fun _ hpre => push16Effect_avoids (by simp) _ _ hpre)
    (push16_imm16_effect_step p imm)

attribute [x86_compose] push16Imm16Effect

@[x86_local] theorem push16Imm16Effect_local {p : BitVec 64} {len : Nat} {imm : BitVec 16} :
    Effect.Local (push16Imm16Effect p len imm) := by
  effect_local [push16Imm16Effect, push16Effect, pushAddr16, stackPtr]

end X86Proofs
