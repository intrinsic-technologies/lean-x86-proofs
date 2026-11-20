import X86Proofs.Instructions.Push.Generated.R16.Step
import X86Proofs.Instructions.Push.Generated.R16.Encode
import X86Proofs.Program.ReadWrite.Load
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def pushR16Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) : RamState → Effect :=
  push16Effect (fun _ => p + BitVec.ofNat 64 len) fun s => (Operand.reg src : Operand 16).read s

@[simp] theorem pushR16Effect_components (p : BitVec 64) (len : Nat) (src : BitVec 5) (s : RamState) :
    (pushR16Effect p len src s).components = [.reg 4, .mem (pushAddr16 s) 2, .rip] :=
  push16Effect_components _ _ s

theorem push_r16_effect_step [Bindings] (p : BitVec 64) (op : UInt8)
    (hop : PushOpcode op) :
    StepEffect (Push16Pre p 2) (codeRange p [0x66, op]) (pushR16Effect p 2 (gprNumber 0 0 (opcodeReg op))) := by
  refine StepEffect.of_push16 _ fun s h hcode hpre => ?_
  have hp := hpre.rip
  subst hp
  have hstep := push_r16_step s h [0x66] (by simpa using scanPrefix_66) (by simp) rfl rfl
    rfl rfl rfl op hop hcode.bytesAt (hcode.low (by simp) (by simp))
    hpre.write
  exact hstep

theorem push_r16_triple_of_bytes [Bindings] (p : BitVec 64) (op : UInt8)
    (hop : PushOpcode op) :
    Triple (Push16Pre p 2) (codeRange p [0x66, op]) (Effect.post (pushR16Effect p 2 (gprNumber 0 0 (opcodeReg op)))) :=
  Triple.of_effect (fun _ hpre => push16Effect_avoids rfl _ _ hpre)
    (push_r16_effect_step p op hop)

theorem push_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8) (hrex : RexNoWPrefix rex.toBitVec) (op : UInt8)
    (hop : PushOpcode op) :
    StepEffect (Push16Pre p 3) (codeRange p [0x66, rex, op]) (pushR16Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op))) := by
  have hr := hrex.rexPrefix
  refine StepEffect.of_push16 _ fun s h hcode hpre => ?_
  have hp := hpre.rip
  subst hp
  have hstep := push_r16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.rex_w_osz s.DS) op hop hcode.bytesAt (hcode.low (by simp) (by simp))
    hpre.write
  simp only [scanContext_66_rex _ _ hr] at hstep
  exact hstep

theorem push_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8) (hrex : RexNoWPrefix rex.toBitVec) (op : UInt8)
    (hop : PushOpcode op) :
    Triple (Push16Pre p 3) (codeRange p [0x66, rex, op]) (Effect.post (pushR16Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op)))) :=
  Triple.of_effect (fun _ hpre => push16Effect_avoids rfl _ _ hpre)
    (push_r16_rex_effect_step p rex hrex op hop)

theorem push_r16_triple [Bindings] (p : BitVec 64) (r : BitVec 4) :
    Triple (Push16Pre p (encodePushR16 r).length) (codeRange p (encodePushR16 r))
      (Effect.post (pushR16Effect p (encodePushR16 r).length (r.setWidth 5))) := by
  rcases encodePushR16_spec r with ⟨op, hbytes, hop, hreg⟩ | ⟨rex, op, hbytes, hrex, hop, hreg⟩
  · rw [hbytes, ← hreg]
    exact push_r16_triple_of_bytes p op hop
  · rw [hbytes, ← hreg]
    exact push_r16_rex_triple_of_bytes p rex hrex op hop

attribute [x86_compose] pushR16Effect

@[x86_local] theorem pushR16Effect_local {p : BitVec 64} {len : Nat} {r : BitVec 5} :
    Effect.Local (pushR16Effect p len r) := by
  effect_local [pushR16Effect, push16Effect, pushAddr16, stackPtr]

end X86Proofs
