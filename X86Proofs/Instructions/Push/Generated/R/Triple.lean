import X86Proofs.Instructions.Push.Generated.R.Step
import X86Proofs.Instructions.Push.Generated.R.Encode
import X86Proofs.Instructions.Push.Triple
import X86Proofs.Instructions.Push.Generated.R16.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem push_r64_ff_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    StepEffect (PushPre p 2) (codeRange p [0xFF, modrm])
      (pushR64Effect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  refine StepEffect.of_push _ fun s h hcode hpre => ?_
  have hp := hpre.rip
  subst hp
  exact push_r64_ff_step s h [] (by simp) (by simp) rfl rfl rfl rfl modrm hmod hreg
    hcode.bytesAt (hcode.low (by simp) (by simp)) hpre.write

theorem push_r64_ff_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    Triple (PushPre p 2) (codeRange p [0xFF, modrm])
      (Effect.post (pushR64Effect p 2 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun _ hpre => pushEffect_avoids rfl _ _ hpre)
    (push_r64_ff_effect_step p modrm hmod hreg)

theorem push_r64_ff_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    StepEffect (PushPre p 3) (codeRange p [rex, 0xFF, modrm])
      (pushR64Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  refine StepEffect.of_push _ fun s h hcode hpre => ?_
  have hp := hpre.rip
  subst hp
  have hstep := push_r64_ff_step s h [rex] (by simpa using hrex.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hrex]; rfl) (by rw [scanContext_rex _ _ hrex]; rfl)
    (by rw [scanContext_rex _ _ hrex]; rfl) (by rw [scanContext_rex _ _ hrex]; rfl) modrm hmod
    hreg hcode.bytesAt (hcode.low (by simp) (by simp)) hpre.write
  simp only [scanContext_rex _ _ hrex] at hstep
  exact hstep

theorem push_r64_ff_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    Triple (PushPre p 3) (codeRange p [rex, 0xFF, modrm])
      (Effect.post (pushR64Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun _ hpre => pushEffect_avoids rfl _ _ hpre)
    (push_r64_ff_rex_effect_step p rex modrm hrex hmod hreg)

theorem push_r64_ff_triple [Bindings] (p : BitVec 64) (r : BitVec 4) :
    Triple (PushPre p (encodePushFFR64 r).length) (codeRange p (encodePushFFR64 r))
      (Effect.post (pushR64Effect p (encodePushFFR64 r).length (r.setWidth 5))) := by
  rcases encodePushFFR64_spec r with ⟨modrm, hbytes, hmod, hreg, hr⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hr⟩
  · rw [hbytes, ← hr]
    exact push_r64_ff_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hr]
    exact push_r64_ff_rex_triple_of_bytes p rex modrm hrex hmod hreg

theorem push_r16_ff_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    StepEffect (Push16Pre p 3) (codeRange p [0x66, 0xFF, modrm])
      (pushR16Effect p 3 (gprNumber 0 0 (modrmRm modrm))) := by
  refine StepEffect.of_push16 _ fun s h hcode hpre => ?_
  have hp := hpre.rip
  subst hp
  have hstep := push_r16_ff_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    rfl rfl rfl rfl rfl modrm hmod hreg hcode.bytesAt (hcode.low (by simp) (by simp))
    hpre.write
  exact hstep

theorem push_r16_ff_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    Triple (Push16Pre p 3) (codeRange p [0x66, 0xFF, modrm])
      (Effect.post (pushR16Effect p 3 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun _ hpre => push16Effect_avoids rfl _ _ hpre)
    (push_r16_ff_effect_step p modrm hmod hreg)

theorem push_r16_ff_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    StepEffect (Push16Pre p 4) (codeRange p [0x66, rex, 0xFF, modrm])
      (pushR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  have hr := hrex.rexPrefix
  refine StepEffect.of_push16 _ fun s h hcode hpre => ?_
  have hp := hpre.rip
  subst hp
  have hstep := push_r16_ff_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix])
    (by simp) (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.rex_w_osz s.DS)
    modrm hmod hreg hcode.bytesAt (hcode.low (by simp) (by simp))
    hpre.write
  simp only [scanContext_66_rex _ _ hr] at hstep
  exact hstep

theorem push_r16_ff_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    Triple (Push16Pre p 4) (codeRange p [0x66, rex, 0xFF, modrm])
      (Effect.post (pushR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun _ hpre => push16Effect_avoids rfl _ _ hpre)
    (push_r16_ff_rex_effect_step p rex hrex modrm hmod hreg)

theorem push_r16_ff_triple [Bindings] (p : BitVec 64) (r : BitVec 4) :
    Triple (Push16Pre p (encodePushFFR16 r).length) (codeRange p (encodePushFFR16 r))
      (Effect.post (pushR16Effect p (encodePushFFR16 r).length (r.setWidth 5))) := by
  rcases encodePushFFR16_spec r with ⟨modrm, hbytes, hmod, hreg, hr⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hr⟩
  · rw [hbytes, ← hr]
    exact push_r16_ff_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hr]
    exact push_r16_ff_rex_triple_of_bytes p rex hrex modrm hmod hreg

end X86Proofs
