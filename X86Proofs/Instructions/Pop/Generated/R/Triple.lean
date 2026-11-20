import X86Proofs.Instructions.Pop.Generated.R.Step
import X86Proofs.Instructions.Pop.Generated.R.Encode
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Pop.Generated.R16.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem pop_r64_8f_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hdst : gprNumber 0 0 (modrmRm modrm) ≠ 4) :
    StepEffect (PopPre p) (codeRange p [0x8F, modrm])
      (popR64Effect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  refine StepEffect.of_pop hdst fun s h hcode hpre => ?_
  have hp := hpre.rip
  subst hp
  exact pop_r64_8f_step s h [] (by simp) (by simp) rfl rfl rfl rfl modrm hmod hreg
    hcode.bytesAt (hcode.low (by simp) (by simp)) hpre.read

theorem pop_r64_8f_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hdst : gprNumber 0 0 (modrmRm modrm) ≠ 4) :
    Triple (PopPre p) (codeRange p [0x8F, modrm])
      (Effect.post (popR64Effect p 2 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => popR64Effect_avoids p _ _ s _)
    (pop_r64_8f_effect_step p modrm hmod hreg hdst)

theorem pop_r64_8f_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hdst : gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) ≠ 4) :
    StepEffect (PopPre p) (codeRange p [rex, 0x8F, modrm])
      (popR64Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  refine StepEffect.of_pop hdst fun s h hcode hpre => ?_
  have hp := hpre.rip
  subst hp
  have hstep := pop_r64_8f_step s h [rex] (by simpa using hrex.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hrex]; rfl) (by rw [scanContext_rex _ _ hrex]; rfl)
    (by rw [scanContext_rex _ _ hrex]; rfl) (by rw [scanContext_rex _ _ hrex]; rfl) modrm hmod
    hreg hcode.bytesAt (hcode.low (by simp) (by simp)) hpre.read
  simp only [scanContext_rex _ _ hrex] at hstep
  exact hstep

theorem pop_r64_8f_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hdst : gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) ≠ 4) :
    Triple (PopPre p) (codeRange p [rex, 0x8F, modrm])
      (Effect.post (popR64Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => popR64Effect_avoids p _ _ s _)
    (pop_r64_8f_rex_effect_step p rex modrm hrex hmod hreg hdst)

theorem pop_r64_8f_triple [Bindings] (p : BitVec 64) (r : BitVec 4) (hdst : r ≠ 4) :
    Triple (PopPre p) (codeRange p (encodePop8FR64 r))
      (Effect.post (popR64Effect p (encodePop8FR64 r).length (r.setWidth 5))) := by
  have hdst5 : r.setWidth 5 ≠ 4 := by
    revert r
    decide
  rcases encodePop8FR64_spec r with ⟨modrm, hbytes, hmod, hreg, hr⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hr⟩
  · rw [hbytes, ← hr]
    exact pop_r64_8f_triple_of_bytes p modrm hmod hreg (hr ▸ hdst5)
  · rw [hbytes, ← hr]
    exact pop_r64_8f_rex_triple_of_bytes p rex modrm hrex hmod hreg (hr ▸ hdst5)

theorem pop_r16_8f_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hdst : (gprNumber 0 0 (modrmRm modrm)) ≠ 4) :
    StepEffect (Pop16Pre p) (codeRange p [0x66, 0x8F, modrm])
      (popR16Effect p 3 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode hpre
  have hp := hpre.rip
  subst hp
  have hstep := pop_r16_8f_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    rfl rfl rfl rfl rfl modrm hmod hreg hcode.bytesAt (hcode.low (by simp) (by simp))
    hpre.read
  exact ⟨_, hstep, ReadyToStep.afterStep_pop16 h _ _ _,
    ⟨afterStep_pop16_rip h _ _ _, ⟨Operand.read_afterStep_pop16 _ _ hdst _,
      Operand.read_afterStep_pop16_rsp _ _ hdst _⟩, trivial, AgreesExcept.afterStep_pop16 _ _ _ _⟩⟩

theorem pop_r16_8f_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hdst : (gprNumber 0 0 (modrmRm modrm)) ≠ 4) :
    Triple (Pop16Pre p) (codeRange p [0x66, 0x8F, modrm])
      (Effect.post (popR16Effect p 3 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [popR16Effect_components]; simp [Component.Covers]) _)
    (pop_r16_8f_effect_step p modrm hmod hreg hdst)

theorem pop_r16_8f_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hdst : (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) ≠ 4) :
    StepEffect (Pop16Pre p) (codeRange p [0x66, rex, 0x8F, modrm])
      (popR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hpre
  have hp := hpre.rip
  subst hp
  have hstep := pop_r16_8f_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix])
    (by simp) (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.rex_w_osz s.DS)
    modrm hmod hreg hcode.bytesAt (hcode.low (by simp) (by simp))
    hpre.read
  simp only [scanContext_66_rex _ _ hr] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_pop16 h _ _ _,
    ⟨afterStep_pop16_rip h _ _ _, ⟨Operand.read_afterStep_pop16 _ _ hdst _,
      Operand.read_afterStep_pop16_rsp _ _ hdst _⟩, trivial, AgreesExcept.afterStep_pop16 _ _ _ _⟩⟩

theorem pop_r16_8f_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hdst : (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) ≠ 4) :
    Triple (Pop16Pre p) (codeRange p [0x66, rex, 0x8F, modrm])
      (Effect.post (popR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [popR16Effect_components]; simp [Component.Covers]) _)
    (pop_r16_8f_rex_effect_step p rex hrex modrm hmod hreg hdst)

theorem pop_r16_8f_triple [Bindings] (p : BitVec 64) (r : BitVec 4) (hdst : r ≠ 4) :
    Triple (Pop16Pre p) (codeRange p (encodePop8FR16 r))
      (Effect.post (popR16Effect p (encodePop8FR16 r).length (r.setWidth 5))) := by
  have hdst5 : r.setWidth 5 ≠ 4 := by
    revert r
    decide
  rcases encodePop8FR16_spec r with ⟨modrm, hbytes, hmod, hreg, hr⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hr⟩
  · rw [hbytes, ← hr]
    exact pop_r16_8f_triple_of_bytes p modrm hmod hreg (hr ▸ hdst5)
  · rw [hbytes, ← hr]
    exact pop_r16_8f_rex_triple_of_bytes p rex hrex modrm hmod hreg (hr ▸ hdst5)

end X86Proofs
