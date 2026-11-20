import X86Proofs.Instructions.Movdqu.Generated.XXRev.Step
import X86Proofs.Instructions.Movdqu.Generated.XXRev.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movdquXmmXmmRevEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) :
    Effect :=
  let b := (Operand.xmm src : Operand 128).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), b⟩] }

@[simp] theorem movdquXmmXmmRevEffect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : (movdquXmmXmmRevEffect p len dst src s).components = [.xmm dst, .rip] := rfl

theorem movdqu_xmm_xmm_rev_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (Sse2Pre p)
      (codeRange p ([0xF3, 0x0F, 0x7F, modrm]))
      (movdquXmmXmmRevEffect p 4 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm))) := by
  intro s h hcode hpre
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := movdqu_xmm_xmm_rev_step s h hpre.sse hpre.sse2 [0xF3]
    (by simpa using scanPrefix_f3) (by simp)
    rfl rfl rfl
    rfl rfl
    modrm hmod hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0xF3]).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) [0xF3]).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0xF3]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0xF3]).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult_xmm h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_writeResult_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]

theorem movdqu_xmm_xmm_rev_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (Sse2Pre p)
      (codeRange p ([0xF3, 0x0F, 0x7F, modrm]))
      (Effect.post (movdquXmmXmmRevEffect p 4 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movdquXmmXmmRevEffect_components]; simp [Component.Covers]) _)
    (movdqu_xmm_xmm_rev_effect_step p modrm hmod)

theorem movdqu_xmm_xmm_rev_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (Sse2Pre p)
      (codeRange p ([0xF3, rex, 0x0F, 0x7F, modrm]))
      (movdquXmmXmmRevEffect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  intro s h hcode hpre
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_f3_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := movdqu_xmm_xmm_rev_step s h hpre.sse hpre.sse2 [0xF3, rex]
    (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl)
    modrm hmod hcode.bytesAt hlow
  simp only [hc] at hstep
  have hdst : gprNumber (repRexContext s.DS rex.toBitVec).rex_b4
      (repRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  have hsrc : gprNumber (repRexContext s.DS rex.toBitVec).rex_r4
      (repRexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult_xmm h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_writeResult_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]

theorem movdqu_xmm_xmm_rev_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (Sse2Pre p)
      (codeRange p ([0xF3, rex, 0x0F, 0x7F, modrm]))
      (Effect.post (movdquXmmXmmRevEffect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movdquXmmXmmRevEffect_components]; simp [Component.Covers]) _)
    (movdqu_xmm_xmm_rev_rex_effect_step p rex hr modrm hmod)

theorem movdqu_xmm_xmm_rev_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (Sse2Pre p) (codeRange p (encodeMovdquXmmXmmRev dst src))
      (Effect.post (movdquXmmXmmRevEffect p (encodeMovdquXmmXmmRev dst src).length
        (dst.setWidth 5) (src.setWidth 5))) := by
  unfold encodeMovdquXmmXmmRev
  rcases encodeSseRegReg_spec 0x7F src dst with ⟨modrm, hbytes, hmod, hreg, hrm⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hrm⟩
  · rw [hbytes, ← hrm, ← hreg]
    exact movdqu_xmm_xmm_rev_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hrm, ← hreg]
    exact movdqu_xmm_xmm_rev_rex_triple_of_bytes p rex hrex modrm hmod

attribute [x86_compose] movdquXmmXmmRevEffect

@[x86_local] theorem movdquXmmXmmRevEffect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5} :
    Effect.Local (movdquXmmXmmRevEffect p len dst src) := by
  effect_local [movdquXmmXmmRevEffect]

end X86Proofs
