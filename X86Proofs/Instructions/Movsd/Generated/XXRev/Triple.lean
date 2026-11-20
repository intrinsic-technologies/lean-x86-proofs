import X86Proofs.Instructions.Movsd.Generated.XXRev.Step
import X86Proofs.Instructions.Movsd.Generated.XXRev.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movsdXmmXmmRevEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) :
    Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.xmm src : Operand 128).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), movsRegSpec 64 a b⟩] }

@[simp] theorem movsdXmmXmmRevEffect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : (movsdXmmXmmRevEffect p len dst src s).components = [.xmm dst, .rip] := rfl

theorem movsd_xmm_xmm_rev_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (Sse2Pre p)
      (codeRange p ([0xF2, 0x0F, 0x11, modrm]))
      (movsdXmmXmmRevEffect p 4 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm))) := by
  intro s h hcode hpre
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := movsd_xmm_xmm_rev_step s h hpre.sse hpre.sse2 [0xF2]
    (by simpa using scanPrefix_f2) (by simp)
    rfl rfl rfl
    rfl rfl
    modrm hmod hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0xF2]).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) [0xF2]).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0xF2]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0xF2]).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult_xmm h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_writeResult_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]

theorem movsd_xmm_xmm_rev_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (Sse2Pre p)
      (codeRange p ([0xF2, 0x0F, 0x11, modrm]))
      (Effect.post (movsdXmmXmmRevEffect p 4 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsdXmmXmmRevEffect_components]; simp [Component.Covers]) _)
    (movsd_xmm_xmm_rev_effect_step p modrm hmod)

theorem movsd_xmm_xmm_rev_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (Sse2Pre p)
      (codeRange p ([0xF2, rex, 0x0F, 0x11, modrm]))
      (movsdXmmXmmRevEffect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  intro s h hcode hpre
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_f2_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := movsd_xmm_xmm_rev_step s h hpre.sse hpre.sse2 [0xF2, rex]
    (by simp [scanPrefix_f2, hr.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl)
    modrm hmod hcode.bytesAt hlow
  simp only [hc] at hstep
  have hdst : gprNumber (repneRexContext s.DS rex.toBitVec).rex_b4
      (repneRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  have hsrc : gprNumber (repneRexContext s.DS rex.toBitVec).rex_r4
      (repneRexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult_xmm h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_writeResult_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]

theorem movsd_xmm_xmm_rev_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (Sse2Pre p)
      (codeRange p ([0xF2, rex, 0x0F, 0x11, modrm]))
      (Effect.post (movsdXmmXmmRevEffect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsdXmmXmmRevEffect_components]; simp [Component.Covers]) _)
    (movsd_xmm_xmm_rev_rex_effect_step p rex hr modrm hmod)

theorem movsd_xmm_xmm_rev_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (Sse2Pre p) (codeRange p (encodeMovsdXmmXmmRev dst src))
      (Effect.post (movsdXmmXmmRevEffect p (encodeMovsdXmmXmmRev dst src).length
        (dst.setWidth 5) (src.setWidth 5))) := by
  unfold encodeMovsdXmmXmmRev
  rcases encodeSseRegReg_spec 0x11 src dst with ⟨modrm, hbytes, hmod, hreg, hrm⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hrm⟩
  · rw [hbytes, ← hrm, ← hreg]
    exact movsd_xmm_xmm_rev_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hrm, ← hreg]
    exact movsd_xmm_xmm_rev_rex_triple_of_bytes p rex hrex modrm hmod

attribute [x86_compose] movsdXmmXmmRevEffect

@[x86_local] theorem movsdXmmXmmRevEffect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5} :
    Effect.Local (movsdXmmXmmRevEffect p len dst src) := by
  effect_local [movsdXmmXmmRevEffect]

end X86Proofs
