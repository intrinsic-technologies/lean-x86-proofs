import X86Proofs.Instructions.Movq.Generated.RX.Step
import X86Proofs.Instructions.Movq.Generated.RX.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movqR64XmmEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) :
    Effect :=
  let a := (Operand.xmm src : Operand 128).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), movdSpec 64 64 a⟩] }

@[simp] theorem movqR64XmmEffect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : (movqR64XmmEffect p len dst src s).components = [.reg dst, .rip] := rfl

theorem movq_r64_xmm_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (Sse2Pre p)
      (codeRange p ([0x66, rex, 0x0F, 0x7E, modrm]))
      (movqR64XmmEffect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode ⟨⟨hp, hsse⟩, hfeat⟩
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_66_rex s.DS (PrefixSegments.ofState s) hr.rexPrefix
  have hstep := movq_r64_xmm_step s h hsse hfeat [0x66, rex]
    (by simp [scanPrefix_66, hr.rexPrefix.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; exact hr.rex_w s.DS)
    modrm hmod hcode.bytesAt hlow
  simp only [hc] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_b4
      (oszRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  have hsrc : gprNumber (oszRexContext s.DS rex.toBitVec).rex_r4
      (oszRexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, Operand.read_afterFetches, Operand.read_beforeFetch]

theorem movq_r64_xmm_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (Sse2Pre p)
      (codeRange p ([0x66, rex, 0x0F, 0x7E, modrm]))
      (Effect.post (movqR64XmmEffect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movqR64XmmEffect_components]; simp [Component.Covers]) _)
    (movq_r64_xmm_rex_effect_step p rex hr modrm hmod)

theorem movq_r64_xmm_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (Sse2Pre p) (codeRange p (encodeMovqR64Xmm dst src))
      (Effect.post (movqR64XmmEffect p (encodeMovqR64Xmm dst src).length
        (dst.setWidth 5) (src.setWidth 5))) := by
  unfold encodeMovqR64Xmm
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hrm⟩ := encodeSseRegRegW_spec 0x7E src dst
  rw [hbytes, ← hreg, ← hrm]
  exact movq_r64_xmm_rex_triple_of_bytes p rex hrex modrm hmod

attribute [x86_compose] movqR64XmmEffect

@[x86_local] theorem movqR64XmmEffect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5} :
    Effect.Local (movqR64XmmEffect p len dst src) := by
  effect_local [movqR64XmmEffect]

end X86Proofs
