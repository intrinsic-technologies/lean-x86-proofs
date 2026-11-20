import X86Proofs.Instructions.Pcmpgtd.Generated.XX.Step
import X86Proofs.Instructions.Pcmpgtd.Generated.XX.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def pcmpgtdXmmXmmEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) :
    Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.xmm src : Operand 128).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), pcmpgtSpec 32 a b⟩] }

@[simp] theorem pcmpgtdXmmXmmEffect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : (pcmpgtdXmmXmmEffect p len dst src s).components = [.xmm dst, .rip] := rfl

theorem pcmpgtd_xmm_xmm_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (Sse2Pre p)
      (codeRange p ([0x66, 0x0F, 0x66, modrm]))
      (pcmpgtdXmmXmmEffect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode ⟨⟨hp, hsse⟩, hfeat⟩
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := pcmpgtd_xmm_xmm_step s h hsse hfeat [0x66]
    (by simpa using scanPrefix_66) (by simp)
    rfl rfl rfl
    rfl rfl rfl modrm hmod hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult_xmm h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_writeResult_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]

theorem pcmpgtd_xmm_xmm_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (Sse2Pre p)
      (codeRange p ([0x66, 0x0F, 0x66, modrm]))
      (Effect.post (pcmpgtdXmmXmmEffect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [pcmpgtdXmmXmmEffect_components]; simp [Component.Covers]) _)
    (pcmpgtd_xmm_xmm_effect_step p modrm hmod)

theorem pcmpgtd_xmm_xmm_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (Sse2Pre p)
      (codeRange p ([0x66, rex, 0x0F, 0x66, modrm]))
      (pcmpgtdXmmXmmEffect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode ⟨⟨hp, hsse⟩, hfeat⟩
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_66_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := pcmpgtd_xmm_xmm_step s h hsse hfeat [0x66, rex]
    (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl) modrm hmod hcode.bytesAt hlow
  simp only [hc] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_r4
      (oszRexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  have hsrc : gprNumber (oszRexContext s.DS rex.toBitVec).rex_b4
      (oszRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult_xmm h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_writeResult_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]

theorem pcmpgtd_xmm_xmm_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (Sse2Pre p)
      (codeRange p ([0x66, rex, 0x0F, 0x66, modrm]))
      (Effect.post (pcmpgtdXmmXmmEffect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [pcmpgtdXmmXmmEffect_components]; simp [Component.Covers]) _)
    (pcmpgtd_xmm_xmm_rex_effect_step p rex hr modrm hmod)

theorem pcmpgtd_xmm_xmm_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (Sse2Pre p) (codeRange p (encodePcmpgtdXmmXmm dst src))
      (Effect.post (pcmpgtdXmmXmmEffect p (encodePcmpgtdXmmXmm dst src).length
        (dst.setWidth 5) (src.setWidth 5))) := by
  unfold encodePcmpgtdXmmXmm
  rcases encodeSseRegReg_spec 0x66 dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact pcmpgtd_xmm_xmm_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact pcmpgtd_xmm_xmm_rex_triple_of_bytes p rex hrex modrm hmod

attribute [x86_compose] pcmpgtdXmmXmmEffect

@[x86_local] theorem pcmpgtdXmmXmmEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 5} :
    Effect.Local (pcmpgtdXmmXmmEffect p len dst src) := by
  effect_local [pcmpgtdXmmXmmEffect]

end X86Proofs
