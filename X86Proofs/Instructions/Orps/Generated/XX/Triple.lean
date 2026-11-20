import X86Proofs.Instructions.Orps.Generated.XX.Step
import X86Proofs.Instructions.Orps.Generated.XX.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def orpsXmmXmmEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) :
    Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.xmm src : Operand 128).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), a ||| b⟩] }

@[simp] theorem orpsXmmXmmEffect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : (orpsXmmXmmEffect p len dst src s).components = [.xmm dst, .rip] := rfl

theorem orps_xmm_xmm_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (SsePre p)
      (codeRange p ([0x0F, 0x56, modrm]))
      (orpsXmmXmmEffect p 3 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode ⟨hp, hsse⟩
  have hfeat := hsse.feature
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := orps_xmm_xmm_step s h hsse hfeat []
    (by simp) (by simp)
    rfl rfl rfl
    rfl rfl rfl modrm hmod hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult_xmm h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_writeResult_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]

theorem orps_xmm_xmm_triple_of_bytes [Bindings]
    (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (SsePre p)
      (codeRange p ([0x0F, 0x56, modrm]))
      (Effect.post (orpsXmmXmmEffect p 3 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [orpsXmmXmmEffect_components]; simp [Component.Covers]) _)
    (orps_xmm_xmm_effect_step p modrm hmod)

theorem orps_xmm_xmm_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (SsePre p)
      (codeRange p ([rex, 0x0F, 0x56, modrm]))
      (orpsXmmXmmEffect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode ⟨hp, hsse⟩
  have hfeat := hsse.feature
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := orps_xmm_xmm_step s h hsse hfeat [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl) modrm hmod hcode.bytesAt hlow
  simp only [hc] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult_xmm h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_writeResult_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]

theorem orps_xmm_xmm_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (SsePre p)
      (codeRange p ([rex, 0x0F, 0x56, modrm]))
      (Effect.post (orpsXmmXmmEffect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [orpsXmmXmmEffect_components]; simp [Component.Covers]) _)
    (orps_xmm_xmm_rex_effect_step p rex hr modrm hmod)

theorem orps_xmm_xmm_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (SsePre p) (codeRange p (encodeOrpsXmmXmm dst src))
      (Effect.post (orpsXmmXmmEffect p (encodeOrpsXmmXmm dst src).length
        (dst.setWidth 5) (src.setWidth 5))) := by
  unfold encodeOrpsXmmXmm
  rcases encodeSseRegReg_spec 0x56 dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact orps_xmm_xmm_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact orps_xmm_xmm_rex_triple_of_bytes p rex hrex modrm hmod

attribute [x86_compose] orpsXmmXmmEffect

@[x86_local] theorem orpsXmmXmmEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 5} :
    Effect.Local (orpsXmmXmmEffect p len dst src) := by
  effect_local [orpsXmmXmmEffect]

end X86Proofs
