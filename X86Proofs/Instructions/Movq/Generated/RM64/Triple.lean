import X86Proofs.Instructions.Movq.Generated.RM64.Step
import X86Proofs.Instructions.Movq.Generated.RM64.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movqR64MmEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 3) (s : RamState) :
    Effect :=
  let b := (Operand.mmx src : Operand 64).read s
  ({ rip := p + BitVec.ofNat 64 len
     writes := [⟨(Operand.reg dst : Operand 64), movdSpec 64 64 b⟩] } : Effect).withMmx s

@[simp] theorem movqR64MmEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (src : BitVec 3) (s : RamState) :
    (movqR64MmEffect p len dst src s).components = [.reg dst, .fsw, .ftw, .rip] := rfl

theorem movq_r64_mm_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (MmxPre p)
      (codeRange p ([rex, 0x0F, 0x7E, modrm]))
      (movqR64MmEffect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) (modrmReg modrm)) := by
  rintro s h hcode ⟨hp, hcr0, hes, hfeat⟩
  subst hp
  have hr := hrex.rexPrefix
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := movq_r64_mm_step s h hcr0 hes hfeat [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; exact hrex.rex_w s.DS) (by rw [scanContext_rex _ _ hr]; rfl) modrm hmod hcode.bytesAt hlow
  simp only [hc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx_reg h _ _ _ _, ?_⟩
  exact mmxRegEffect_holds h _ _ _ _ (mergeGPR_64 _ _) rfl

theorem movq_r64_mm_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (MmxPre p)
      (codeRange p ([rex, 0x0F, 0x7E, modrm]))
      (Effect.post (movqR64MmEffect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) (modrmReg modrm))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movqR64MmEffect_components]; simp [Component.Covers]) _)
    (movq_r64_mm_effect_step p rex hrex modrm hmod)

theorem movq_r64_mm_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (src : BitVec 3) :
    Triple (MmxPre p) (codeRange p (encodeMovqR64Mm dst src))
      (Effect.post (movqR64MmEffect p (encodeMovqR64Mm dst src).length (dst.setWidth 5) src)) := by
  unfold encodeMovqR64Mm
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hsrc, hdst⟩ := encodeMmxGprW_spec 0x7E src dst
  rw [hbytes, ← hdst, ← hsrc]
  exact movq_r64_mm_triple_of_bytes p rex hrex modrm hmod

attribute [x86_compose] movqR64MmEffect

@[x86_local] theorem movqR64MmEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 3} :
    Effect.Local (movqR64MmEffect p len dst src) := by
  effect_local [movqR64MmEffect, Effect.withMmx]

end X86Proofs
