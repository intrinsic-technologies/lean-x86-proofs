import X86Proofs.Instructions.Movq.Generated.MR64.Step
import X86Proofs.Instructions.Movq.Generated.MR64.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movqMmR64Effect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (src : BitVec 5) (s : RamState) :
    Effect :=
  let b := (Operand.reg src : Operand 64).read s
  mmxEffect s (p + BitVec.ofNat 64 len) dst (movdSpec 64 64 b)

@[simp] theorem movqMmR64Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (src : BitVec 5) (s : RamState) :
    (movqMmR64Effect p len dst src s).components = [.fpr dst, .fsw, .ftw, .rip] := rfl

theorem movq_mm_r64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (MmxPre p)
      (codeRange p ([rex, 0x0F, 0x6E, modrm]))
      (movqMmR64Effect p 4 (modrmReg modrm) (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode ⟨hp, hcr0, hes, hmmx⟩
  subst hp
  have hr := hrex.rexPrefix
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := movq_mm_r64_step s h hcr0 hes hmmx [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; exact hrex.rex_w s.DS) modrm hmod hcode.bytesAt hlow
  simp only [hc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds h _ _ _ _ rfl

theorem movq_mm_r64_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (MmxPre p)
      (codeRange p ([rex, 0x0F, 0x6E, modrm]))
      (Effect.post (movqMmR64Effect p 4 (modrmReg modrm) (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movqMmR64Effect_components]; simp [Component.Covers]) _)
    (movq_mm_r64_effect_step p rex hrex modrm hmod)

theorem movq_mm_r64_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (src : BitVec 4) :
    Triple (MmxPre p) (codeRange p (encodeMovqMmR64 dst src))
      (Effect.post (movqMmR64Effect p (encodeMovqMmR64 dst src).length dst (src.setWidth 5))) := by
  unfold encodeMovqMmR64
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeMmxGprW_spec 0x6E dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact movq_mm_r64_triple_of_bytes p rex hrex modrm hmod

attribute [x86_compose] movqMmR64Effect

@[x86_local] theorem movqMmR64Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {src : BitVec 5} :
    Effect.Local (movqMmR64Effect p len dst src) := by
  effect_local [movqMmR64Effect, mmxEffect]

end X86Proofs
