import X86Proofs.Instructions.Maskmovq.Generated.MM.Step
import X86Proofs.Instructions.Maskmovq.Generated.MM.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def maskmovqMmMmEffect (p : BitVec 64) (len : Nat) (src mask : BitVec 3) (s : RamState) :
    Effect :=
  (storeEffect p len (fun s => rdi.read s) (fun s =>
    maskmovqSpec ((Operand.mmx src : Operand 64).read s) ((Operand.mmx mask : Operand 64).read s)
      ((Operand.mem (rdi.read s) : Operand 64).read s)) s).withMmx s

@[simp] theorem maskmovqMmMmEffect_components (p : BitVec 64) (len : Nat) (src mask : BitVec 3)
    (s : RamState) :
    (maskmovqMmMmEffect p len src mask s).components = [.mem (rdi.read s) 8, .fsw, .ftw, .rip] := by
  simp [maskmovqMmMmEffect, storeEffect, Effect.withMmx, Effect.components]

def maskmovqMmMmSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (src mask : BitVec 3)
    (s : RamState) : Effect :=
  (storeEffect p len (fun s => base + rdi.read s) (fun s =>
    maskmovqSpec ((Operand.mmx src : Operand 64).read s) ((Operand.mmx mask : Operand 64).read s)
      ((Operand.mem (base + rdi.read s) : Operand 64).read s)) s).withMmx s

@[simp] theorem maskmovqMmMmSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (src mask : BitVec 3) (s : RamState) :
    (maskmovqMmMmSegEffect p len base src mask s).components =
      [.mem (base + rdi.read s) 8, .fsw, .ftw, .rip] := by
  simp [maskmovqMmMmSegEffect, storeEffect, Effect.withMmx, Effect.components]

theorem maskmovq_mm_mm_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (MmxStorePre p 3 (fun s => rdi.read s) 8)
      (codeRange p [0x0F, 0xF7, modrm])
      (maskmovqMmMmEffect p 3 (modrmReg modrm) (modrmRm modrm)) := by
  refine StepEffect.of_maskStateN_mmx (n := 64) (by decide) (by decide) _
    (fun s => (Operand.mmx (modrmReg modrm) : Operand 64).read s)
    (fun s => (Operand.mmx (modrmRm modrm) : Operand 64).read s) (fun o => oracleSkip o 464)
    (fun _ hpre => hpre.store) fun s h hcode hpre => ?_
  have hp := hpre.store.rip
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  exact maskmovq_mm_mm_step s h hpre.cr0 hpre.es hpre.mmx [] (by simp) (by simp)
    rfl rfl rfl rfl rfl rfl (by intro h; cases h)
    modrm hmod hcode.bytesAt hlow hpre.store.write

theorem maskmovq_mm_mm_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (MmxStorePre p 3 (fun s => rdi.read s) 8)
      (codeRange p [0x0F, 0xF7, modrm])
      (Effect.post (maskmovqMmMmEffect p 3 (modrmReg modrm) (modrmRm modrm))) :=
  Triple.of_effect (fun s hpre => (storeEffect_avoids (n := 64) (by simp) _ _
    hpre.store).withMmx s)
    (maskmovq_mm_mm_effect_step p modrm hmod)

theorem maskmovq_mm_mm_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (modrm : UInt8) (hmod : modrmMod modrm = 3) :
    StepEffect
      (fun s => MmxStorePre p 4 (fun t => base + rdi.read t) 8 s ∧ r.Ready base s)
      (codeRange p [r.prefixByte, 0x0F, 0xF7, modrm])
      (maskmovqMmMmSegEffect p 4 base (modrmReg modrm) (modrmRm modrm)) := by
  refine StepEffect.of_maskStateN_mmx (n := 64) (by decide) (by decide) _
    (fun s => (Operand.mmx (modrmReg modrm) : Operand 64).read s)
    (fun s => (Operand.mmx (modrmRm modrm) : Operand 64).read s) (fun o => oracleSkip o 464)
    (fun _ hpre => hpre.1.store) fun s h hcode hpre => ?_
  obtain ⟨hpre, hseg, hbase⟩ := hpre
  have hp := hpre.store.rip
  subst hp hbase
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [] noSegPrefix_nil]
  have hstep := maskmovq_mm_mm_step s h hpre.cr0 hpre.es hpre.mmx [r.prefixByte]
    (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; exact fun _ => hseg)
    modrm hmod hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.store.write)
  simp only [hsc, segAddr_withSeg] at hstep
  exact hstep

theorem maskmovq_mm_mm_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (modrm : UInt8) (hmod : modrmMod modrm = 3) :
    Triple
      (fun s => MmxStorePre p 4 (fun t => base + rdi.read t) 8 s ∧ r.Ready base s)
      (codeRange p [r.prefixByte, 0x0F, 0xF7, modrm])
      (Effect.post (maskmovqMmMmSegEffect p 4 base (modrmReg modrm) (modrmRm modrm))) :=
  Triple.of_effect (fun s hpre => (storeEffect_avoids (n := 64) (by simp) _ _
    hpre.1.store).withMmx s)
    (maskmovq_mm_mm_seg_effect_step p r base modrm hmod)

theorem maskmovq_mm_mm_triple [Bindings] (p : BitVec 64) (src mask : BitVec 3) :
    Triple (MmxStorePre p (encodeMaskmovqMmMm src mask).length (fun s => rdi.read s) 8)
      (codeRange p (encodeMaskmovqMmMm src mask))
      (Effect.post (maskmovqMmMmEffect p (encodeMaskmovqMmMm src mask).length src mask)) := by
  obtain ⟨modrm, hbytes, hmod, hreg, hrm⟩ := encodeMmxRegReg_spec 0xF7 src mask
  unfold encodeMaskmovqMmMm
  rw [hbytes, ← hreg, ← hrm]
  exact maskmovq_mm_mm_triple_of_bytes p modrm hmod

theorem maskmovq_mm_mm_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src mask : BitVec 3) :
    Triple
      (fun s => MmxStorePre p (r.prefixByte :: encodeMaskmovqMmMm src mask).length
        (fun t => base + rdi.read t) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: encodeMaskmovqMmMm src mask))
      (Effect.post (maskmovqMmMmSegEffect p (r.prefixByte :: encodeMaskmovqMmMm src mask).length
        base src mask)) := by
  obtain ⟨modrm, hbytes, hmod, hreg, hrm⟩ := encodeMmxRegReg_spec 0xF7 src mask
  unfold encodeMaskmovqMmMm
  rw [hbytes, ← hreg, ← hrm]
  exact maskmovq_mm_mm_seg_triple_of_bytes p r base modrm hmod

attribute [x86_compose] maskmovqMmMmEffect maskmovqMmMmSegEffect

@[x86_local] theorem maskmovqMmMmEffect_local {p : BitVec 64} {len : Nat} {src mask : BitVec 3} :
    Effect.Local (maskmovqMmMmEffect p len src mask) := by
  effect_local [maskmovqMmMmEffect, storeEffect, Effect.withMmx]

@[x86_local] theorem maskmovqMmMmSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src mask : BitVec 3} :
    Effect.Local (maskmovqMmMmSegEffect p len base src mask) := by
  effect_local [maskmovqMmMmSegEffect, storeEffect, Effect.withMmx]

end X86Proofs
