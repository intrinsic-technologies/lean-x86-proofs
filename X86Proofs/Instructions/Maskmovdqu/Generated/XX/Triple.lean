import X86Proofs.Instructions.Maskmovdqu.Generated.XX.Step
import X86Proofs.Instructions.Maskmovdqu.Generated.XX.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def maskmovdquXmmXmmEffect (p : BitVec 64) (len : Nat) (src mask : BitVec 5) :
    RamState → Effect :=
  storeEffect p len (fun s => rdi.read s) fun s =>
    maskmovdquSpec ((Operand.xmm src : Operand 128).read s)
      ((Operand.xmm mask : Operand 128).read s)
      ((Operand.mem (rdi.read s) : Operand 128).read s)

@[simp] theorem maskmovdquXmmXmmEffect_components (p : BitVec 64) (len : Nat) (src mask : BitVec 5)
    (s : RamState) :
    (maskmovdquXmmXmmEffect p len src mask s).components = [.mem (rdi.read s) 16, .rip] := by
  simp [maskmovdquXmmXmmEffect]

def maskmovdquXmmXmmSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (src mask : BitVec 5) :
    RamState → Effect :=
  storeEffect p len (fun s => base + rdi.read s) fun s =>
    maskmovdquSpec ((Operand.xmm src : Operand 128).read s)
      ((Operand.xmm mask : Operand 128).read s)
      ((Operand.mem (base + rdi.read s) : Operand 128).read s)

@[simp] theorem maskmovdquXmmXmmSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (src mask : BitVec 5) (s : RamState) :
    (maskmovdquXmmXmmSegEffect p len base src mask s).components =
      [.mem (base + rdi.read s) 16, .rip] := by
  simp [maskmovdquXmmXmmSegEffect]

theorem maskmovdqu_xmm_xmm_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (Sse2StoreNPre p 4 (fun s => rdi.read s) 16)
      (codeRange p [0x66, 0x0F, 0xF7, modrm])
      (maskmovdquXmmXmmEffect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))) := by
  refine StepEffect.of_maskmov _ (fun s => (Operand.xmm (gprNumber 0 0 (modrmReg modrm)) :
    Operand 128).read s) (fun s => (Operand.xmm (gprNumber 0 0 (modrmRm modrm)) :
    Operand 128).read s) (fun _ hpre => hpre.store) fun s h hcode hpre => ?_
  have hp := hpre.store.rip
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  exact maskmovdqu_xmm_xmm_step s h hpre.sse hpre.sse2 [0x66]
    (by simpa using scanPrefix_66) (by simp)
    rfl rfl rfl rfl rfl rfl rfl (by intro h; cases h)
    modrm hmod hcode.bytesAt hlow hpre.store.write

theorem maskmovdqu_xmm_xmm_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (Sse2StoreNPre p 4 (fun s => rdi.read s) 16)
      (codeRange p [0x66, 0x0F, 0xF7, modrm])
      (Effect.post (maskmovdquXmmXmmEffect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (n := 128) (by simp) _ _ hpre.store)
    (maskmovdqu_xmm_xmm_effect_step p modrm hmod)

theorem maskmovdqu_xmm_xmm_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8) (hmod : modrmMod modrm = 3) :
    StepEffect
      (Sse2StoreNPre p 5 (fun s => rdi.read s) 16)
      (codeRange p [0x66, rex, 0x0F, 0xF7, modrm])
      (maskmovdquXmmXmmEffect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  refine StepEffect.of_maskmov _
    (fun s => (Operand.xmm (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) : Operand 128).read s)
    (fun s => (Operand.xmm (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 128).read s)
    (fun _ hpre => hpre.store) fun s h hcode hpre => ?_
  have hp := hpre.store.rip
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hc := scanContext_66_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := maskmovdqu_xmm_xmm_step s h hpre.sse hpre.sse2 [0x66, rex]
    (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; intro h; cases h)
    modrm hmod hcode.bytesAt hlow (by rw [hc]; exact hpre.store.write)
  simp only [hc] at hstep
  exact hstep

theorem maskmovdqu_xmm_xmm_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8) (hmod : modrmMod modrm = 3) :
    Triple
      (Sse2StoreNPre p 5 (fun s => rdi.read s) 16)
      (codeRange p [0x66, rex, 0x0F, 0xF7, modrm])
      (Effect.post (maskmovdquXmmXmmEffect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (n := 128) (by simp) _ _ hpre.store)
    (maskmovdqu_xmm_xmm_rex_effect_step p rex hr modrm hmod)

theorem maskmovdqu_xmm_xmm_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (modrm : UInt8) (hmod : modrmMod modrm = 3) :
    StepEffect
      (fun s => Sse2StoreNPre p 5 (fun t => base + rdi.read t) 16 s ∧ r.Ready base s)
      (codeRange p [r.prefixByte, 0x66, 0x0F, 0xF7, modrm])
      (maskmovdquXmmXmmSegEffect p 5 base (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))) := by
  refine StepEffect.of_maskmov _
    (fun s => (Operand.xmm (gprNumber 0 0 (modrmReg modrm)) : Operand 128).read s)
    (fun s => (Operand.xmm (gprNumber 0 0 (modrmRm modrm)) : Operand 128).read s)
    (fun _ hpre => hpre.1.store) fun s h hcode hpre => ?_
  obtain ⟨hpre, hseg, hbase⟩ := hpre
  have hp := hpre.store.rip
  subst hp hbase
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66]
      (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := maskmovdqu_xmm_xmm_step s h hpre.sse hpre.sse2 [r.prefixByte, 0x66]
    (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; exact fun _ => hseg)
    modrm hmod hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.store.write)
  simp only [hsc, segAddr_withSeg] at hstep
  exact hstep

theorem maskmovdqu_xmm_xmm_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (modrm : UInt8) (hmod : modrmMod modrm = 3) :
    Triple
      (fun s => Sse2StoreNPre p 5 (fun t => base + rdi.read t) 16 s ∧ r.Ready base s)
      (codeRange p [r.prefixByte, 0x66, 0x0F, 0xF7, modrm])
      (Effect.post (maskmovdquXmmXmmSegEffect p 5 base (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (n := 128) (by simp) _ _ hpre.1.store)
    (maskmovdqu_xmm_xmm_seg_effect_step p r base modrm hmod)

theorem maskmovdqu_xmm_xmm_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8) (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect
      (fun s => Sse2StoreNPre p 6 (fun t => base + rdi.read t) 16 s ∧ r.Ready base s)
      (codeRange p [r.prefixByte, 0x66, rex, 0x0F, 0xF7, modrm])
      (maskmovdquXmmXmmSegEffect p 6 base (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  refine StepEffect.of_maskmov _
    (fun s => (Operand.xmm (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) : Operand 128).read s)
    (fun s => (Operand.xmm (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 128).read s)
    (fun _ hpre => hpre.1.store) fun s h hcode hpre => ?_
  obtain ⟨hpre, hseg, hbase⟩ := hpre
  have hp := hpre.store.rip
  subst hp hbase
  have hlow : s.RIP.toNat + 6 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66, rex] =
      withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66, rex]
      (noSegPrefix_cons noSegPrefix_66 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)),
      scanContext_66_rex s.DS (PrefixSegments.ofState s) hr]
  have hstep := maskmovdqu_xmm_xmm_step s h hpre.sse hpre.sse2 [r.prefixByte, 0x66, rex]
    (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; exact fun _ => hseg)
    modrm hmod hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.store.write)
  simp only [hsc, segAddr_withSeg] at hstep
  exact hstep

theorem maskmovdqu_xmm_xmm_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8) (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple
      (fun s => Sse2StoreNPre p 6 (fun t => base + rdi.read t) 16 s ∧ r.Ready base s)
      (codeRange p [r.prefixByte, 0x66, rex, 0x0F, 0xF7, modrm])
      (Effect.post (maskmovdquXmmXmmSegEffect p 6 base
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (n := 128) (by simp) _ _ hpre.1.store)
    (maskmovdqu_xmm_xmm_rex_seg_effect_step p r base rex hr modrm hmod)

theorem maskmovdqu_xmm_xmm_triple [Bindings] (p : BitVec 64) (src mask : BitVec 4) :
    Triple (Sse2StoreNPre p (encodeMaskmovdquXmmXmm src mask).length (fun s => rdi.read s) 16)
      (codeRange p (encodeMaskmovdquXmmXmm src mask))
      (Effect.post (maskmovdquXmmXmmEffect p (encodeMaskmovdquXmmXmm src mask).length
        (src.setWidth 5) (mask.setWidth 5))) := by
  unfold encodeMaskmovdquXmmXmm
  rcases encodeSseRegReg_spec 0xF7 src mask with ⟨modrm, hbytes, hmod, hreg, hrm⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hrm⟩
  · rw [hbytes, ← hreg, ← hrm]
    exact maskmovdqu_xmm_xmm_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hreg, ← hrm]
    exact maskmovdqu_xmm_xmm_rex_triple_of_bytes p rex hrex modrm hmod

theorem maskmovdqu_xmm_xmm_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src mask : BitVec 4) :
    Triple
      (fun s => Sse2StoreNPre p (r.prefixByte :: encodeMaskmovdquXmmXmm src mask).length
        (fun t => base + rdi.read t) 16 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: encodeMaskmovdquXmmXmm src mask))
      (Effect.post (maskmovdquXmmXmmSegEffect p
        (r.prefixByte :: encodeMaskmovdquXmmXmm src mask).length base
        (src.setWidth 5) (mask.setWidth 5))) := by
  unfold encodeMaskmovdquXmmXmm
  rcases encodeSseRegReg_spec 0xF7 src mask with ⟨modrm, hbytes, hmod, hreg, hrm⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hrm⟩
  · rw [hbytes, ← hreg, ← hrm]
    exact maskmovdqu_xmm_xmm_seg_triple_of_bytes p r base modrm hmod
  · rw [hbytes, ← hreg, ← hrm]
    exact maskmovdqu_xmm_xmm_rex_seg_triple_of_bytes p r base rex hrex modrm hmod

attribute [x86_compose] maskmovdquXmmXmmEffect

@[x86_local] theorem maskmovdquXmmXmmEffect_local {p : BitVec 64} {len : Nat}
    {src mask : BitVec 5} :
    Effect.Local (maskmovdquXmmXmmEffect p len src mask) := by
  effect_local [maskmovdquXmmXmmEffect, storeEffect]

attribute [x86_compose] maskmovdquXmmXmmSegEffect

@[x86_local] theorem maskmovdquXmmXmmSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src mask : BitVec 5} :
    Effect.Local (maskmovdquXmmXmmSegEffect p len base src mask) := by
  effect_local [maskmovdquXmmXmmSegEffect, storeEffect]

end X86Proofs
