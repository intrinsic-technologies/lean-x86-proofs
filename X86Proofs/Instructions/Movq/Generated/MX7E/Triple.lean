import X86Proofs.Instructions.Movq.Generated.MX7E.Step
import X86Proofs.Instructions.Movq.Generated.MX7E.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movqM64XmmRexwEffect (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr s (p + BitVec.ofNat 64 len))
    fun s => movdSpec 64 64 ((Operand.xmm src : Operand 128).read s)

@[simp] theorem movqM64XmmRexwEffect_components (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (am : AddrMode) (s : RamState) : (movqM64XmmRexwEffect p len src am s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) 8, .rip] := by
  simp [movqM64XmmRexwEffect]

def movqM64XmmRexwSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (src : BitVec 5)
    (am : AddrMode) : RamState → Effect :=
  storeEffect p len (fun s => base + am.addr s (p + BitVec.ofNat 64 len))
    fun s => movdSpec 64 64 ((Operand.xmm src : Operand 128).read s)

@[simp] theorem movqM64XmmRexwSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (src : BitVec 5) (am : AddrMode) (s : RamState) :
    (movqM64XmmRexwSegEffect p len base src am s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) 8, .rip] := by
  simp [movqM64XmmRexwSegEffect]

def movqM64XmmRexwA32Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr32 s (p + BitVec.ofNat 64 len))
    fun s => movdSpec 64 64 ((Operand.xmm src : Operand 128).read s)

@[simp] theorem movqM64XmmRexwA32Effect_components (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (am : AddrMode) (s : RamState) : (movqM64XmmRexwA32Effect p len src am s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) 8, .rip] := by
  simp [movqM64XmmRexwA32Effect]

theorem movq_m64_xmm_rexw_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (Sse2StoreNPre p (5 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (0x66 :: rex :: 0x0F :: 0x7E :: am.modrm reg :: am.tail))
      (movqM64XmmRexwEffect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  refine StepEffect.of_store_pre (n := 64) (by decide) (by decide) _ _
    (fun _ hpre => hpre.store) fun s h hcode hpre => ?_
  have hp := hpre.store.rip
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hc := scanContext_66_rex s.DS (PrefixSegments.ofState s) hr.rexPrefix
  have hstep := movq_m64_xmm_rexw_step s h hpre.sse hpre.sse2 [0x66, rex]
    (by simp [scanPrefix_66, hr.rexPrefix.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; exact hr.rex_w s.DS) (by rw [hc]; rfl) (by rw [hc]; rfl)
    reg am hv (by rw [hc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [hc]; exact hpre.store.write)
  simp only [hc] at hstep
  have hsrc : gprNumber (oszRexContext s.DS rex.toBitVec).rex_r4
      (oszRexContext s.DS rex.toBitVec).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movq_m64_xmm_rexw_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (Sse2StoreNPre p (5 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (0x66 :: rex :: 0x0F :: 0x7E :: am.modrm reg :: am.tail))
      (Effect.post (movqM64XmmRexwEffect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (movq_m64_xmm_rexw_rex_effect_step p rex hr reg am hv hx hb)

theorem movq_m64_xmm_rexw_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => Sse2StoreNPre p (6 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (6 + am.tail.length))) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: 0x7E :: am.modrm reg :: am.tail))
      (movqM64XmmRexwSegEffect p (6 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  refine StepEffect.of_store_pre (n := 64) (by decide) (by decide) _ _
    (fun _ hpre => hpre.1.store) fun s h hcode hpre => ?_
  obtain ⟨hpre, hseg, hbase⟩ := hpre
  have hp := hpre.store.rip
  subst hp hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66, rex] =
      withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66, rex]
      (noSegPrefix_cons noSegPrefix_66 (noSegPrefix_cons hr.rexPrefix.noSegPrefix noSegPrefix_nil)), scanContext_66_rex s.DS (PrefixSegments.ofState s) hr.rexPrefix]
  have hstep := movq_m64_xmm_rexw_step s h hpre.sse hpre.sse2 [r.prefixByte, 0x66, rex]
    (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.rexPrefix.scanPrefix])) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; exact hr.rex_w s.DS) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.store.write)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movq_m64_xmm_rexw_rex_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => Sse2StoreNPre p (6 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (6 + am.tail.length))) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: 0x7E :: am.modrm reg :: am.tail))
      (Effect.post (movqM64XmmRexwSegEffect p (6 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1.store)
    (movq_m64_xmm_rexw_rex_seg_effect_step p r base rex hr reg am hv hx hb)

theorem movq_m64_xmm_rexw_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (Sse2StoreNPre p (6 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 8)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: 0x7E :: am.modrm reg :: am.tail))
      (movqM64XmmRexwA32Effect p (6 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  refine StepEffect.of_store_pre (n := 64) (by decide) (by decide) _ _
    (fun _ hpre => hpre.store) fun s h hcode hpre => ?_
  have hp := hpre.store.rip
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, rex] =
      withAsz (oszRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_66_rex s.DS (PrefixSegments.ofState s) hr.rexPrefix]
  have hstep := movq_m64_xmm_rexw_a32_step s h hpre.sse hpre.sse2 [0x67, 0x66, rex]
    (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.rexPrefix.scanPrefix])) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; exact hr.rex_w s.DS) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.store.write)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (oszRexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (oszRexContext s.DS rex.toBitVec)).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movq_m64_xmm_rexw_rex_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (Sse2StoreNPre p (6 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 8)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: 0x7E :: am.modrm reg :: am.tail))
      (Effect.post (movqM64XmmRexwA32Effect p (6 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (movq_m64_xmm_rexw_rex_a32_effect_step p rex hr reg am hv hx hb)

theorem movq_m64_xmm_rexw_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (Sse2StoreNPre p (encodeMovqM64XmmRexw src am).length
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeMovqM64XmmRexw src am).length)) 8)
      (codeRange p (encodeMovqM64XmmRexw src am))
      (Effect.post (movqM64XmmRexwEffect p (encodeMovqM64XmmRexw src am).length
        (src.setWidth 5) am)) := by
  unfold encodeMovqM64XmmRexw
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := movq_m64_xmm_rexw_rex_triple_of_bytes p _ hrex (regLow src) am hv hx hb
  rw [hr, gprNumber_reg] at this
  have hl : (0x66 :: am.rexByte true src :: 0x0F :: 0x7E :: am.modrm (regLow src) ::
      am.tail).length = 5 + am.tail.length := by simp; omega
  unfold encodeSseMemW
  rw [hl]
  exact this

theorem movq_m64_xmm_rexw_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple
      (fun s => Sse2StoreNPre p (r.prefixByte :: encodeMovqM64XmmRexw src am).length
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeMovqM64XmmRexw src am).length)) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: encodeMovqM64XmmRexw src am))
      (Effect.post (movqM64XmmRexwSegEffect p (r.prefixByte :: encodeMovqM64XmmRexw src am).length base
        (src.setWidth 5) am)) := by
  unfold encodeMovqM64XmmRexw
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := movq_m64_xmm_rexw_rex_seg_triple_of_bytes p r base _ hrex (regLow src) am hv hx hb
  rw [hr, gprNumber_reg] at this
  have hl : (r.prefixByte :: 0x66 :: am.rexByte true src :: 0x0F :: 0x7E ::
      am.modrm (regLow src) :: am.tail).length = 6 + am.tail.length := by simp; omega
  unfold encodeSseMemW
  rw [hl]
  exact this

attribute [x86_compose] movqM64XmmRexwEffect

@[x86_local] theorem movqM64XmmRexwEffect_local {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} :
    Effect.Local (movqM64XmmRexwEffect p len src am) := by
  effect_local [movqM64XmmRexwEffect, storeEffect]

attribute [x86_compose] movqM64XmmRexwSegEffect

@[x86_local] theorem movqM64XmmRexwSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 5} {am : AddrMode} :
    Effect.Local (movqM64XmmRexwSegEffect p len base src am) := by
  effect_local [movqM64XmmRexwSegEffect, storeEffect]

theorem movq_m64_xmm_rexw_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (Sse2StoreNPre p (0x67 :: encodeMovqM64XmmRexw src am).length
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeMovqM64XmmRexw src am).length)) 8)
      (codeRange p (0x67 :: encodeMovqM64XmmRexw src am))
      (Effect.post (movqM64XmmRexwA32Effect p (0x67 :: encodeMovqM64XmmRexw src am).length
        (src.setWidth 5) am)) := by
  unfold encodeMovqM64XmmRexw
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := movq_m64_xmm_rexw_rex_a32_triple_of_bytes p _ hrex (regLow src) am hv hx hb
  rw [hr, gprNumber_reg] at this
  have hl : (0x67 :: 0x66 :: am.rexByte true src :: 0x0F :: 0x7E ::
      am.modrm (regLow src) :: am.tail).length = 6 + am.tail.length := by simp; omega
  unfold encodeSseMemW
  rw [hl]
  exact this

attribute [x86_compose] movqM64XmmRexwA32Effect

@[x86_local] theorem movqM64XmmRexwA32Effect_local {p : BitVec 64} {len : Nat}
    {src : BitVec 5} {am : AddrMode} :
    Effect.Local (movqM64XmmRexwA32Effect p len src am) := by
  effect_local [movqM64XmmRexwA32Effect, storeEffect]

end X86Proofs
