import X86Proofs.Instructions.Movnti.Generated.MR64.Step
import X86Proofs.Instructions.Movnti.Generated.MR64.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movntiM64R64Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr s (p + BitVec.ofNat 64 len))
    fun s => movSpec ((Operand.reg src : Operand 64).read s)

@[simp] theorem movntiM64R64Effect_components (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (am : AddrMode) (s : RamState) : (movntiM64R64Effect p len src am s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) 8, .rip] := by
  simp [movntiM64R64Effect]

def movntiM64R64SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (src : BitVec 5)
    (am : AddrMode) : RamState → Effect :=
  storeEffect p len (fun s => base + am.addr s (p + BitVec.ofNat 64 len))
    fun s => movSpec ((Operand.reg src : Operand 64).read s)

@[simp] theorem movntiM64R64SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (src : BitVec 5) (am : AddrMode) (s : RamState) :
    (movntiM64R64SegEffect p len base src am s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) 8, .rip] := by
  simp [movntiM64R64SegEffect]

def movntiM64R64A32Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr32 s (p + BitVec.ofNat 64 len))
    fun s => movSpec ((Operand.reg src : Operand 64).read s)

@[simp] theorem movntiM64R64A32Effect_components (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (am : AddrMode) (s : RamState) : (movntiM64R64A32Effect p len src am s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) 8, .rip] := by
  simp [movntiM64R64A32Effect]

theorem movnti_m64_r64_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (Sse2GprStorePre p (4 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (rex :: 0x0F :: 0xC3 :: am.modrm reg :: am.tail))
      (movntiM64R64Effect p (4 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  refine StepEffect.of_store_pre (n := 64) (by decide) (by decide) _ _
    (fun _ hpre => hpre.store) fun s h hcode hpre => ?_
  have hp := hpre.store.rip
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr.rexPrefix
  have hstep := movnti_m64_r64_step s h hpre.sse2 [rex]
    (by simpa using hr.rexPrefix.scanPrefix) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; exact hr.rex_w s.DS) (by rw [hc]; rfl) (by rw [hc]; rfl)
    reg am hv (by rw [hc]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [hc]; exact hpre.store.write)
  simp only [hc] at hstep
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movnti_m64_r64_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (Sse2GprStorePre p (4 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (rex :: 0x0F :: 0xC3 :: am.modrm reg :: am.tail))
      (Effect.post (movntiM64R64Effect p (4 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (movnti_m64_r64_rex_effect_step p rex hr reg am hv hx hb)

theorem movnti_m64_r64_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => Sse2GprStorePre p (5 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xC3 :: am.modrm reg :: am.tail))
      (movntiM64R64SegEffect p (5 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  refine StepEffect.of_store_pre (n := 64) (by decide) (by decide) _ _
    (fun _ hpre => hpre.1.store) fun s h hcode hpre => ?_
  obtain ⟨hpre, hseg, hbase⟩ := hpre
  have hp := hpre.store.rip
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.rexPrefix.noSegPrefix noSegPrefix_nil), scanContext_rex s.DS (PrefixSegments.ofState s) hr.rexPrefix]
  have hstep := movnti_m64_r64_step s h hpre.sse2 [r.prefixByte, rex]
    (scanPrefix_seg_cons r (by simpa using hr.rexPrefix.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; exact hr.rex_w s.DS) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.store.write)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movnti_m64_r64_rex_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => Sse2GprStorePre p (5 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xC3 :: am.modrm reg :: am.tail))
      (Effect.post (movntiM64R64SegEffect p (5 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1.store)
    (movnti_m64_r64_rex_seg_effect_step p r base rex hr reg am hv hx hb)

theorem movnti_m64_r64_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (Sse2GprStorePre p (5 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xC3 :: am.modrm reg :: am.tail))
      (movntiM64R64A32Effect p (5 + am.tail.length)
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
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex s.DS (PrefixSegments.ofState s) hr.rexPrefix]
  have hstep := movnti_m64_r64_a32_step s h hpre.sse2 [0x67, rex]
    (scanPrefix_asz_cons (by simpa using hr.rexPrefix.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; exact hr.rex_w s.DS) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.store.write)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (rexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (rexContext s.DS rex.toBitVec)).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movnti_m64_r64_rex_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (Sse2GprStorePre p (5 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xC3 :: am.modrm reg :: am.tail))
      (Effect.post (movntiM64R64A32Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (movnti_m64_r64_rex_a32_effect_step p rex hr reg am hv hx hb)

theorem movnti_m64_r64_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (Sse2GprStorePre p (encodeMovntiM64R64 src am).length
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeMovntiM64R64 src am).length)) 8)
      (codeRange p (encodeMovntiM64R64 src am))
      (Effect.post (movntiM64R64Effect p (encodeMovntiM64R64 src am).length
        (src.setWidth 5) am)) := by
  unfold encodeMovntiM64R64
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := movnti_m64_r64_rex_triple_of_bytes p _ hrex (regLow src) am hv hx hb
  rw [hr, gprNumber_reg] at this
  have hl : (am.rexByte true src :: 0x0F :: 0xC3 :: am.modrm (regLow src) ::
      am.tail).length = 4 + am.tail.length := by simp; omega
  unfold encodeSseMemW
  rw [hl]
  exact this

theorem movnti_m64_r64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple
      (fun s => Sse2GprStorePre p (r.prefixByte :: encodeMovntiM64R64 src am).length
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeMovntiM64R64 src am).length)) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: encodeMovntiM64R64 src am))
      (Effect.post (movntiM64R64SegEffect p (r.prefixByte :: encodeMovntiM64R64 src am).length base
        (src.setWidth 5) am)) := by
  unfold encodeMovntiM64R64
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := movnti_m64_r64_rex_seg_triple_of_bytes p r base _ hrex (regLow src) am hv hx hb
  rw [hr, gprNumber_reg] at this
  have hl : (r.prefixByte :: am.rexByte true src :: 0x0F :: 0xC3 ::
      am.modrm (regLow src) :: am.tail).length = 5 + am.tail.length := by simp; omega
  unfold encodeSseMemW
  rw [hl]
  exact this

attribute [x86_compose] movntiM64R64Effect

@[x86_local] theorem movntiM64R64Effect_local {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} :
    Effect.Local (movntiM64R64Effect p len src am) := by
  effect_local [movntiM64R64Effect, storeEffect]

attribute [x86_compose] movntiM64R64SegEffect

@[x86_local] theorem movntiM64R64SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 5} {am : AddrMode} :
    Effect.Local (movntiM64R64SegEffect p len base src am) := by
  effect_local [movntiM64R64SegEffect, storeEffect]

theorem movnti_m64_r64_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (Sse2GprStorePre p (0x67 :: encodeMovntiM64R64 src am).length
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeMovntiM64R64 src am).length)) 8)
      (codeRange p (0x67 :: encodeMovntiM64R64 src am))
      (Effect.post (movntiM64R64A32Effect p (0x67 :: encodeMovntiM64R64 src am).length
        (src.setWidth 5) am)) := by
  unfold encodeMovntiM64R64
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := movnti_m64_r64_rex_a32_triple_of_bytes p _ hrex (regLow src) am hv hx hb
  rw [hr, gprNumber_reg] at this
  have hl : (0x67 :: am.rexByte true src :: 0x0F :: 0xC3 ::
      am.modrm (regLow src) :: am.tail).length = 5 + am.tail.length := by simp; omega
  unfold encodeSseMemW
  rw [hl]
  exact this

attribute [x86_compose] movntiM64R64A32Effect

@[x86_local] theorem movntiM64R64A32Effect_local {p : BitVec 64} {len : Nat}
    {src : BitVec 5} {am : AddrMode} :
    Effect.Local (movntiM64R64A32Effect p len src am) := by
  effect_local [movntiM64R64A32Effect, storeEffect]

end X86Proofs
