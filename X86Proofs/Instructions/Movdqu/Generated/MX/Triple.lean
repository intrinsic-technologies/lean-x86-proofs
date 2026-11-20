import X86Proofs.Instructions.Movdqu.Generated.MX.Step
import X86Proofs.Instructions.Movdqu.Generated.MX.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movdquM128XmmEffect (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr s (p + BitVec.ofNat 64 len))
    fun s => ((Operand.xmm src : Operand 128).read s)

@[simp] theorem movdquM128XmmEffect_components (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (am : AddrMode) (s : RamState) : (movdquM128XmmEffect p len src am s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) 16, .rip] := by
  simp [movdquM128XmmEffect]

def movdquM128XmmSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (src : BitVec 5)
    (am : AddrMode) : RamState → Effect :=
  storeEffect p len (fun s => base + am.addr s (p + BitVec.ofNat 64 len))
    fun s => ((Operand.xmm src : Operand 128).read s)

@[simp] theorem movdquM128XmmSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (src : BitVec 5) (am : AddrMode) (s : RamState) :
    (movdquM128XmmSegEffect p len base src am s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) 16, .rip] := by
  simp [movdquM128XmmSegEffect]

def movdquM128XmmA32Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr32 s (p + BitVec.ofNat 64 len))
    fun s => ((Operand.xmm src : Operand 128).read s)

@[simp] theorem movdquM128XmmA32Effect_components (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (am : AddrMode) (s : RamState) : (movdquM128XmmA32Effect p len src am s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) 16, .rip] := by
  simp [movdquM128XmmA32Effect]

theorem movdqu_m128_xmm_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (Sse2StoreNPre p (4 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 16)
      (codeRange p (0xF3 :: 0x0F :: 0x7F :: am.modrm reg :: am.tail))
      (movdquM128XmmEffect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am) := by
  refine StepEffect.of_store_pre (n := 128) (by decide) (by decide) _ _
    (fun _ hpre => hpre.store) fun s h hcode hpre => ?_
  have hp := hpre.store.rip
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := movdqu_m128_xmm_step s h hpre.sse hpre.sse2 [0xF3]
    (by simpa using scanPrefix_f3) (by simp)
    rfl rfl rfl
    rfl
    reg am hv (AddrContext.rep _ am hx hb).toSeg
    hcode.bytesAt hlow hpre.store.write
  dsimp only at hstep
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0xF3]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0xF3]).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movdqu_m128_xmm_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (Sse2StoreNPre p (4 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 16)
      (codeRange p (0xF3 :: 0x0F :: 0x7F :: am.modrm reg :: am.tail))
      (Effect.post (movdquM128XmmEffect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (movdqu_m128_xmm_effect_step p reg am hv hx hb)

theorem movdqu_m128_xmm_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (Sse2StoreNPre p (5 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 16)
      (codeRange p (0xF3 :: rex :: 0x0F :: 0x7F :: am.modrm reg :: am.tail))
      (movdquM128XmmEffect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  refine StepEffect.of_store_pre (n := 128) (by decide) (by decide) _ _
    (fun _ hpre => hpre.store) fun s h hcode hpre => ?_
  have hp := hpre.store.rip
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hc := scanContext_f3_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := movdqu_m128_xmm_step s h hpre.sse hpre.sse2 [0xF3, rex]
    (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl)
    reg am hv (by rw [hc]; exact (AddrContext.repRex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [hc]; exact hpre.store.write)
  simp only [hc] at hstep
  have hsrc : gprNumber (repRexContext s.DS rex.toBitVec).rex_r4
      (repRexContext s.DS rex.toBitVec).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movdqu_m128_xmm_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (Sse2StoreNPre p (5 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 16)
      (codeRange p (0xF3 :: rex :: 0x0F :: 0x7F :: am.modrm reg :: am.tail))
      (Effect.post (movdquM128XmmEffect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (movdqu_m128_xmm_rex_effect_step p rex hr reg am hv hx hb)

theorem movdqu_m128_xmm_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => Sse2StoreNPre p (5 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 16 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0xF3 :: 0x0F :: 0x7F :: am.modrm reg :: am.tail))
      (movdquM128XmmSegEffect p (5 + am.tail.length) base
        (gprNumber 0 0 reg) am) := by
  refine StepEffect.of_store_pre (n := 128) (by decide) (by decide) _ _
    (fun _ hpre => hpre.1.store) fun s h hcode hpre => ?_
  obtain ⟨hpre, hseg, hbase⟩ := hpre
  have hp := hpre.store.rip
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3]
      (noSegPrefix_cons noSegPrefix_f3 noSegPrefix_nil)]
  have hstep := movdqu_m128_xmm_step s h hpre.sse hpre.sse2 [r.prefixByte, 0xF3]
    (scanPrefix_seg_cons r (by simpa using scanPrefix_f3)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rep _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.store.write)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) (r.select (PrefixSegments.ofState s))).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movdqu_m128_xmm_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => Sse2StoreNPre p (5 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 16 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0xF3 :: 0x0F :: 0x7F :: am.modrm reg :: am.tail))
      (Effect.post (movdquM128XmmSegEffect p (5 + am.tail.length) base
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1.store)
    (movdqu_m128_xmm_seg_effect_step p r base reg am hv hx hb)

theorem movdqu_m128_xmm_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => Sse2StoreNPre p (6 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (6 + am.tail.length))) 16 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0xF3 :: rex :: 0x0F :: 0x7F :: am.modrm reg :: am.tail))
      (movdquM128XmmSegEffect p (6 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  refine StepEffect.of_store_pre (n := 128) (by decide) (by decide) _ _
    (fun _ hpre => hpre.1.store) fun s h hcode hpre => ?_
  obtain ⟨hpre, hseg, hbase⟩ := hpre
  have hp := hpre.store.rip
  subst hp hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3, rex] =
      withSeg (repRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3, rex]
      (noSegPrefix_cons noSegPrefix_f3 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_f3_rex s.DS (PrefixSegments.ofState s) hr]
  have hstep := movdqu_m128_xmm_step s h hpre.sse hpre.sse2 [r.prefixByte, 0xF3, rex]
    (scanPrefix_seg_cons r (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.repRex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.store.write)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (repRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (repRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movdqu_m128_xmm_rex_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => Sse2StoreNPre p (6 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (6 + am.tail.length))) 16 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0xF3 :: rex :: 0x0F :: 0x7F :: am.modrm reg :: am.tail))
      (Effect.post (movdquM128XmmSegEffect p (6 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1.store)
    (movdqu_m128_xmm_rex_seg_effect_step p r base rex hr reg am hv hx hb)

theorem movdqu_m128_xmm_a32_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (Sse2StoreNPre p (5 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 16)
      (codeRange p (0x67 :: 0xF3 :: 0x0F :: 0x7F :: am.modrm reg :: am.tail))
      (movdquM128XmmA32Effect p (5 + am.tail.length)
        (gprNumber 0 0 reg) am) := by
  refine StepEffect.of_store_pre (n := 128) (by decide) (by decide) _ _
    (fun _ hpre => hpre.store) fun s h hcode hpre => ?_
  have hp := hpre.store.rip
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0xF3] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) := by
    rw [scanContext_asz_cons]
  have hstep := movdqu_m128_xmm_a32_step s h hpre.sse hpre.sse2 [0x67, 0xF3]
    (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rep _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.store.write)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0xF3])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0xF3])).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movdqu_m128_xmm_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (Sse2StoreNPre p (5 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 16)
      (codeRange p (0x67 :: 0xF3 :: 0x0F :: 0x7F :: am.modrm reg :: am.tail))
      (Effect.post (movdquM128XmmA32Effect p (5 + am.tail.length)
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (movdqu_m128_xmm_a32_effect_step p reg am hv hx hb)

theorem movdqu_m128_xmm_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (Sse2StoreNPre p (6 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 16)
      (codeRange p (0x67 :: 0xF3 :: rex :: 0x0F :: 0x7F :: am.modrm reg :: am.tail))
      (movdquM128XmmA32Effect p (6 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  refine StepEffect.of_store_pre (n := 128) (by decide) (by decide) _ _
    (fun _ hpre => hpre.store) fun s h hcode hpre => ?_
  have hp := hpre.store.rip
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0xF3, rex] =
      withAsz (repRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_f3_rex s.DS (PrefixSegments.ofState s) hr]
  have hstep := movdqu_m128_xmm_a32_step s h hpre.sse hpre.sse2 [0x67, 0xF3, rex]
    (scanPrefix_asz_cons (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.repRex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.store.write)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (repRexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (repRexContext s.DS rex.toBitVec)).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movdqu_m128_xmm_rex_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (Sse2StoreNPre p (6 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 16)
      (codeRange p (0x67 :: 0xF3 :: rex :: 0x0F :: 0x7F :: am.modrm reg :: am.tail))
      (Effect.post (movdquM128XmmA32Effect p (6 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (movdqu_m128_xmm_rex_a32_effect_step p rex hr reg am hv hx hb)

theorem movdqu_m128_xmm_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (Sse2StoreNPre p (encodeMovdquM128Xmm src am).length
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeMovdquM128Xmm src am).length)) 16)
      (codeRange p (encodeMovdquM128Xmm src am))
      (Effect.post (movdquM128XmmEffect p (encodeMovdquM128Xmm src am).length
        (src.setWidth 5) am)) := by
  unfold encodeMovdquM128Xmm
  rcases encodeSseMem_spec 0x7F src am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (0xF3 :: 0x0F :: 0x7F :: am.modrm (regLow src) :: am.tail :
        List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact movdqu_m128_xmm_triple_of_bytes p (regLow src) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := movdqu_m128_xmm_rex_triple_of_bytes p _ hrex.rexPrefix (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (0xF3 :: am.rexByte false src :: 0x0F :: 0x7F :: am.modrm (regLow src) ::
        am.tail).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact this

theorem movdqu_m128_xmm_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple
      (fun s => Sse2StoreNPre p (r.prefixByte :: encodeMovdquM128Xmm src am).length
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeMovdquM128Xmm src am).length)) 16 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: encodeMovdquM128Xmm src am))
      (Effect.post (movdquM128XmmSegEffect p (r.prefixByte :: encodeMovdquM128Xmm src am).length base
        (src.setWidth 5) am)) := by
  unfold encodeMovdquM128Xmm
  rcases encodeSseMem_spec 0x7F src am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (r.prefixByte :: 0xF3 :: 0x0F :: 0x7F :: am.modrm (regLow src) ::
        am.tail : List UInt8).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact movdqu_m128_xmm_seg_triple_of_bytes p r base (regLow src) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := movdqu_m128_xmm_rex_seg_triple_of_bytes p r base _
      hrex.rexPrefix (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (r.prefixByte :: 0xF3 :: am.rexByte false src :: 0x0F :: 0x7F ::
        am.modrm (regLow src) :: am.tail).length = 6 + am.tail.length := by
      simp; omega
    rw [hbytes, hl]
    exact this

attribute [x86_compose] movdquM128XmmEffect

@[x86_local] theorem movdquM128XmmEffect_local {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} :
    Effect.Local (movdquM128XmmEffect p len src am) := by
  effect_local [movdquM128XmmEffect, storeEffect]

attribute [x86_compose] movdquM128XmmSegEffect

@[x86_local] theorem movdquM128XmmSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 5} {am : AddrMode} :
    Effect.Local (movdquM128XmmSegEffect p len base src am) := by
  effect_local [movdquM128XmmSegEffect, storeEffect]

theorem movdqu_m128_xmm_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (Sse2StoreNPre p (0x67 :: encodeMovdquM128Xmm src am).length
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeMovdquM128Xmm src am).length)) 16)
      (codeRange p (0x67 :: encodeMovdquM128Xmm src am))
      (Effect.post (movdquM128XmmA32Effect p (0x67 :: encodeMovdquM128Xmm src am).length
        (src.setWidth 5) am)) := by
  unfold encodeMovdquM128Xmm
  rcases encodeSseMem_spec 0x7F src am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (0x67 :: 0xF3 :: 0x0F :: 0x7F :: am.modrm (regLow src) ::
        am.tail : List UInt8).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact movdqu_m128_xmm_a32_triple_of_bytes p (regLow src) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := movdqu_m128_xmm_rex_a32_triple_of_bytes p _
      hrex.rexPrefix (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (0x67 :: 0xF3 :: am.rexByte false src :: 0x0F :: 0x7F ::
        am.modrm (regLow src) :: am.tail).length = 6 + am.tail.length := by
      simp; omega
    rw [hbytes, hl]
    exact this

attribute [x86_compose] movdquM128XmmA32Effect

@[x86_local] theorem movdquM128XmmA32Effect_local {p : BitVec 64} {len : Nat}
    {src : BitVec 5} {am : AddrMode} :
    Effect.Local (movdquM128XmmA32Effect p len src am) := by
  effect_local [movdquM128XmmA32Effect, storeEffect]

end X86Proofs
