import X86Proofs.Instructions.Movlps.Generated.MX.Step
import X86Proofs.Instructions.Movlps.Generated.MX.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movlpsM64XmmEffect (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr s (p + BitVec.ofNat 64 len))
    fun s => movlpStoreSpec ((Operand.xmm src : Operand 128).read s)

@[simp] theorem movlpsM64XmmEffect_components (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (am : AddrMode) (s : RamState) : (movlpsM64XmmEffect p len src am s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) 8, .rip] := by
  simp [movlpsM64XmmEffect]

def movlpsM64XmmSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (src : BitVec 5)
    (am : AddrMode) : RamState → Effect :=
  storeEffect p len (fun s => base + am.addr s (p + BitVec.ofNat 64 len))
    fun s => movlpStoreSpec ((Operand.xmm src : Operand 128).read s)

@[simp] theorem movlpsM64XmmSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (src : BitVec 5) (am : AddrMode) (s : RamState) :
    (movlpsM64XmmSegEffect p len base src am s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) 8, .rip] := by
  simp [movlpsM64XmmSegEffect]

def movlpsM64XmmA32Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr32 s (p + BitVec.ofNat 64 len))
    fun s => movlpStoreSpec ((Operand.xmm src : Operand 128).read s)

@[simp] theorem movlpsM64XmmA32Effect_components (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (am : AddrMode) (s : RamState) : (movlpsM64XmmA32Effect p len src am s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) 8, .rip] := by
  simp [movlpsM64XmmA32Effect]

theorem movlps_m64_xmm_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (SseStoreNPre p (3 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 8)
      (codeRange p (0x0F :: 0x13 :: am.modrm reg :: am.tail))
      (movlpsM64XmmEffect p (3 + am.tail.length)
        (gprNumber 0 0 reg) am) := by
  refine StepEffect.of_store_pre (n := 64) (by decide) (by decide) _ _
    (fun _ hpre => hpre.store) fun s h hcode hpre => ?_
  have hp := hpre.store.rip
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := movlps_m64_xmm_step s h hpre.sse hpre.sse.feature []
    (by simp) (by simp)
    rfl rfl rfl
    rfl rfl
    reg am hv (AddrContext.legacy _ am hx hb).toSeg
    hcode.bytesAt hlow hpre.store.write
  dsimp only at hstep
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movlps_m64_xmm_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (SseStoreNPre p (3 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 8)
      (codeRange p (0x0F :: 0x13 :: am.modrm reg :: am.tail))
      (Effect.post (movlpsM64XmmEffect p (3 + am.tail.length)
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (movlps_m64_xmm_effect_step p reg am hv hx hb)

theorem movlps_m64_xmm_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (SseStoreNPre p (4 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (rex :: 0x0F :: 0x13 :: am.modrm reg :: am.tail))
      (movlpsM64XmmEffect p (4 + am.tail.length)
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
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := movlps_m64_xmm_step s h hpre.sse hpre.sse.feature [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl)
    reg am hv (by rw [hc]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [hc]; exact hpre.store.write)
  simp only [hc] at hstep
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movlps_m64_xmm_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (SseStoreNPre p (4 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (rex :: 0x0F :: 0x13 :: am.modrm reg :: am.tail))
      (Effect.post (movlpsM64XmmEffect p (4 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (movlps_m64_xmm_rex_effect_step p rex hr reg am hv hx hb)

theorem movlps_m64_xmm_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => SseStoreNPre p (4 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x0F :: 0x13 :: am.modrm reg :: am.tail))
      (movlpsM64XmmSegEffect p (4 + am.tail.length) base
        (gprNumber 0 0 reg) am) := by
  refine StepEffect.of_store_pre (n := 64) (by decide) (by decide) _ _
    (fun _ hpre => hpre.1.store) fun s h hcode hpre => ?_
  obtain ⟨hpre, hseg, hbase⟩ := hpre
  have hp := hpre.store.rip
  subst hp hbase
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := movlps_m64_xmm_step s h hpre.sse hpre.sse.feature [r.prefixByte]
    (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.store.write)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movlps_m64_xmm_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => SseStoreNPre p (4 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x0F :: 0x13 :: am.modrm reg :: am.tail))
      (Effect.post (movlpsM64XmmSegEffect p (4 + am.tail.length) base
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1.store)
    (movlps_m64_xmm_seg_effect_step p r base reg am hv hx hb)

theorem movlps_m64_xmm_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => SseStoreNPre p (5 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x13 :: am.modrm reg :: am.tail))
      (movlpsM64XmmSegEffect p (5 + am.tail.length) base
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
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex s.DS (PrefixSegments.ofState s) hr]
  have hstep := movlps_m64_xmm_step s h hpre.sse hpre.sse.feature [r.prefixByte, rex]
    (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.store.write)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movlps_m64_xmm_rex_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => SseStoreNPre p (5 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x13 :: am.modrm reg :: am.tail))
      (Effect.post (movlpsM64XmmSegEffect p (5 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1.store)
    (movlps_m64_xmm_rex_seg_effect_step p r base rex hr reg am hv hx hb)

theorem movlps_m64_xmm_a32_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (SseStoreNPre p (4 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (0x67 :: 0x0F :: 0x13 :: am.modrm reg :: am.tail))
      (movlpsM64XmmA32Effect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am) := by
  refine StepEffect.of_store_pre (n := 64) (by decide) (by decide) _ _
    (fun _ hpre => hpre.store) fun s h hcode hpre => ?_
  have hp := hpre.store.rip
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := movlps_m64_xmm_a32_step s h hpre.sse hpre.sse.feature [0x67]
    (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.store.write)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movlps_m64_xmm_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (SseStoreNPre p (4 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (0x67 :: 0x0F :: 0x13 :: am.modrm reg :: am.tail))
      (Effect.post (movlpsM64XmmA32Effect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (movlps_m64_xmm_a32_effect_step p reg am hv hx hb)

theorem movlps_m64_xmm_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (SseStoreNPre p (5 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0x0F :: 0x13 :: am.modrm reg :: am.tail))
      (movlpsM64XmmA32Effect p (5 + am.tail.length)
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
    rw [scanContext_asz_cons, scanContext_rex s.DS (PrefixSegments.ofState s) hr]
  have hstep := movlps_m64_xmm_a32_step s h hpre.sse hpre.sse.feature [0x67, rex]
    (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.store.write)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (rexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (rexContext s.DS rex.toBitVec)).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movlps_m64_xmm_rex_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (SseStoreNPre p (5 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0x0F :: 0x13 :: am.modrm reg :: am.tail))
      (Effect.post (movlpsM64XmmA32Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (movlps_m64_xmm_rex_a32_effect_step p rex hr reg am hv hx hb)

theorem movlps_m64_xmm_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (SseStoreNPre p (encodeMovlpsM64Xmm src am).length
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeMovlpsM64Xmm src am).length)) 8)
      (codeRange p (encodeMovlpsM64Xmm src am))
      (Effect.post (movlpsM64XmmEffect p (encodeMovlpsM64Xmm src am).length
        (src.setWidth 5) am)) := by
  unfold encodeMovlpsM64Xmm
  rcases encodeSseMem_spec 0x13 src am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (0x0F :: 0x13 :: am.modrm (regLow src) :: am.tail :
        List UInt8).length = 3 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact movlps_m64_xmm_triple_of_bytes p (regLow src) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := movlps_m64_xmm_rex_triple_of_bytes p _ hrex.rexPrefix (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (am.rexByte false src :: 0x0F :: 0x13 :: am.modrm (regLow src) ::
        am.tail).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact this

theorem movlps_m64_xmm_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple
      (fun s => SseStoreNPre p (r.prefixByte :: encodeMovlpsM64Xmm src am).length
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeMovlpsM64Xmm src am).length)) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: encodeMovlpsM64Xmm src am))
      (Effect.post (movlpsM64XmmSegEffect p (r.prefixByte :: encodeMovlpsM64Xmm src am).length base
        (src.setWidth 5) am)) := by
  unfold encodeMovlpsM64Xmm
  rcases encodeSseMem_spec 0x13 src am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (r.prefixByte :: 0x0F :: 0x13 :: am.modrm (regLow src) ::
        am.tail : List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact movlps_m64_xmm_seg_triple_of_bytes p r base (regLow src) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := movlps_m64_xmm_rex_seg_triple_of_bytes p r base _
      hrex.rexPrefix (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (r.prefixByte :: am.rexByte false src :: 0x0F :: 0x13 ::
        am.modrm (regLow src) :: am.tail).length = 5 + am.tail.length := by
      simp; omega
    rw [hbytes, hl]
    exact this

attribute [x86_compose] movlpsM64XmmEffect

@[x86_local] theorem movlpsM64XmmEffect_local {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} :
    Effect.Local (movlpsM64XmmEffect p len src am) := by
  effect_local [movlpsM64XmmEffect, storeEffect]

attribute [x86_compose] movlpsM64XmmSegEffect

@[x86_local] theorem movlpsM64XmmSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 5} {am : AddrMode} :
    Effect.Local (movlpsM64XmmSegEffect p len base src am) := by
  effect_local [movlpsM64XmmSegEffect, storeEffect]

theorem movlps_m64_xmm_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (SseStoreNPre p (0x67 :: encodeMovlpsM64Xmm src am).length
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeMovlpsM64Xmm src am).length)) 8)
      (codeRange p (0x67 :: encodeMovlpsM64Xmm src am))
      (Effect.post (movlpsM64XmmA32Effect p (0x67 :: encodeMovlpsM64Xmm src am).length
        (src.setWidth 5) am)) := by
  unfold encodeMovlpsM64Xmm
  rcases encodeSseMem_spec 0x13 src am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (0x67 :: 0x0F :: 0x13 :: am.modrm (regLow src) ::
        am.tail : List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact movlps_m64_xmm_a32_triple_of_bytes p (regLow src) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := movlps_m64_xmm_rex_a32_triple_of_bytes p _
      hrex.rexPrefix (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (0x67 :: am.rexByte false src :: 0x0F :: 0x13 ::
        am.modrm (regLow src) :: am.tail).length = 5 + am.tail.length := by
      simp; omega
    rw [hbytes, hl]
    exact this

attribute [x86_compose] movlpsM64XmmA32Effect

@[x86_local] theorem movlpsM64XmmA32Effect_local {p : BitVec 64} {len : Nat}
    {src : BitVec 5} {am : AddrMode} :
    Effect.Local (movlpsM64XmmA32Effect p len src am) := by
  effect_local [movlpsM64XmmA32Effect, storeEffect]

end X86Proofs
