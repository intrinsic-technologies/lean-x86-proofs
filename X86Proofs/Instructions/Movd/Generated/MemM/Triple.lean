import X86Proofs.Instructions.Movd.Generated.MemM.Step
import X86Proofs.Instructions.Movd.Generated.MemM.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movdM32MmEffect (p : BitVec 64) (len : Nat) (src : BitVec 3) (am : AddrMode) (s : RamState) :
    Effect :=
  (storeEffect p len (fun s => am.addr s (p + BitVec.ofNat 64 len))
    (fun s => movdSpec 32 32 ((Operand.mmx src : Operand 64).read s)) s).withMmx s

@[simp] theorem movdM32MmEffect_components (p : BitVec 64) (len : Nat) (src : BitVec 3)
    (am : AddrMode) (s : RamState) : (movdM32MmEffect p len src am s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) 4, .fsw, .ftw, .rip] := by
  simp [movdM32MmEffect, storeEffect, Effect.withMmx, Effect.components]

def movdM32MmSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (src : BitVec 3)
    (am : AddrMode) (s : RamState) : Effect :=
  (storeEffect p len (fun s => base + am.addr s (p + BitVec.ofNat 64 len))
    (fun s => movdSpec 32 32 ((Operand.mmx src : Operand 64).read s)) s).withMmx s

@[simp] theorem movdM32MmSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (src : BitVec 3) (am : AddrMode) (s : RamState) :
    (movdM32MmSegEffect p len base src am s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) 4, .fsw, .ftw, .rip] := by
  simp [movdM32MmSegEffect, storeEffect, Effect.withMmx, Effect.components]

def movdM32MmA32Effect (p : BitVec 64) (len : Nat) (src : BitVec 3) (am : AddrMode) (s : RamState) :
    Effect :=
  (storeEffect p len (fun s => am.addr32 s (p + BitVec.ofNat 64 len))
    (fun s => movdSpec 32 32 ((Operand.mmx src : Operand 64).read s)) s).withMmx s

@[simp] theorem movdM32MmA32Effect_components (p : BitVec 64) (len : Nat) (src : BitVec 3)
    (am : AddrMode) (s : RamState) : (movdM32MmA32Effect p len src am s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) 4, .fsw, .ftw, .rip] := by
  simp [movdM32MmA32Effect, storeEffect, Effect.withMmx, Effect.components]

theorem movd_m32_mm_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (MmxStorePre p (3 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (0x0F :: 0x7E :: am.modrm reg :: am.tail))
      (movdM32MmEffect p (3 + am.tail.length) reg am) := by
  refine StepEffect.of_mmx_store_pre (n := 32) (by decide) (by decide) _ _
    (fun _ hpre => hpre.store) fun s h hcode hpre => ?_
  have hp := hpre.store.rip
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := movd_m32_mm_step s h hpre.cr0 hpre.es hpre.mmx []
    (by simp) (by simp)
    rfl rfl rfl rfl rfl rfl
    reg am hv (AddrContext.legacy _ am hx hb).toSeg
    hcode.bytesAt hlow hpre.store.write
  dsimp only at hstep
  exact hstep

theorem movd_m32_mm_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (MmxStorePre p (3 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (0x0F :: 0x7E :: am.modrm reg :: am.tail))
      (Effect.post (movdM32MmEffect p (3 + am.tail.length) reg am)) :=
  Triple.of_effect (fun s hpre => (storeEffect_avoids (by simp; omega) _ _
    hpre.store).withMmx s)
    (movd_m32_mm_effect_step p reg am hv hx hb)

theorem movd_m32_mm_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (MmxStorePre p (4 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (rex :: 0x0F :: 0x7E :: am.modrm reg :: am.tail))
      (movdM32MmEffect p (4 + am.tail.length) reg am) := by
  refine StepEffect.of_mmx_store_pre (n := 32) (by decide) (by decide) _ _
    (fun _ hpre => hpre.store) fun s h hcode hpre => ?_
  have hp := hpre.store.rip
  subst hp
  have hr := hrex.rexPrefix
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := movd_m32_mm_step s h hpre.cr0 hpre.es hpre.mmx [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; exact hrex.rex_w s.DS) (by rw [scanContext_rex _ _ hr]; rfl)
    reg am hv (by rw [hc]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [hc]; exact hpre.store.write)
  simp only [hc] at hstep
  exact hstep

theorem movd_m32_mm_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (MmxStorePre p (4 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (rex :: 0x0F :: 0x7E :: am.modrm reg :: am.tail))
      (Effect.post (movdM32MmEffect p (4 + am.tail.length) reg am)) :=
  Triple.of_effect (fun s hpre => (storeEffect_avoids (by simp; omega) _ _
    hpre.store).withMmx s)
    (movd_m32_mm_rex_effect_step p rex hrex reg am hv hx hb)

theorem movd_m32_mm_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => MmxStorePre p (4 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x0F :: 0x7E :: am.modrm reg :: am.tail))
      (movdM32MmSegEffect p (4 + am.tail.length) base reg am) := by
  refine StepEffect.of_mmx_store_pre (n := 32) (by decide) (by decide) _ _
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
  have hstep := movd_m32_mm_step s h hpre.cr0 hpre.es hpre.mmx [r.prefixByte]
    (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.store.write)
  simp only [hsc, segAddr_withSeg] at hstep
  exact hstep

theorem movd_m32_mm_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => MmxStorePre p (4 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x0F :: 0x7E :: am.modrm reg :: am.tail))
      (Effect.post (movdM32MmSegEffect p (4 + am.tail.length) base reg am)) :=
  Triple.of_effect (fun s hpre => (storeEffect_avoids (by simp; omega) _ _
    hpre.1.store).withMmx s)
    (movd_m32_mm_seg_effect_step p r base reg am hv hx hb)

theorem movd_m32_mm_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => MmxStorePre p (5 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 4 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x7E :: am.modrm reg :: am.tail))
      (movdM32MmSegEffect p (5 + am.tail.length) base reg am) := by
  refine StepEffect.of_mmx_store_pre (n := 32) (by decide) (by decide) _ _
    (fun _ hpre => hpre.1.store) fun s h hcode hpre => ?_
  obtain ⟨hpre, hseg, hbase⟩ := hpre
  have hp := hpre.store.rip
  subst hp hbase
  have hr := hrex.rexPrefix
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex s.DS (PrefixSegments.ofState s) hr]
  have hstep := movd_m32_mm_step s h hpre.cr0 hpre.es hpre.mmx [r.prefixByte, rex]
    (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; exact hrex.rex_w s.DS) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.store.write)
  simp only [hsc, segAddr_withSeg] at hstep
  exact hstep

theorem movd_m32_mm_rex_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => MmxStorePre p (5 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 4 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x7E :: am.modrm reg :: am.tail))
      (Effect.post (movdM32MmSegEffect p (5 + am.tail.length) base reg am)) :=
  Triple.of_effect (fun s hpre => (storeEffect_avoids (by simp; omega) _ _
    hpre.1.store).withMmx s)
    (movd_m32_mm_rex_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem movd_m32_mm_a32_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (MmxStorePre p (4 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (0x67 :: 0x0F :: 0x7E :: am.modrm reg :: am.tail))
      (movdM32MmA32Effect p (4 + am.tail.length) reg am) := by
  refine StepEffect.of_mmx_store_pre (n := 32) (by decide) (by decide) _ _
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
  have hstep := movd_m32_mm_a32_step s h hpre.cr0 hpre.es hpre.mmx [0x67]
    (scanPrefix_asz_cons (by simp)) (by simp)
    rfl rfl rfl rfl rfl rfl
    reg am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.store.write)
  simp only [hsc] at hstep
  exact hstep

theorem movd_m32_mm_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (MmxStorePre p (4 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (0x67 :: 0x0F :: 0x7E :: am.modrm reg :: am.tail))
      (Effect.post (movdM32MmA32Effect p (4 + am.tail.length) reg am)) :=
  Triple.of_effect (fun s hpre => (storeEffect_avoids (by simp; omega) _ _
    hpre.store).withMmx s)
    (movd_m32_mm_a32_effect_step p reg am hv hx hb)

theorem movd_m32_mm_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (MmxStorePre p (5 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4)
      (codeRange p (0x67 :: rex :: 0x0F :: 0x7E :: am.modrm reg :: am.tail))
      (movdM32MmA32Effect p (5 + am.tail.length) reg am) := by
  refine StepEffect.of_mmx_store_pre (n := 32) (by decide) (by decide) _ _
    (fun _ hpre => hpre.store) fun s h hcode hpre => ?_
  have hp := hpre.store.rip
  subst hp
  have hr := hrex.rexPrefix
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex s.DS (PrefixSegments.ofState s) hr]
  have hstep := movd_m32_mm_a32_step s h hpre.cr0 hpre.es hpre.mmx [0x67, rex]
    (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; exact hrex.rex_w s.DS) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.store.write)
  simp only [hsc] at hstep
  exact hstep

theorem movd_m32_mm_rex_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (MmxStorePre p (5 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4)
      (codeRange p (0x67 :: rex :: 0x0F :: 0x7E :: am.modrm reg :: am.tail))
      (Effect.post (movdM32MmA32Effect p (5 + am.tail.length) reg am)) :=
  Triple.of_effect (fun s hpre => (storeEffect_avoids (by simp; omega) _ _
    hpre.store).withMmx s)
    (movd_m32_mm_rex_a32_effect_step p rex hrex reg am hv hx hb)

theorem movd_m32_mm_triple [Bindings] (p : BitVec 64) (src : BitVec 3) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (MmxStorePre p (encodeMovdM32Mm src am).length
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeMovdM32Mm src am).length)) 4)
      (codeRange p (encodeMovdM32Mm src am))
      (Effect.post (movdM32MmEffect p (encodeMovdM32Mm src am).length src am)) := by
  unfold encodeMovdM32Mm
  rcases encodeMmxMem_spec 0x7E src am with ⟨hbytes, hx, hb⟩ | ⟨hbytes, hrex, hx, hb⟩
  · have hl : (0x0F :: 0x7E :: am.modrm src :: am.tail : List UInt8).length =
        3 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact movd_m32_mm_triple_of_bytes p src am hv hx hb
  · have hl : (am.rexByte false 0 :: 0x0F :: 0x7E :: am.modrm src :: am.tail).length =
        4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact movd_m32_mm_rex_triple_of_bytes p _ hrex src am hv hx hb

theorem movd_m32_mm_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 3) (am : AddrMode) (hv : am.Valid) :
    Triple
      (fun s => MmxStorePre p (r.prefixByte :: encodeMovdM32Mm src am).length
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeMovdM32Mm src am).length)) 4 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: encodeMovdM32Mm src am))
      (Effect.post (movdM32MmSegEffect p (r.prefixByte :: encodeMovdM32Mm src am).length base src am)) := by
  unfold encodeMovdM32Mm
  rcases encodeMmxMem_spec 0x7E src am with ⟨hbytes, hx, hb⟩ | ⟨hbytes, hrex, hx, hb⟩
  · have hl : (r.prefixByte :: 0x0F :: 0x7E :: am.modrm src :: am.tail :
        List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact movd_m32_mm_seg_triple_of_bytes p r base src am hv hx hb
  · have hl : (r.prefixByte :: am.rexByte false 0 :: 0x0F :: 0x7E :: am.modrm src ::
        am.tail).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact movd_m32_mm_rex_seg_triple_of_bytes p r base _ hrex src am hv
      hx hb

theorem movd_m32_mm_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 3) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (MmxStorePre p (0x67 :: encodeMovdM32Mm src am).length
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeMovdM32Mm src am).length)) 4)
      (codeRange p (0x67 :: encodeMovdM32Mm src am))
      (Effect.post (movdM32MmA32Effect p (0x67 :: encodeMovdM32Mm src am).length src am)) := by
  unfold encodeMovdM32Mm
  rcases encodeMmxMem_spec 0x7E src am with ⟨hbytes, hx, hb⟩ | ⟨hbytes, hrex, hx, hb⟩
  · have hl : (0x67 :: 0x0F :: 0x7E :: am.modrm src :: am.tail : List UInt8).length =
        4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact movd_m32_mm_a32_triple_of_bytes p src am hv hx hb
  · have hl : (0x67 :: am.rexByte false 0 :: 0x0F :: 0x7E :: am.modrm src ::
        am.tail).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact movd_m32_mm_rex_a32_triple_of_bytes p _ hrex src am hv hx hb

attribute [x86_compose] movdM32MmEffect movdM32MmSegEffect movdM32MmA32Effect

@[x86_local] theorem movdM32MmEffect_local {p : BitVec 64} {len : Nat} {src : BitVec 3}
    {am : AddrMode} :
    Effect.Local (movdM32MmEffect p len src am) := by
  effect_local [movdM32MmEffect, storeEffect, Effect.withMmx]

@[x86_local] theorem movdM32MmSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 3} {am : AddrMode} :
    Effect.Local (movdM32MmSegEffect p len base src am) := by
  effect_local [movdM32MmSegEffect, storeEffect, Effect.withMmx]

@[x86_local] theorem movdM32MmA32Effect_local {p : BitVec 64} {len : Nat} {src : BitVec 3}
    {am : AddrMode} :
    Effect.Local (movdM32MmA32Effect p len src am) := by
  effect_local [movdM32MmA32Effect, storeEffect, Effect.withMmx]

end X86Proofs
