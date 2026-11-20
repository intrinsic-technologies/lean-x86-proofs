import X86Proofs.Instructions.Movq.Generated.MMem6E.Step
import X86Proofs.Instructions.Movq.Generated.MMem6E.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movqMmM646eEffect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (am : AddrMode) (s : RamState) :
    Effect :=
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  mmxEffect s (p + BitVec.ofNat 64 len) dst (movdSpec 64 64 b)

@[simp] theorem movqMmM646eEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (am : AddrMode) (s : RamState) :
    (movqMmM646eEffect p len dst am s).components = [.fpr dst, .fsw, .ftw, .rip] := rfl

def movqMmM646eSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 3)
    (am : AddrMode) (s : RamState) : Effect :=
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  mmxEffect s (p + BitVec.ofNat 64 len) dst (movdSpec 64 64 b)

@[simp] theorem movqMmM646eSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 3) (am : AddrMode) (s : RamState) :
    (movqMmM646eSegEffect p len base dst am s).components = [.fpr dst, .fsw, .ftw, .rip] := rfl

def movqMmM646eA32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (am : AddrMode) (s : RamState) :
    Effect :=
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  mmxEffect s (p + BitVec.ofNat 64 len) dst (movdSpec 64 64 b)

@[simp] theorem movqMmM646eA32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (am : AddrMode) (s : RamState) :
    (movqMmM646eA32Effect p len dst am s).components = [.fpr dst, .fsw, .ftw, .rip] := rfl

theorem movq_mm_m64_6e_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (MmxLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (rex :: 0x0F :: 0x6E :: am.modrm reg :: am.tail))
      (movqMmM646eEffect p (4 + am.tail.length) reg am) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hmmx⟩, hread⟩
  subst hp
  have hr := hrex.rexPrefix
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := movq_mm_m64_6e_step s h hcr0 hes hmmx [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    reg am hv (by rw [hc]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [hc]; exact hread)
  simp only [hc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds_load h _ _ _ _ rfl

theorem movq_mm_m64_6e_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (MmxLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (rex :: 0x0F :: 0x6E :: am.modrm reg :: am.tail))
      (Effect.post (movqMmM646eEffect p (4 + am.tail.length) reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movqMmM646eEffect_components]; simp [Component.Covers]) _)
    (movq_mm_m64_6e_effect_step p rex hrex reg am hv hx hb)

theorem movq_mm_m64_6e_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => MmxLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x6E :: am.modrm reg :: am.tail))
      (movqMmM646eSegEffect p (5 + am.tail.length) base reg am) := by
  rintro s h hcode ⟨⟨⟨hp, hcr0, hes, hmmx⟩, hread⟩, hseg, hbase⟩
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
  have hstep := movq_mm_m64_6e_step s h hcr0 hes hmmx [r.prefixByte, rex]
    (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; exact hrex.rex_w s.DS)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds_load h _ _ _ _ rfl

theorem movq_mm_m64_6e_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => MmxLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x6E :: am.modrm reg :: am.tail))
      (Effect.post (movqMmM646eSegEffect p (5 + am.tail.length) base reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movqMmM646eSegEffect_components]; simp [Component.Covers]) _)
    (movq_mm_m64_6e_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem movq_mm_m64_6e_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (MmxLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0x0F :: 0x6E :: am.modrm reg :: am.tail))
      (movqMmM646eA32Effect p (5 + am.tail.length) reg am) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hmmx⟩, hread⟩
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
  have hstep := movq_mm_m64_6e_a32_step s h hcr0 hes hmmx [0x67, rex]
    (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; exact hrex.rex_w s.DS)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds_load h _ _ _ _ rfl

theorem movq_mm_m64_6e_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (MmxLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0x0F :: 0x6E :: am.modrm reg :: am.tail))
      (Effect.post (movqMmM646eA32Effect p (5 + am.tail.length) reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movqMmM646eA32Effect_components]; simp [Component.Covers]) _)
    (movq_mm_m64_6e_a32_effect_step p rex hrex reg am hv hx hb)

theorem movq_mm_m64_6e_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (MmxLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeMovqMmM646e dst am).length)) 8)
      (codeRange p (encodeMovqMmM646e dst am))
      (Effect.post (movqMmM646eEffect p (encodeMovqMmM646e dst am).length dst am)) := by
  unfold encodeMovqMmM646e
  obtain ⟨hbytes, hrex, hx, hb⟩ := encodeMmxMemW_spec 0x6E dst am
  have hl : (am.rexByte true 0 :: 0x0F :: 0x6E :: am.modrm dst :: am.tail).length =
      4 + am.tail.length := by simp; omega
  rw [hbytes, hl]
  exact movq_mm_m64_6e_triple_of_bytes p _ hrex dst am hv hx hb

theorem movq_mm_m64_6e_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 3) (am : AddrMode) (hv : am.Valid) :
    Triple
      (fun s => MmxLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeMovqMmM646e dst am).length)) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: encodeMovqMmM646e dst am))
      (Effect.post (movqMmM646eSegEffect p (r.prefixByte :: encodeMovqMmM646e dst am).length base dst am)) := by
  unfold encodeMovqMmM646e
  obtain ⟨hbytes, hrex, hx, hb⟩ := encodeMmxMemW_spec 0x6E dst am
  have hl : (r.prefixByte :: am.rexByte true 0 :: 0x0F :: 0x6E :: am.modrm dst ::
      am.tail).length = 5 + am.tail.length := by simp; omega
  rw [hbytes, hl]
  exact movq_mm_m64_6e_seg_triple_of_bytes p r base _ hrex dst am hv hx hb

theorem movq_mm_m64_6e_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (MmxLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeMovqMmM646e dst am).length)) 8)
      (codeRange p (0x67 :: encodeMovqMmM646e dst am))
      (Effect.post (movqMmM646eA32Effect p (0x67 :: encodeMovqMmM646e dst am).length dst am)) := by
  unfold encodeMovqMmM646e
  obtain ⟨hbytes, hrex, hx, hb⟩ := encodeMmxMemW_spec 0x6E dst am
  have hl : (0x67 :: am.rexByte true 0 :: 0x0F :: 0x6E :: am.modrm dst ::
      am.tail).length = 5 + am.tail.length := by simp; omega
  rw [hbytes, hl]
  exact movq_mm_m64_6e_a32_triple_of_bytes p _ hrex dst am hv hx hb

attribute [x86_compose] movqMmM646eEffect

@[x86_local] theorem movqMmM646eEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {am : AddrMode} :
    Effect.Local (movqMmM646eEffect p len dst am) := by
  effect_local [movqMmM646eEffect, mmxEffect]

attribute [x86_compose] movqMmM646eSegEffect

@[x86_local] theorem movqMmM646eSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 3} {am : AddrMode} :
    Effect.Local (movqMmM646eSegEffect p len base dst am) := by
  effect_local [movqMmM646eSegEffect, mmxEffect]

attribute [x86_compose] movqMmM646eA32Effect

@[x86_local] theorem movqMmM646eA32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {am : AddrMode} :
    Effect.Local (movqMmM646eA32Effect p len dst am) := by
  effect_local [movqMmM646eA32Effect, mmxEffect]

end X86Proofs
