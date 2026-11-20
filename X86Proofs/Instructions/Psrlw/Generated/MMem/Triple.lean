import X86Proofs.Instructions.Psrlw.Generated.MMem.Step
import X86Proofs.Instructions.Psrlw.Generated.MMem.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def psrlwMmM64Effect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (am : AddrMode) (s : RamState) :
    Effect :=
  let a := (Operand.mmx dst : Operand 64).read s
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  mmxEffect s (p + BitVec.ofNat 64 len) dst (psrlMmxSpec 16 a b.toNat)

@[simp] theorem psrlwMmM64Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (am : AddrMode) (s : RamState) :
    (psrlwMmM64Effect p len dst am s).components = [.fpr dst, .fsw, .ftw, .rip] := rfl

def psrlwMmM64SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 3)
    (am : AddrMode) (s : RamState) : Effect :=
  let a := (Operand.mmx dst : Operand 64).read s
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  mmxEffect s (p + BitVec.ofNat 64 len) dst (psrlMmxSpec 16 a b.toNat)

@[simp] theorem psrlwMmM64SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 3) (am : AddrMode) (s : RamState) :
    (psrlwMmM64SegEffect p len base dst am s).components = [.fpr dst, .fsw, .ftw, .rip] := rfl

def psrlwMmM64A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (am : AddrMode) (s : RamState) :
    Effect :=
  let a := (Operand.mmx dst : Operand 64).read s
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  mmxEffect s (p + BitVec.ofNat 64 len) dst (psrlMmxSpec 16 a b.toNat)

@[simp] theorem psrlwMmM64A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (am : AddrMode) (s : RamState) :
    (psrlwMmM64A32Effect p len dst am s).components = [.fpr dst, .fsw, .ftw, .rip] := rfl

theorem psrlw_mm_m64_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (MmxLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 8)
      (codeRange p (0x0F :: 0xD1 :: am.modrm reg :: am.tail))
      (psrlwMmM64Effect p (3 + am.tail.length) reg am) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hmmx⟩, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := psrlw_mm_m64_step s h hcr0 hes hmmx []
    (by simp) (by simp)
    rfl rfl rfl rfl rfl
    reg am hv (AddrContext.legacy _ am hx hb).toSeg
    hcode.bytesAt hlow hread
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds_load h _ _ _ _ rfl

theorem psrlw_mm_m64_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (MmxLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 8)
      (codeRange p (0x0F :: 0xD1 :: am.modrm reg :: am.tail))
      (Effect.post (psrlwMmM64Effect p (3 + am.tail.length) reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [psrlwMmM64Effect_components]; simp [Component.Covers]) _)
    (psrlw_mm_m64_effect_step p reg am hv hx hb)

theorem psrlw_mm_m64_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (MmxLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (rex :: 0x0F :: 0xD1 :: am.modrm reg :: am.tail))
      (psrlwMmM64Effect p (4 + am.tail.length) reg am) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hmmx⟩, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := psrlw_mm_m64_step s h hcr0 hes hmmx [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    reg am hv (by rw [hc]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [hc]; exact hread)
  simp only [hc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds_load h _ _ _ _ rfl

theorem psrlw_mm_m64_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (MmxLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (rex :: 0x0F :: 0xD1 :: am.modrm reg :: am.tail))
      (Effect.post (psrlwMmM64Effect p (4 + am.tail.length) reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [psrlwMmM64Effect_components]; simp [Component.Covers]) _)
    (psrlw_mm_m64_rex_effect_step p rex hr reg am hv hx hb)

theorem psrlw_mm_m64_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => MmxLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x0F :: 0xD1 :: am.modrm reg :: am.tail))
      (psrlwMmM64SegEffect p (4 + am.tail.length) base reg am) := by
  rintro s h hcode ⟨⟨⟨hp, hcr0, hes, hmmx⟩, hread⟩, hseg, hbase⟩
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
  have hstep := psrlw_mm_m64_step s h hcr0 hes hmmx [r.prefixByte]
    (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds_load h _ _ _ _ rfl

theorem psrlw_mm_m64_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => MmxLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x0F :: 0xD1 :: am.modrm reg :: am.tail))
      (Effect.post (psrlwMmM64SegEffect p (4 + am.tail.length) base reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [psrlwMmM64SegEffect_components]; simp [Component.Covers]) _)
    (psrlw_mm_m64_seg_effect_step p r base reg am hv hx hb)

theorem psrlw_mm_m64_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => MmxLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xD1 :: am.modrm reg :: am.tail))
      (psrlwMmM64SegEffect p (5 + am.tail.length) base reg am) := by
  rintro s h hcode ⟨⟨⟨hp, hcr0, hes, hmmx⟩, hread⟩, hseg, hbase⟩
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
  have hstep := psrlw_mm_m64_step s h hcr0 hes hmmx [r.prefixByte, rex]
    (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds_load h _ _ _ _ rfl

theorem psrlw_mm_m64_rex_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => MmxLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xD1 :: am.modrm reg :: am.tail))
      (Effect.post (psrlwMmM64SegEffect p (5 + am.tail.length) base reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [psrlwMmM64SegEffect_components]; simp [Component.Covers]) _)
    (psrlw_mm_m64_rex_seg_effect_step p r base rex hr reg am hv hx hb)

theorem psrlw_mm_m64_a32_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (MmxLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (0x67 :: 0x0F :: 0xD1 :: am.modrm reg :: am.tail))
      (psrlwMmM64A32Effect p (4 + am.tail.length) reg am) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hmmx⟩, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := psrlw_mm_m64_a32_step s h hcr0 hes hmmx [0x67]
    (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds_load h _ _ _ _ rfl

theorem psrlw_mm_m64_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (MmxLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (0x67 :: 0x0F :: 0xD1 :: am.modrm reg :: am.tail))
      (Effect.post (psrlwMmM64A32Effect p (4 + am.tail.length) reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [psrlwMmM64A32Effect_components]; simp [Component.Covers]) _)
    (psrlw_mm_m64_a32_effect_step p reg am hv hx hb)

theorem psrlw_mm_m64_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (MmxLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xD1 :: am.modrm reg :: am.tail))
      (psrlwMmM64A32Effect p (5 + am.tail.length) reg am) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hmmx⟩, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex s.DS (PrefixSegments.ofState s) hr]
  have hstep := psrlw_mm_m64_a32_step s h hcr0 hes hmmx [0x67, rex]
    (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds_load h _ _ _ _ rfl

theorem psrlw_mm_m64_rex_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (MmxLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xD1 :: am.modrm reg :: am.tail))
      (Effect.post (psrlwMmM64A32Effect p (5 + am.tail.length) reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [psrlwMmM64A32Effect_components]; simp [Component.Covers]) _)
    (psrlw_mm_m64_rex_a32_effect_step p rex hr reg am hv hx hb)

theorem psrlw_mm_m64_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (MmxLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodePsrlwMmM64 dst am).length)) 8)
      (codeRange p (encodePsrlwMmM64 dst am))
      (Effect.post (psrlwMmM64Effect p (encodePsrlwMmM64 dst am).length dst am)) := by
  unfold encodePsrlwMmM64
  rcases encodeMmxMem_spec 0xD1 dst am with ⟨hbytes, hx, hb⟩ | ⟨hbytes, hrex, hx, hb⟩
  · have hl : (0x0F :: 0xD1 :: am.modrm dst :: am.tail : List UInt8).length =
        3 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact psrlw_mm_m64_triple_of_bytes p dst am hv hx hb
  · have hl : (am.rexByte false 0 :: 0x0F :: 0xD1 :: am.modrm dst :: am.tail).length =
        4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact psrlw_mm_m64_rex_triple_of_bytes p _ hrex.rexPrefix dst am hv hx hb

theorem psrlw_mm_m64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 3) (am : AddrMode) (hv : am.Valid) :
    Triple
      (fun s => MmxLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodePsrlwMmM64 dst am).length)) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: encodePsrlwMmM64 dst am))
      (Effect.post (psrlwMmM64SegEffect p (r.prefixByte :: encodePsrlwMmM64 dst am).length base dst am)) := by
  unfold encodePsrlwMmM64
  rcases encodeMmxMem_spec 0xD1 dst am with ⟨hbytes, hx, hb⟩ | ⟨hbytes, hrex, hx, hb⟩
  · have hl : (r.prefixByte :: 0x0F :: 0xD1 :: am.modrm dst :: am.tail : List UInt8).length =
        4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact psrlw_mm_m64_seg_triple_of_bytes p r base dst am hv hx hb
  · have hl : (r.prefixByte :: am.rexByte false 0 :: 0x0F :: 0xD1 :: am.modrm dst ::
        am.tail).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact psrlw_mm_m64_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix dst am hv hx
      hb

theorem psrlw_mm_m64_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (MmxLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodePsrlwMmM64 dst am).length)) 8)
      (codeRange p (0x67 :: encodePsrlwMmM64 dst am))
      (Effect.post (psrlwMmM64A32Effect p (0x67 :: encodePsrlwMmM64 dst am).length dst am)) := by
  unfold encodePsrlwMmM64
  rcases encodeMmxMem_spec 0xD1 dst am with ⟨hbytes, hx, hb⟩ | ⟨hbytes, hrex, hx, hb⟩
  · have hl : (0x67 :: 0x0F :: 0xD1 :: am.modrm dst :: am.tail : List UInt8).length =
        4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact psrlw_mm_m64_a32_triple_of_bytes p dst am hv hx hb
  · have hl : (0x67 :: am.rexByte false 0 :: 0x0F :: 0xD1 :: am.modrm dst ::
        am.tail).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact psrlw_mm_m64_rex_a32_triple_of_bytes p _ hrex.rexPrefix dst am hv hx hb

attribute [x86_compose] psrlwMmM64Effect

@[x86_local] theorem psrlwMmM64Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {am : AddrMode} :
    Effect.Local (psrlwMmM64Effect p len dst am) := by
  effect_local [psrlwMmM64Effect, mmxEffect]

attribute [x86_compose] psrlwMmM64SegEffect

@[x86_local] theorem psrlwMmM64SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 3} {am : AddrMode} :
    Effect.Local (psrlwMmM64SegEffect p len base dst am) := by
  effect_local [psrlwMmM64SegEffect, mmxEffect]

attribute [x86_compose] psrlwMmM64A32Effect

@[x86_local] theorem psrlwMmM64A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {am : AddrMode} :
    Effect.Local (psrlwMmM64A32Effect p len dst am) := by
  effect_local [psrlwMmM64A32Effect, mmxEffect]

end X86Proofs
