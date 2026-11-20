import X86Proofs.Instructions.Minps.Generated.XM.Step
import X86Proofs.Instructions.Minps.Generated.XM.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def minpsXmmM128Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 128).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), minpSpec 32 s.MXCSR a b⟩,
      ⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (minpFlags 32 s.MXCSR a b)⟩] }

def minpsXmmM128Ok (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Prop :=
  minpOk 32 s.MXCSR ((Operand.xmm dst : Operand 128).read s)
    ((Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 128).read s)

@[simp] theorem minpsXmmM128Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (minpsXmmM128Effect p len dst am s).components = [.xmm dst, .mxcsr, .rip] := rfl

def minpsXmmM128SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 128).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), minpSpec 32 s.MXCSR a b⟩,
      ⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (minpFlags 32 s.MXCSR a b)⟩] }

def minpsXmmM128SegOk (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Prop :=
  minpOk 32 s.MXCSR ((Operand.xmm dst : Operand 128).read s)
    ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 128).read s)

@[simp] theorem minpsXmmM128SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (minpsXmmM128SegEffect p len base dst am s).components = [.xmm dst, .mxcsr, .rip] := rfl

def minpsXmmM128A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 128).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), minpSpec 32 s.MXCSR a b⟩,
      ⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (minpFlags 32 s.MXCSR a b)⟩] }

def minpsXmmM128A32Ok (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Prop :=
  minpOk 32 s.MXCSR ((Operand.xmm dst : Operand 128).read s)
    ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 128).read s)

@[simp] theorem minpsXmmM128A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (minpsXmmM128A32Effect p len dst am s).components = [.xmm dst, .mxcsr, .rip] := rfl

theorem minps_xmm_m128_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (FpPre (SseAlignedLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))))
        (minpsXmmM128Ok p (3 + am.tail.length) (gprNumber 0 0 reg) am))
      (codeRange p (0x0F :: 0x5D :: am.modrm reg :: am.tail))
      (minpsXmmM128Effect p (3 + am.tail.length)
        (gprNumber 0 0 reg) am) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := minps_xmm_m128_step s h hpre.sse hpre.sse.feature []
    (by simp) (by simp)
    rfl rfl rfl
    rfl rfl rfl
    rfl
    reg am hv (AddrContext.legacy _ am hx hb).toSeg
    hcode.bytesAt hlow hpre.aligned hpre.read hm hok
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_xmm_mxcsr h _ _ _ _ _,
    ⟨afterStep_load_xmm_mxcsr_rip h _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_load_xmm_mxcsr s _ _ _ _ _⟩⟩
  refine ⟨?_, ?_⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_xmm_mxcsr]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    rfl
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_mxcsr]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    rfl

theorem minps_xmm_m128_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (FpPre (SseAlignedLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))))
        (minpsXmmM128Ok p (3 + am.tail.length) (gprNumber 0 0 reg) am))
      (codeRange p (0x0F :: 0x5D :: am.modrm reg :: am.tail))
      (Effect.post (minpsXmmM128Effect p (3 + am.tail.length)
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [minpsXmmM128Effect_components]; simp [Component.Covers]) _)
    (minps_xmm_m128_effect_step p reg am hv hx hb)

theorem minps_xmm_m128_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (FpPre (SseAlignedLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))))
        (minpsXmmM128Ok p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (rex :: 0x0F :: 0x5D :: am.modrm reg :: am.tail))
      (minpsXmmM128Effect p (4 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := minps_xmm_m128_step s h hpre.sse hpre.sse.feature [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl)
    reg am hv (by rw [hc]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [hc]; exact hpre.aligned) (by rw [hc]; exact hpre.read) hm
    (by rw [hc]; exact hok)
  simp only [hc] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_xmm_mxcsr h _ _ _ _ _,
    ⟨afterStep_load_xmm_mxcsr_rip h _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_load_xmm_mxcsr s _ _ _ _ _⟩⟩
  refine ⟨?_, ?_⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_xmm_mxcsr]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    rfl
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_mxcsr]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    rfl

theorem minps_xmm_m128_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (FpPre (SseAlignedLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))))
        (minpsXmmM128Ok p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (rex :: 0x0F :: 0x5D :: am.modrm reg :: am.tail))
      (Effect.post (minpsXmmM128Effect p (4 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [minpsXmmM128Effect_components]; simp [Component.Covers]) _)
    (minps_xmm_m128_rex_effect_step p rex hr reg am hv hx hb)

theorem minps_xmm_m128_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (FpPre (fun s => SseAlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) s ∧ r.Ready base s)
        (minpsXmmM128SegOk p (4 + am.tail.length) base (gprNumber 0 0 reg) am))
      (codeRange p (r.prefixByte :: 0x0F :: 0x5D :: am.modrm reg :: am.tail))
      (minpsXmmM128SegEffect p (4 + am.tail.length) base
        (gprNumber 0 0 reg) am) := by
  intro s h hcode ⟨⟨hpre, hseg, hbase⟩, hm, hok⟩
  have hp := hpre.rip
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
  have hstep := minps_xmm_m128_step s h hpre.sse hpre.sse.feature [r.prefixByte]
    (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.aligned) (by rw [hsc, segAddr_withSeg]; exact hpre.read) hm
    (by rw [hsc, segAddr_withSeg]; exact hok)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_xmm_mxcsr h _ _ _ _ _,
    ⟨afterStep_load_xmm_mxcsr_rip h _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_load_xmm_mxcsr s _ _ _ _ _⟩⟩
  refine ⟨?_, ?_⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_xmm_mxcsr]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    rfl
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_mxcsr]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    rfl

theorem minps_xmm_m128_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (FpPre (fun s => SseAlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) s ∧ r.Ready base s)
        (minpsXmmM128SegOk p (4 + am.tail.length) base (gprNumber 0 0 reg) am))
      (codeRange p (r.prefixByte :: 0x0F :: 0x5D :: am.modrm reg :: am.tail))
      (Effect.post (minpsXmmM128SegEffect p (4 + am.tail.length) base
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [minpsXmmM128SegEffect_components]; simp [Component.Covers]) _)
    (minps_xmm_m128_seg_effect_step p r base reg am hv hx hb)

theorem minps_xmm_m128_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (FpPre (fun s => SseAlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) s ∧ r.Ready base s)
        (minpsXmmM128SegOk p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x5D :: am.modrm reg :: am.tail))
      (minpsXmmM128SegEffect p (5 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode ⟨⟨hpre, hseg, hbase⟩, hm, hok⟩
  have hp := hpre.rip
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
  have hstep := minps_xmm_m128_step s h hpre.sse hpre.sse.feature [r.prefixByte, rex]
    (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.aligned) (by rw [hsc, segAddr_withSeg]; exact hpre.read) hm
    (by rw [hsc, segAddr_withSeg]; exact hok)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_xmm_mxcsr h _ _ _ _ _,
    ⟨afterStep_load_xmm_mxcsr_rip h _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_load_xmm_mxcsr s _ _ _ _ _⟩⟩
  refine ⟨?_, ?_⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_xmm_mxcsr]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    rfl
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_mxcsr]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    rfl

theorem minps_xmm_m128_rex_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (FpPre (fun s => SseAlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) s ∧ r.Ready base s)
        (minpsXmmM128SegOk p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x5D :: am.modrm reg :: am.tail))
      (Effect.post (minpsXmmM128SegEffect p (5 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [minpsXmmM128SegEffect_components]; simp [Component.Covers]) _)
    (minps_xmm_m128_rex_seg_effect_step p r base rex hr reg am hv hx hb)

theorem minps_xmm_m128_a32_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (FpPre (SseAlignedLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))))
        (minpsXmmM128A32Ok p (4 + am.tail.length) (gprNumber 0 0 reg) am))
      (codeRange p (0x67 :: 0x0F :: 0x5D :: am.modrm reg :: am.tail))
      (minpsXmmM128A32Effect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := minps_xmm_m128_a32_step s h hpre.sse hpre.sse.feature [0x67]
    (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.aligned) (by rw [hsc]; exact hpre.read) hm
    (by rw [hsc]; exact hok)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_xmm_mxcsr h _ _ _ _ _,
    ⟨afterStep_load_xmm_mxcsr_rip h _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_load_xmm_mxcsr s _ _ _ _ _⟩⟩
  refine ⟨?_, ?_⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_xmm_mxcsr]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    rfl
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_mxcsr]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    rfl

theorem minps_xmm_m128_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (FpPre (SseAlignedLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))))
        (minpsXmmM128A32Ok p (4 + am.tail.length) (gprNumber 0 0 reg) am))
      (codeRange p (0x67 :: 0x0F :: 0x5D :: am.modrm reg :: am.tail))
      (Effect.post (minpsXmmM128A32Effect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [minpsXmmM128A32Effect_components]; simp [Component.Covers]) _)
    (minps_xmm_m128_a32_effect_step p reg am hv hx hb)

theorem minps_xmm_m128_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (FpPre (SseAlignedLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))))
        (minpsXmmM128A32Ok p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (0x67 :: rex :: 0x0F :: 0x5D :: am.modrm reg :: am.tail))
      (minpsXmmM128A32Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex s.DS (PrefixSegments.ofState s) hr]
  have hstep := minps_xmm_m128_a32_step s h hpre.sse hpre.sse.feature [0x67, rex]
    (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.aligned) (by rw [hsc]; exact hpre.read) hm
    (by rw [hsc]; exact hok)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (rexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (rexContext s.DS rex.toBitVec)).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_xmm_mxcsr h _ _ _ _ _,
    ⟨afterStep_load_xmm_mxcsr_rip h _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_load_xmm_mxcsr s _ _ _ _ _⟩⟩
  refine ⟨?_, ?_⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_xmm_mxcsr]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    rfl
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_mxcsr]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    rfl

theorem minps_xmm_m128_rex_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (FpPre (SseAlignedLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))))
        (minpsXmmM128A32Ok p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (0x67 :: rex :: 0x0F :: 0x5D :: am.modrm reg :: am.tail))
      (Effect.post (minpsXmmM128A32Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [minpsXmmM128A32Effect_components]; simp [Component.Covers]) _)
    (minps_xmm_m128_rex_a32_effect_step p rex hr reg am hv hx hb)

theorem minps_xmm_m128_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (FpPre (SseAlignedLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeMinpsXmmM128 dst am).length)))
        (minpsXmmM128Ok p (encodeMinpsXmmM128 dst am).length (dst.setWidth 5) am))
      (codeRange p (encodeMinpsXmmM128 dst am))
      (Effect.post (minpsXmmM128Effect p (encodeMinpsXmmM128 dst am).length
        (dst.setWidth 5) am)) := by
  unfold encodeMinpsXmmM128
  rcases encodeSseMem_spec 0x5D dst am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (0x0F :: 0x5D :: am.modrm (regLow dst) :: am.tail :
        List UInt8).length = 3 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact minps_xmm_m128_triple_of_bytes p (regLow dst) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := minps_xmm_m128_rex_triple_of_bytes p _ hrex.rexPrefix (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (am.rexByte false dst :: 0x0F :: 0x5D :: am.modrm (regLow dst) ::
        am.tail).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact this

theorem minps_xmm_m128_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple
      (FpPre (fun s => SseAlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeMinpsXmmM128 dst am).length)) s ∧ r.Ready base s)
        (minpsXmmM128SegOk p (r.prefixByte :: encodeMinpsXmmM128 dst am).length base (dst.setWidth 5) am))
      (codeRange p (r.prefixByte :: encodeMinpsXmmM128 dst am))
      (Effect.post (minpsXmmM128SegEffect p (r.prefixByte :: encodeMinpsXmmM128 dst am).length base
        (dst.setWidth 5) am)) := by
  unfold encodeMinpsXmmM128
  rcases encodeSseMem_spec 0x5D dst am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (r.prefixByte :: 0x0F :: 0x5D :: am.modrm (regLow dst) ::
        am.tail : List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact minps_xmm_m128_seg_triple_of_bytes p r base (regLow dst) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := minps_xmm_m128_rex_seg_triple_of_bytes p r base _
      hrex.rexPrefix (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (r.prefixByte :: am.rexByte false dst :: 0x0F :: 0x5D ::
        am.modrm (regLow dst) :: am.tail).length = 5 + am.tail.length := by
      simp; omega
    rw [hbytes, hl]
    exact this

theorem minps_xmm_m128_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (FpPre (SseAlignedLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeMinpsXmmM128 dst am).length)))
        (minpsXmmM128A32Ok p (0x67 :: encodeMinpsXmmM128 dst am).length (dst.setWidth 5) am))
      (codeRange p (0x67 :: encodeMinpsXmmM128 dst am))
      (Effect.post (minpsXmmM128A32Effect p (0x67 :: encodeMinpsXmmM128 dst am).length
        (dst.setWidth 5) am)) := by
  unfold encodeMinpsXmmM128
  rcases encodeSseMem_spec 0x5D dst am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (0x67 :: 0x0F :: 0x5D :: am.modrm (regLow dst) ::
        am.tail : List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact minps_xmm_m128_a32_triple_of_bytes p (regLow dst) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := minps_xmm_m128_rex_a32_triple_of_bytes p _
      hrex.rexPrefix (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (0x67 :: am.rexByte false dst :: 0x0F :: 0x5D ::
        am.modrm (regLow dst) :: am.tail).length = 5 + am.tail.length := by
      simp; omega
    rw [hbytes, hl]
    exact this

attribute [x86_compose] minpsXmmM128Effect

@[x86_local] theorem minpsXmmM128Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (minpsXmmM128Effect p len dst am) := by
  effect_local [minpsXmmM128Effect]

attribute [x86_compose] minpsXmmM128SegEffect

@[x86_local] theorem minpsXmmM128SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (minpsXmmM128SegEffect p len base dst am) := by
  effect_local [minpsXmmM128SegEffect]

attribute [x86_compose] minpsXmmM128A32Effect

@[x86_local] theorem minpsXmmM128A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (minpsXmmM128A32Effect p len dst am) := by
  effect_local [minpsXmmM128A32Effect]

end X86Proofs
