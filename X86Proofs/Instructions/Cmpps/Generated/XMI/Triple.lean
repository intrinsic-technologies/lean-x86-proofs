import X86Proofs.Instructions.Cmpps.Generated.XMI.Step
import X86Proofs.Instructions.Cmpps.Generated.XMI.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cmppsXmmM128Imm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 128).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), cmpfpSpec 32 s.MXCSR a b imm⟩,
      ⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (cmpfpFlags 32 s.MXCSR a b imm)⟩] }

def cmppsXmmM128Imm8Ok (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8)
    (s : RamState) : Prop :=
  cmpfpOk 32 s.MXCSR ((Operand.xmm dst : Operand 128).read s)
    ((Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 128).read s) imm

@[simp] theorem cmppsXmmM128Imm8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    (cmppsXmmM128Imm8Effect p len dst am imm s).components = [.xmm dst, .mxcsr, .rip] := rfl

def cmppsXmmM128Imm8SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 128).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), cmpfpSpec 32 s.MXCSR a b imm⟩,
      ⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (cmpfpFlags 32 s.MXCSR a b imm)⟩] }

def cmppsXmmM128Imm8SegOk (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) : Prop :=
  cmpfpOk 32 s.MXCSR ((Operand.xmm dst : Operand 128).read s)
    ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 128).read s) imm

@[simp] theorem cmppsXmmM128Imm8SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    (cmppsXmmM128Imm8SegEffect p len base dst am imm s).components = [.xmm dst, .mxcsr, .rip] := rfl

def cmppsXmmM128Imm8A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 128).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), cmpfpSpec 32 s.MXCSR a b imm⟩,
      ⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (cmpfpFlags 32 s.MXCSR a b imm)⟩] }

def cmppsXmmM128Imm8A32Ok (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8)
    (s : RamState) : Prop :=
  cmpfpOk 32 s.MXCSR ((Operand.xmm dst : Operand 128).read s)
    ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 128).read s) imm

@[simp] theorem cmppsXmmM128Imm8A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    (cmppsXmmM128Imm8A32Effect p len dst am imm s).components = [.xmm dst, .mxcsr, .rip] := rfl

theorem cmpps_xmm_m128_imm8_effect_step [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) :
    StepEffect
      (FpPre (SseAlignedLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))))
        (cmppsXmmM128Imm8Ok p (4 + am.tail.length) (gprNumber 0 0 reg) am imm))
      (codeRange p (0x0F :: 0xC2 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (cmppsXmmM128Imm8Effect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am imm) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := cmpps_xmm_m128_imm8_step s h hpre.sse hpre.sse.feature []
    (by simp) (by simp)
    rfl rfl rfl
    rfl rfl rfl
    rfl
    reg am hv (AddrContext.legacy _ am hx hb).toSeg imm
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
    simp only [afterFetches_MXCSR, beforeFetch_MXCSR]
    rfl
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_mxcsr]
    simp only [afterFetches_MXCSR, beforeFetch_MXCSR]
    rfl

theorem cmpps_xmm_m128_imm8_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) :
    Triple
      (FpPre (SseAlignedLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))))
        (cmppsXmmM128Imm8Ok p (4 + am.tail.length) (gprNumber 0 0 reg) am imm))
      (codeRange p (0x0F :: 0xC2 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (cmppsXmmM128Imm8Effect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmppsXmmM128Imm8Effect_components]; simp [Component.Covers]) _)
    (cmpps_xmm_m128_imm8_effect_step p reg am hv hx hb imm)

theorem cmpps_xmm_m128_imm8_rex_effect_step [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    StepEffect
      (FpPre (SseAlignedLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))))
        (cmppsXmmM128Imm8Ok p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am imm))
      (codeRange p (rex :: 0x0F :: 0xC2 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (cmppsXmmM128Imm8Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am imm) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := cmpps_xmm_m128_imm8_step s h hpre.sse hpre.sse.feature [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl)
    reg am hv (by rw [hc]; exact (AddrContext.rex _ _ am hx hb).toSeg) imm
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
    simp only [afterFetches_MXCSR, beforeFetch_MXCSR]
    rfl
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_mxcsr]
    simp only [afterFetches_MXCSR, beforeFetch_MXCSR]
    rfl

theorem cmpps_xmm_m128_imm8_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    Triple
      (FpPre (SseAlignedLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))))
        (cmppsXmmM128Imm8Ok p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am imm))
      (codeRange p (rex :: 0x0F :: 0xC2 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (cmppsXmmM128Imm8Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmppsXmmM128Imm8Effect_components]; simp [Component.Covers]) _)
    (cmpps_xmm_m128_imm8_rex_effect_step p rex hr reg am hv hx hb imm)

theorem cmpps_xmm_m128_imm8_seg_effect_step [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) :
    StepEffect
      (FpPre (fun s => SseAlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) s ∧ r.Ready base s)
        (cmppsXmmM128Imm8SegOk p (5 + am.tail.length) base (gprNumber 0 0 reg) am imm))
      (codeRange p (r.prefixByte :: 0x0F :: 0xC2 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (cmppsXmmM128Imm8SegEffect p (5 + am.tail.length) base
        (gprNumber 0 0 reg) am imm) := by
  intro s h hcode ⟨⟨hpre, hseg, hbase⟩, hm, hok⟩
  have hp := hpre.rip
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := cmpps_xmm_m128_imm8_step s h hpre.sse hpre.sse.feature [r.prefixByte]
    (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg) imm
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
    simp only [afterFetches_MXCSR, beforeFetch_MXCSR]
    rfl
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_mxcsr]
    simp only [afterFetches_MXCSR, beforeFetch_MXCSR]
    rfl

theorem cmpps_xmm_m128_imm8_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) :
    Triple
      (FpPre (fun s => SseAlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) s ∧ r.Ready base s)
        (cmppsXmmM128Imm8SegOk p (5 + am.tail.length) base (gprNumber 0 0 reg) am imm))
      (codeRange p (r.prefixByte :: 0x0F :: 0xC2 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (cmppsXmmM128Imm8SegEffect p (5 + am.tail.length) base
        (gprNumber 0 0 reg) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmppsXmmM128Imm8SegEffect_components]; simp [Component.Covers]) _)
    (cmpps_xmm_m128_imm8_seg_effect_step p r base reg am hv hx hb imm)

theorem cmpps_xmm_m128_imm8_rex_seg_effect_step [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    StepEffect
      (FpPre (fun s => SseAlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (6 + am.tail.length))) s ∧ r.Ready base s)
        (cmppsXmmM128Imm8SegOk p (6 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am imm))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xC2 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (cmppsXmmM128Imm8SegEffect p (6 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am imm) := by
  intro s h hcode ⟨⟨hpre, hseg, hbase⟩, hm, hok⟩
  have hp := hpre.rip
  subst hp hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex s.DS (PrefixSegments.ofState s) hr]
  have hstep := cmpps_xmm_m128_imm8_step s h hpre.sse hpre.sse.feature [r.prefixByte, rex]
    (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg) imm
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
    simp only [afterFetches_MXCSR, beforeFetch_MXCSR]
    rfl
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_mxcsr]
    simp only [afterFetches_MXCSR, beforeFetch_MXCSR]
    rfl

theorem cmpps_xmm_m128_imm8_rex_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    Triple
      (FpPre (fun s => SseAlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (6 + am.tail.length))) s ∧ r.Ready base s)
        (cmppsXmmM128Imm8SegOk p (6 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am imm))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xC2 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (cmppsXmmM128Imm8SegEffect p (6 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmppsXmmM128Imm8SegEffect_components]; simp [Component.Covers]) _)
    (cmpps_xmm_m128_imm8_rex_seg_effect_step p r base rex hr reg am hv hx hb imm)

theorem cmpps_xmm_m128_imm8_a32_effect_step [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) :
    StepEffect
      (FpPre (SseAlignedLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))))
        (cmppsXmmM128Imm8A32Ok p (5 + am.tail.length) (gprNumber 0 0 reg) am imm))
      (codeRange p (0x67 :: 0x0F :: 0xC2 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (cmppsXmmM128Imm8A32Effect p (5 + am.tail.length)
        (gprNumber 0 0 reg) am imm) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := cmpps_xmm_m128_imm8_a32_step s h hpre.sse hpre.sse.feature [0x67]
    (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz) imm
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
    simp only [afterFetches_MXCSR, beforeFetch_MXCSR]
    rfl
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_mxcsr]
    simp only [afterFetches_MXCSR, beforeFetch_MXCSR]
    rfl

theorem cmpps_xmm_m128_imm8_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) :
    Triple
      (FpPre (SseAlignedLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))))
        (cmppsXmmM128Imm8A32Ok p (5 + am.tail.length) (gprNumber 0 0 reg) am imm))
      (codeRange p (0x67 :: 0x0F :: 0xC2 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (cmppsXmmM128Imm8A32Effect p (5 + am.tail.length)
        (gprNumber 0 0 reg) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmppsXmmM128Imm8A32Effect_components]; simp [Component.Covers]) _)
    (cmpps_xmm_m128_imm8_a32_effect_step p reg am hv hx hb imm)

theorem cmpps_xmm_m128_imm8_rex_a32_effect_step [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    StepEffect
      (FpPre (SseAlignedLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))))
        (cmppsXmmM128Imm8A32Ok p (6 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am imm))
      (codeRange p (0x67 :: rex :: 0x0F :: 0xC2 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (cmppsXmmM128Imm8A32Effect p (6 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am imm) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex s.DS (PrefixSegments.ofState s) hr]
  have hstep := cmpps_xmm_m128_imm8_a32_step s h hpre.sse hpre.sse.feature [0x67, rex]
    (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz) imm
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
    simp only [afterFetches_MXCSR, beforeFetch_MXCSR]
    rfl
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_mxcsr]
    simp only [afterFetches_MXCSR, beforeFetch_MXCSR]
    rfl

theorem cmpps_xmm_m128_imm8_rex_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    Triple
      (FpPre (SseAlignedLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))))
        (cmppsXmmM128Imm8A32Ok p (6 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am imm))
      (codeRange p (0x67 :: rex :: 0x0F :: 0xC2 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (cmppsXmmM128Imm8A32Effect p (6 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmppsXmmM128Imm8A32Effect_components]; simp [Component.Covers]) _)
    (cmpps_xmm_m128_imm8_rex_a32_effect_step p rex hr reg am hv hx hb imm)

theorem cmpps_xmm_m128_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (imm : BitVec 8) :
    Triple
      (FpPre (SseAlignedLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeCmppsXmmM128Imm8 dst am imm).length)))
        (cmppsXmmM128Imm8Ok p (encodeCmppsXmmM128Imm8 dst am imm).length (dst.setWidth 5) am imm))
      (codeRange p (encodeCmppsXmmM128Imm8 dst am imm))
      (Effect.post (cmppsXmmM128Imm8Effect p (encodeCmppsXmmM128Imm8 dst am imm).length
        (dst.setWidth 5) am imm)) := by
  unfold encodeCmppsXmmM128Imm8
  rcases encodeSseMem_spec 0xC2 dst am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (((0x0F :: 0xC2 :: am.modrm (regLow dst) :: am.tail) ++
        immBytes 8 imm) : List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact cmpps_xmm_m128_imm8_triple_of_bytes p (regLow dst) am hv hx hb imm
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := cmpps_xmm_m128_imm8_rex_triple_of_bytes p _ hrex.rexPrefix (regLow dst) am hv hx hb
      imm
    rw [hr, gprNumber_reg] at this
    have hl : (((am.rexByte false dst :: 0x0F :: 0xC2 ::
        am.modrm (regLow dst) :: am.tail) ++ immBytes 8 imm)).length =
        5 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact this

theorem cmpps_xmm_m128_imm8_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (imm : BitVec 8) :
    Triple
      (FpPre (SseAlignedLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeCmppsXmmM128Imm8 dst am imm).length)))
        (cmppsXmmM128Imm8A32Ok p (0x67 :: encodeCmppsXmmM128Imm8 dst am imm).length (dst.setWidth 5) am imm))
      (codeRange p (0x67 :: encodeCmppsXmmM128Imm8 dst am imm))
      (Effect.post (cmppsXmmM128Imm8A32Effect p (0x67 :: encodeCmppsXmmM128Imm8 dst am imm).length
        (dst.setWidth 5) am imm)) := by
  unfold encodeCmppsXmmM128Imm8
  rcases encodeSseMem_spec 0xC2 dst am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (0x67 :: ((0x0F :: 0xC2 :: am.modrm (regLow dst) :: am.tail) ++
        immBytes 8 imm) : List UInt8).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact cmpps_xmm_m128_imm8_a32_triple_of_bytes p (regLow dst) am hv hx hb imm
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := cmpps_xmm_m128_imm8_rex_a32_triple_of_bytes p _ hrex.rexPrefix (regLow dst) am hv hx hb
      imm
    rw [hr, gprNumber_reg] at this
    have hl : (0x67 :: ((am.rexByte false dst :: 0x0F :: 0xC2 ::
        am.modrm (regLow dst) :: am.tail) ++ immBytes 8 imm)).length =
        6 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact this

theorem cmpps_xmm_m128_imm8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) (imm : BitVec 8) :
    Triple
      (FpPre (fun s => SseAlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeCmppsXmmM128Imm8 dst am imm).length)) s ∧ r.Ready base s)
        (cmppsXmmM128Imm8SegOk p (r.prefixByte :: encodeCmppsXmmM128Imm8 dst am imm).length base (dst.setWidth 5) am imm))
      (codeRange p (r.prefixByte :: encodeCmppsXmmM128Imm8 dst am imm))
      (Effect.post (cmppsXmmM128Imm8SegEffect p (r.prefixByte :: encodeCmppsXmmM128Imm8 dst am imm).length base
        (dst.setWidth 5) am imm)) := by
  unfold encodeCmppsXmmM128Imm8
  rcases encodeSseMem_spec 0xC2 dst am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (r.prefixByte :: ((0x0F :: 0xC2 :: am.modrm (regLow dst) ::
        am.tail) ++ immBytes 8 imm) : List UInt8).length = 5 + am.tail.length := by
      simp; omega
    rw [hbytes, ← hreg, hl]
    exact cmpps_xmm_m128_imm8_seg_triple_of_bytes p r base (regLow dst) am hv hx hb imm
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := cmpps_xmm_m128_imm8_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix (regLow dst) am hv
      hx hb imm
    rw [hr, gprNumber_reg] at this
    have hl : (r.prefixByte :: ((am.rexByte false dst :: 0x0F :: 0xC2 ::
        am.modrm (regLow dst) :: am.tail) ++ immBytes 8 imm)).length =
        6 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact this

attribute [x86_compose] cmppsXmmM128Imm8Effect

@[x86_local] theorem cmppsXmmM128Imm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (cmppsXmmM128Imm8Effect p len dst am imm) := by
  effect_local [cmppsXmmM128Imm8Effect]

attribute [x86_compose] cmppsXmmM128Imm8SegEffect

@[x86_local] theorem cmppsXmmM128Imm8SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (cmppsXmmM128Imm8SegEffect p len base dst am imm) := by
  effect_local [cmppsXmmM128Imm8SegEffect]

attribute [x86_compose] cmppsXmmM128Imm8A32Effect

@[x86_local] theorem cmppsXmmM128Imm8A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (cmppsXmmM128Imm8A32Effect p len dst am imm) := by
  effect_local [cmppsXmmM128Imm8A32Effect]

end X86Proofs
