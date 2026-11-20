import X86Proofs.Instructions.Comisd.Generated.XM.Step
import X86Proofs.Instructions.Comisd.Generated.XM.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def comisdXmmM64Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (comisExc 64 s.MXCSR a b)⟩]
    flags := some (.ofStatusFlags (comisFlags 64 s.MXCSR a b)) }

def comisdXmmM64Ok (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Prop :=
  comisOk 64 s.MXCSR ((Operand.xmm dst : Operand 128).read s)
    ((Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s)

@[simp] theorem comisdXmmM64Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (comisdXmmM64Effect p len dst am s).components = [.mxcsr, .flags, .rip] := rfl

def comisdXmmM64SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (comisExc 64 s.MXCSR a b)⟩]
    flags := some (.ofStatusFlags (comisFlags 64 s.MXCSR a b)) }

def comisdXmmM64SegOk (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Prop :=
  comisOk 64 s.MXCSR ((Operand.xmm dst : Operand 128).read s)
    ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s)

@[simp] theorem comisdXmmM64SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (comisdXmmM64SegEffect p len base dst am s).components = [.mxcsr, .flags, .rip] := rfl

def comisdXmmM64A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (comisExc 64 s.MXCSR a b)⟩]
    flags := some (.ofStatusFlags (comisFlags 64 s.MXCSR a b)) }

def comisdXmmM64A32Ok (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Prop :=
  comisOk 64 s.MXCSR ((Operand.xmm dst : Operand 128).read s)
    ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 64).read s)

@[simp] theorem comisdXmmM64A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (comisdXmmM64A32Effect p len dst am s).components = [.mxcsr, .flags, .rip] := rfl

theorem comisd_xmm_m64_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
        (comisdXmmM64Ok p (4 + am.tail.length) (gprNumber 0 0 reg) am))
      (codeRange p (0x66 :: 0x0F :: 0x2F :: am.modrm reg :: am.tail))
      (comisdXmmM64Effect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := comisd_xmm_m64_step s h hpre.sse hpre.sse2 [0x66]
    (by simpa using scanPrefix_66) (by simp)
    rfl rfl rfl
    rfl rfl rfl
    reg am hv (AddrContext.osz _ am hx hb).toSeg
    hcode.bytesAt hlow hpre.read hm hok
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_writeFpFlags h _ _ _ _,
    ⟨afterStep_load_writeFpFlags_rip h _ _ _ _, ?_, ?_,
      AgreesExcept.afterStep_load_writeFpFlags s _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_writeFpFlags_mxcsr]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    rfl
  · show StatusFlagsOutcome.Allows _ _
    rw [ofRFLAGS_afterStep_load_writeFpFlags]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem comisd_xmm_m64_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
        (comisdXmmM64Ok p (4 + am.tail.length) (gprNumber 0 0 reg) am))
      (codeRange p (0x66 :: 0x0F :: 0x2F :: am.modrm reg :: am.tail))
      (Effect.post (comisdXmmM64Effect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [comisdXmmM64Effect_components]; simp [Component.Covers]) _)
    (comisd_xmm_m64_effect_step p reg am hv hx hb)

theorem comisd_xmm_m64_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
        (comisdXmmM64Ok p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (0x66 :: rex :: 0x0F :: 0x2F :: am.modrm reg :: am.tail))
      (comisdXmmM64Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hc := scanContext_66_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := comisd_xmm_m64_step s h hpre.sse hpre.sse2 [0x66, rex]
    (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    reg am hv (by rw [hc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [hc]; exact hpre.read) hm
    (by rw [hc]; exact hok)
  simp only [hc] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_r4
      (oszRexContext s.DS rex.toBitVec).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_writeFpFlags h _ _ _ _,
    ⟨afterStep_load_writeFpFlags_rip h _ _ _ _, ?_, ?_,
      AgreesExcept.afterStep_load_writeFpFlags s _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_writeFpFlags_mxcsr]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    rfl
  · show StatusFlagsOutcome.Allows _ _
    rw [ofRFLAGS_afterStep_load_writeFpFlags]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem comisd_xmm_m64_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
        (comisdXmmM64Ok p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (0x66 :: rex :: 0x0F :: 0x2F :: am.modrm reg :: am.tail))
      (Effect.post (comisdXmmM64Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [comisdXmmM64Effect_components]; simp [Component.Covers]) _)
    (comisd_xmm_m64_rex_effect_step p rex hr reg am hv hx hb)

theorem comisd_xmm_m64_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (FpPre (fun s => Sse2LoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 8 s ∧ r.Ready base s)
        (comisdXmmM64SegOk p (5 + am.tail.length) base (gprNumber 0 0 reg) am))
      (codeRange p (r.prefixByte :: 0x66 :: 0x0F :: 0x2F :: am.modrm reg :: am.tail))
      (comisdXmmM64SegEffect p (5 + am.tail.length) base
        (gprNumber 0 0 reg) am) := by
  intro s h hcode ⟨⟨hpre, hseg, hbase⟩, hm, hok⟩
  have hp := hpre.rip
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66]
      (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := comisd_xmm_m64_step s h hpre.sse hpre.sse2 [r.prefixByte, 0x66]
    (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.read) hm
    (by rw [hsc, segAddr_withSeg]; exact hok)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s))).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_writeFpFlags h _ _ _ _,
    ⟨afterStep_load_writeFpFlags_rip h _ _ _ _, ?_, ?_,
      AgreesExcept.afterStep_load_writeFpFlags s _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_writeFpFlags_mxcsr]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    rfl
  · show StatusFlagsOutcome.Allows _ _
    rw [ofRFLAGS_afterStep_load_writeFpFlags]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem comisd_xmm_m64_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (FpPre (fun s => Sse2LoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 8 s ∧ r.Ready base s)
        (comisdXmmM64SegOk p (5 + am.tail.length) base (gprNumber 0 0 reg) am))
      (codeRange p (r.prefixByte :: 0x66 :: 0x0F :: 0x2F :: am.modrm reg :: am.tail))
      (Effect.post (comisdXmmM64SegEffect p (5 + am.tail.length) base
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [comisdXmmM64SegEffect_components]; simp [Component.Covers]) _)
    (comisd_xmm_m64_seg_effect_step p r base reg am hv hx hb)

theorem comisd_xmm_m64_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (FpPre (fun s => Sse2LoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (6 + am.tail.length))) 8 s ∧ r.Ready base s)
        (comisdXmmM64SegOk p (6 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: 0x2F :: am.modrm reg :: am.tail))
      (comisdXmmM64SegEffect p (6 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode ⟨⟨hpre, hseg, hbase⟩, hm, hok⟩
  have hp := hpre.rip
  subst hp hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66, rex] =
      withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66, rex]
      (noSegPrefix_cons noSegPrefix_66 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_66_rex s.DS (PrefixSegments.ofState s) hr]
  have hstep := comisd_xmm_m64_step s h hpre.sse hpre.sse2 [r.prefixByte, 0x66, rex]
    (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.read) hm
    (by rw [hsc, segAddr_withSeg]; exact hok)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_writeFpFlags h _ _ _ _,
    ⟨afterStep_load_writeFpFlags_rip h _ _ _ _, ?_, ?_,
      AgreesExcept.afterStep_load_writeFpFlags s _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_writeFpFlags_mxcsr]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    rfl
  · show StatusFlagsOutcome.Allows _ _
    rw [ofRFLAGS_afterStep_load_writeFpFlags]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem comisd_xmm_m64_rex_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (FpPre (fun s => Sse2LoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (6 + am.tail.length))) 8 s ∧ r.Ready base s)
        (comisdXmmM64SegOk p (6 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: 0x2F :: am.modrm reg :: am.tail))
      (Effect.post (comisdXmmM64SegEffect p (6 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [comisdXmmM64SegEffect_components]; simp [Component.Covers]) _)
    (comisd_xmm_m64_rex_seg_effect_step p r base rex hr reg am hv hx hb)

theorem comisd_xmm_m64_a32_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
        (comisdXmmM64A32Ok p (5 + am.tail.length) (gprNumber 0 0 reg) am))
      (codeRange p (0x67 :: 0x66 :: 0x0F :: 0x2F :: am.modrm reg :: am.tail))
      (comisdXmmM64A32Effect p (5 + am.tail.length)
        (gprNumber 0 0 reg) am) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66]) := by
    rw [scanContext_asz_cons]
  have hstep := comisd_xmm_m64_a32_step s h hpre.sse hpre.sse2 [0x67, 0x66]
    (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.read) hm
    (by rw [hsc]; exact hok)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66])).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_writeFpFlags h _ _ _ _,
    ⟨afterStep_load_writeFpFlags_rip h _ _ _ _, ?_, ?_,
      AgreesExcept.afterStep_load_writeFpFlags s _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_writeFpFlags_mxcsr]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    rfl
  · show StatusFlagsOutcome.Allows _ _
    rw [ofRFLAGS_afterStep_load_writeFpFlags]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem comisd_xmm_m64_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
        (comisdXmmM64A32Ok p (5 + am.tail.length) (gprNumber 0 0 reg) am))
      (codeRange p (0x67 :: 0x66 :: 0x0F :: 0x2F :: am.modrm reg :: am.tail))
      (Effect.post (comisdXmmM64A32Effect p (5 + am.tail.length)
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [comisdXmmM64A32Effect_components]; simp [Component.Covers]) _)
    (comisd_xmm_m64_a32_effect_step p reg am hv hx hb)

theorem comisd_xmm_m64_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 8)
        (comisdXmmM64A32Ok p (6 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: 0x2F :: am.modrm reg :: am.tail))
      (comisdXmmM64A32Effect p (6 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, rex] =
      withAsz (oszRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_66_rex s.DS (PrefixSegments.ofState s) hr]
  have hstep := comisd_xmm_m64_a32_step s h hpre.sse hpre.sse2 [0x67, 0x66, rex]
    (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.read) hm
    (by rw [hsc]; exact hok)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (oszRexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (oszRexContext s.DS rex.toBitVec)).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_writeFpFlags h _ _ _ _,
    ⟨afterStep_load_writeFpFlags_rip h _ _ _ _, ?_, ?_,
      AgreesExcept.afterStep_load_writeFpFlags s _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep_load_writeFpFlags_mxcsr]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    rfl
  · show StatusFlagsOutcome.Allows _ _
    rw [ofRFLAGS_afterStep_load_writeFpFlags]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem comisd_xmm_m64_rex_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 8)
        (comisdXmmM64A32Ok p (6 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: 0x2F :: am.modrm reg :: am.tail))
      (Effect.post (comisdXmmM64A32Effect p (6 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [comisdXmmM64A32Effect_components]; simp [Component.Covers]) _)
    (comisd_xmm_m64_rex_a32_effect_step p rex hr reg am hv hx hb)

theorem comisd_xmm_m64_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeComisdXmmM64 dst am).length)) 8)
        (comisdXmmM64Ok p (encodeComisdXmmM64 dst am).length (dst.setWidth 5) am))
      (codeRange p (encodeComisdXmmM64 dst am))
      (Effect.post (comisdXmmM64Effect p (encodeComisdXmmM64 dst am).length
        (dst.setWidth 5) am)) := by
  unfold encodeComisdXmmM64
  rcases encodeSseMem_spec 0x2F dst am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (0x66 :: 0x0F :: 0x2F :: am.modrm (regLow dst) :: am.tail :
        List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact comisd_xmm_m64_triple_of_bytes p (regLow dst) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := comisd_xmm_m64_rex_triple_of_bytes p _ hrex.rexPrefix (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (0x66 :: am.rexByte false dst :: 0x0F :: 0x2F :: am.modrm (regLow dst) ::
        am.tail).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact this

theorem comisd_xmm_m64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple
      (FpPre (fun s => Sse2LoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeComisdXmmM64 dst am).length)) 8 s ∧ r.Ready base s)
        (comisdXmmM64SegOk p (r.prefixByte :: encodeComisdXmmM64 dst am).length base (dst.setWidth 5) am))
      (codeRange p (r.prefixByte :: encodeComisdXmmM64 dst am))
      (Effect.post (comisdXmmM64SegEffect p (r.prefixByte :: encodeComisdXmmM64 dst am).length base
        (dst.setWidth 5) am)) := by
  unfold encodeComisdXmmM64
  rcases encodeSseMem_spec 0x2F dst am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (r.prefixByte :: 0x66 :: 0x0F :: 0x2F :: am.modrm (regLow dst) ::
        am.tail : List UInt8).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact comisd_xmm_m64_seg_triple_of_bytes p r base (regLow dst) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := comisd_xmm_m64_rex_seg_triple_of_bytes p r base _
      hrex.rexPrefix (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (r.prefixByte :: 0x66 :: am.rexByte false dst :: 0x0F :: 0x2F ::
        am.modrm (regLow dst) :: am.tail).length = 6 + am.tail.length := by
      simp; omega
    rw [hbytes, hl]
    exact this

theorem comisd_xmm_m64_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeComisdXmmM64 dst am).length)) 8)
        (comisdXmmM64A32Ok p (0x67 :: encodeComisdXmmM64 dst am).length (dst.setWidth 5) am))
      (codeRange p (0x67 :: encodeComisdXmmM64 dst am))
      (Effect.post (comisdXmmM64A32Effect p (0x67 :: encodeComisdXmmM64 dst am).length
        (dst.setWidth 5) am)) := by
  unfold encodeComisdXmmM64
  rcases encodeSseMem_spec 0x2F dst am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (0x67 :: 0x66 :: 0x0F :: 0x2F :: am.modrm (regLow dst) ::
        am.tail : List UInt8).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact comisd_xmm_m64_a32_triple_of_bytes p (regLow dst) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := comisd_xmm_m64_rex_a32_triple_of_bytes p _
      hrex.rexPrefix (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (0x67 :: 0x66 :: am.rexByte false dst :: 0x0F :: 0x2F ::
        am.modrm (regLow dst) :: am.tail).length = 6 + am.tail.length := by
      simp; omega
    rw [hbytes, hl]
    exact this

attribute [x86_compose] comisdXmmM64Effect

@[x86_local] theorem comisdXmmM64Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (comisdXmmM64Effect p len dst am) := by
  effect_local [comisdXmmM64Effect]

attribute [x86_compose] comisdXmmM64SegEffect

@[x86_local] theorem comisdXmmM64SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (comisdXmmM64SegEffect p len base dst am) := by
  effect_local [comisdXmmM64SegEffect]

attribute [x86_compose] comisdXmmM64A32Effect

@[x86_local] theorem comisdXmmM64A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (comisdXmmM64A32Effect p len dst am) := by
  effect_local [comisdXmmM64A32Effect]

end X86Proofs
