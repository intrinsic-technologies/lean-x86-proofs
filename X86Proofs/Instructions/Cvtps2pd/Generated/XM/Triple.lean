import X86Proofs.Instructions.Cvtps2pd.Generated.XM.Step
import X86Proofs.Instructions.Cvtps2pd.Generated.XM.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cvtps2pdXmmM64Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), cvtps2pdSpec s.MXCSR a b⟩,
      ⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (cvtps2pdFlags s.MXCSR a b)⟩] }

def cvtps2pdXmmM64Ok (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Prop :=
  cvtps2pdOk s.MXCSR ((Operand.xmm dst : Operand 128).read s)
    ((Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s)

@[simp] theorem cvtps2pdXmmM64Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (cvtps2pdXmmM64Effect p len dst am s).components = [.xmm dst, .mxcsr, .rip] := rfl

def cvtps2pdXmmM64SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), cvtps2pdSpec s.MXCSR a b⟩,
      ⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (cvtps2pdFlags s.MXCSR a b)⟩] }

def cvtps2pdXmmM64SegOk (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Prop :=
  cvtps2pdOk s.MXCSR ((Operand.xmm dst : Operand 128).read s)
    ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s)

@[simp] theorem cvtps2pdXmmM64SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (cvtps2pdXmmM64SegEffect p len base dst am s).components = [.xmm dst, .mxcsr, .rip] := rfl

def cvtps2pdXmmM64A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), cvtps2pdSpec s.MXCSR a b⟩,
      ⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (cvtps2pdFlags s.MXCSR a b)⟩] }

def cvtps2pdXmmM64A32Ok (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Prop :=
  cvtps2pdOk s.MXCSR ((Operand.xmm dst : Operand 128).read s)
    ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 64).read s)

@[simp] theorem cvtps2pdXmmM64A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (cvtps2pdXmmM64A32Effect p len dst am s).components = [.xmm dst, .mxcsr, .rip] := rfl

theorem cvtps2pd_xmm_m64_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 8)
        (cvtps2pdXmmM64Ok p (3 + am.tail.length) (gprNumber 0 0 reg) am))
      (codeRange p (0x0F :: 0x5A :: am.modrm reg :: am.tail))
      (cvtps2pdXmmM64Effect p (3 + am.tail.length)
        (gprNumber 0 0 reg) am) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cvtps2pd_xmm_m64_step s h hpre.sse hpre.sse2 []
    (by simp) (by simp)
    rfl rfl rfl
    rfl rfl rfl
    rfl
    reg am hv (AddrContext.legacy _ am hx hb).toSeg
    hcode.bytesAt hlow hpre.read hm hok
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

theorem cvtps2pd_xmm_m64_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 8)
        (cvtps2pdXmmM64Ok p (3 + am.tail.length) (gprNumber 0 0 reg) am))
      (codeRange p (0x0F :: 0x5A :: am.modrm reg :: am.tail))
      (Effect.post (cvtps2pdXmmM64Effect p (3 + am.tail.length)
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvtps2pdXmmM64Effect_components]; simp [Component.Covers]) _)
    (cvtps2pd_xmm_m64_effect_step p reg am hv hx hb)

theorem cvtps2pd_xmm_m64_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
        (cvtps2pdXmmM64Ok p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (rex :: 0x0F :: 0x5A :: am.modrm reg :: am.tail))
      (cvtps2pdXmmM64Effect p (4 + am.tail.length)
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
  have hstep := cvtps2pd_xmm_m64_step s h hpre.sse hpre.sse2 [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl)
    reg am hv (by rw [hc]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [hc]; exact hpre.read) hm
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

theorem cvtps2pd_xmm_m64_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
        (cvtps2pdXmmM64Ok p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (rex :: 0x0F :: 0x5A :: am.modrm reg :: am.tail))
      (Effect.post (cvtps2pdXmmM64Effect p (4 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvtps2pdXmmM64Effect_components]; simp [Component.Covers]) _)
    (cvtps2pd_xmm_m64_rex_effect_step p rex hr reg am hv hx hb)

theorem cvtps2pd_xmm_m64_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (FpPre (fun s => Sse2LoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧ r.Ready base s)
        (cvtps2pdXmmM64SegOk p (4 + am.tail.length) base (gprNumber 0 0 reg) am))
      (codeRange p (r.prefixByte :: 0x0F :: 0x5A :: am.modrm reg :: am.tail))
      (cvtps2pdXmmM64SegEffect p (4 + am.tail.length) base
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
  have hstep := cvtps2pd_xmm_m64_step s h hpre.sse hpre.sse2 [r.prefixByte]
    (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.read) hm
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

theorem cvtps2pd_xmm_m64_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (FpPre (fun s => Sse2LoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧ r.Ready base s)
        (cvtps2pdXmmM64SegOk p (4 + am.tail.length) base (gprNumber 0 0 reg) am))
      (codeRange p (r.prefixByte :: 0x0F :: 0x5A :: am.modrm reg :: am.tail))
      (Effect.post (cvtps2pdXmmM64SegEffect p (4 + am.tail.length) base
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvtps2pdXmmM64SegEffect_components]; simp [Component.Covers]) _)
    (cvtps2pd_xmm_m64_seg_effect_step p r base reg am hv hx hb)

theorem cvtps2pd_xmm_m64_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (FpPre (fun s => Sse2LoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 8 s ∧ r.Ready base s)
        (cvtps2pdXmmM64SegOk p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x5A :: am.modrm reg :: am.tail))
      (cvtps2pdXmmM64SegEffect p (5 + am.tail.length) base
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
  have hstep := cvtps2pd_xmm_m64_step s h hpre.sse hpre.sse2 [r.prefixByte, rex]
    (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.read) hm
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

theorem cvtps2pd_xmm_m64_rex_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (FpPre (fun s => Sse2LoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 8 s ∧ r.Ready base s)
        (cvtps2pdXmmM64SegOk p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x5A :: am.modrm reg :: am.tail))
      (Effect.post (cvtps2pdXmmM64SegEffect p (5 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvtps2pdXmmM64SegEffect_components]; simp [Component.Covers]) _)
    (cvtps2pd_xmm_m64_rex_seg_effect_step p r base rex hr reg am hv hx hb)

theorem cvtps2pd_xmm_m64_a32_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
        (cvtps2pdXmmM64A32Ok p (4 + am.tail.length) (gprNumber 0 0 reg) am))
      (codeRange p (0x67 :: 0x0F :: 0x5A :: am.modrm reg :: am.tail))
      (cvtps2pdXmmM64A32Effect p (4 + am.tail.length)
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
  have hstep := cvtps2pd_xmm_m64_a32_step s h hpre.sse hpre.sse2 [0x67]
    (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.read) hm
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

theorem cvtps2pd_xmm_m64_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
        (cvtps2pdXmmM64A32Ok p (4 + am.tail.length) (gprNumber 0 0 reg) am))
      (codeRange p (0x67 :: 0x0F :: 0x5A :: am.modrm reg :: am.tail))
      (Effect.post (cvtps2pdXmmM64A32Effect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvtps2pdXmmM64A32Effect_components]; simp [Component.Covers]) _)
    (cvtps2pd_xmm_m64_a32_effect_step p reg am hv hx hb)

theorem cvtps2pd_xmm_m64_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
        (cvtps2pdXmmM64A32Ok p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (0x67 :: rex :: 0x0F :: 0x5A :: am.modrm reg :: am.tail))
      (cvtps2pdXmmM64A32Effect p (5 + am.tail.length)
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
  have hstep := cvtps2pd_xmm_m64_a32_step s h hpre.sse hpre.sse2 [0x67, rex]
    (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.read) hm
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

theorem cvtps2pd_xmm_m64_rex_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
        (cvtps2pdXmmM64A32Ok p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (0x67 :: rex :: 0x0F :: 0x5A :: am.modrm reg :: am.tail))
      (Effect.post (cvtps2pdXmmM64A32Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvtps2pdXmmM64A32Effect_components]; simp [Component.Covers]) _)
    (cvtps2pd_xmm_m64_rex_a32_effect_step p rex hr reg am hv hx hb)

theorem cvtps2pd_xmm_m64_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeCvtps2pdXmmM64 dst am).length)) 8)
        (cvtps2pdXmmM64Ok p (encodeCvtps2pdXmmM64 dst am).length (dst.setWidth 5) am))
      (codeRange p (encodeCvtps2pdXmmM64 dst am))
      (Effect.post (cvtps2pdXmmM64Effect p (encodeCvtps2pdXmmM64 dst am).length
        (dst.setWidth 5) am)) := by
  unfold encodeCvtps2pdXmmM64
  rcases encodeSseMem_spec 0x5A dst am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (0x0F :: 0x5A :: am.modrm (regLow dst) :: am.tail :
        List UInt8).length = 3 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact cvtps2pd_xmm_m64_triple_of_bytes p (regLow dst) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := cvtps2pd_xmm_m64_rex_triple_of_bytes p _ hrex.rexPrefix (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (am.rexByte false dst :: 0x0F :: 0x5A :: am.modrm (regLow dst) ::
        am.tail).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact this

theorem cvtps2pd_xmm_m64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple
      (FpPre (fun s => Sse2LoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeCvtps2pdXmmM64 dst am).length)) 8 s ∧ r.Ready base s)
        (cvtps2pdXmmM64SegOk p (r.prefixByte :: encodeCvtps2pdXmmM64 dst am).length base (dst.setWidth 5) am))
      (codeRange p (r.prefixByte :: encodeCvtps2pdXmmM64 dst am))
      (Effect.post (cvtps2pdXmmM64SegEffect p (r.prefixByte :: encodeCvtps2pdXmmM64 dst am).length base
        (dst.setWidth 5) am)) := by
  unfold encodeCvtps2pdXmmM64
  rcases encodeSseMem_spec 0x5A dst am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (r.prefixByte :: 0x0F :: 0x5A :: am.modrm (regLow dst) ::
        am.tail : List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact cvtps2pd_xmm_m64_seg_triple_of_bytes p r base (regLow dst) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := cvtps2pd_xmm_m64_rex_seg_triple_of_bytes p r base _
      hrex.rexPrefix (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (r.prefixByte :: am.rexByte false dst :: 0x0F :: 0x5A ::
        am.modrm (regLow dst) :: am.tail).length = 5 + am.tail.length := by
      simp; omega
    rw [hbytes, hl]
    exact this

theorem cvtps2pd_xmm_m64_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeCvtps2pdXmmM64 dst am).length)) 8)
        (cvtps2pdXmmM64A32Ok p (0x67 :: encodeCvtps2pdXmmM64 dst am).length (dst.setWidth 5) am))
      (codeRange p (0x67 :: encodeCvtps2pdXmmM64 dst am))
      (Effect.post (cvtps2pdXmmM64A32Effect p (0x67 :: encodeCvtps2pdXmmM64 dst am).length
        (dst.setWidth 5) am)) := by
  unfold encodeCvtps2pdXmmM64
  rcases encodeSseMem_spec 0x5A dst am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (0x67 :: 0x0F :: 0x5A :: am.modrm (regLow dst) ::
        am.tail : List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact cvtps2pd_xmm_m64_a32_triple_of_bytes p (regLow dst) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := cvtps2pd_xmm_m64_rex_a32_triple_of_bytes p _
      hrex.rexPrefix (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (0x67 :: am.rexByte false dst :: 0x0F :: 0x5A ::
        am.modrm (regLow dst) :: am.tail).length = 5 + am.tail.length := by
      simp; omega
    rw [hbytes, hl]
    exact this

attribute [x86_compose] cvtps2pdXmmM64Effect

@[x86_local] theorem cvtps2pdXmmM64Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (cvtps2pdXmmM64Effect p len dst am) := by
  effect_local [cvtps2pdXmmM64Effect]

attribute [x86_compose] cvtps2pdXmmM64SegEffect

@[x86_local] theorem cvtps2pdXmmM64SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (cvtps2pdXmmM64SegEffect p len base dst am) := by
  effect_local [cvtps2pdXmmM64SegEffect]

attribute [x86_compose] cvtps2pdXmmM64A32Effect

@[x86_local] theorem cvtps2pdXmmM64A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (cvtps2pdXmmM64A32Effect p len dst am) := by
  effect_local [cvtps2pdXmmM64A32Effect]

end X86Proofs
