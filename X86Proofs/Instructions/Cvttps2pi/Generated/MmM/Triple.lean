import X86Proofs.Instructions.Cvttps2pi.Generated.MmM.Step
import X86Proofs.Instructions.Cvttps2pi.Generated.MmM.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cvttps2piMmM64Effect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (am : AddrMode)
    (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  mmxMxcsrEffect s (p + BitVec.ofNat 64 len) dst (cvttps2piSpec s.MXCSR b)
    (mxOr s.MXCSR (cvttps2piFlags s.MXCSR b))

def cvttps2piMmM64Ok (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Prop :=
  cvttps2piOk s.MXCSR
    ((Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s)

@[simp] theorem cvttps2piMmM64Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (am : AddrMode) (s : RamState) :
    (cvttps2piMmM64Effect p len dst am s).components = [.fpr dst, .mxcsr, .fsw, .ftw, .rip] := rfl

def cvttps2piMmM64SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 3)
    (am : AddrMode) (s : RamState) : Effect :=
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  mmxMxcsrEffect s (p + BitVec.ofNat 64 len) dst (cvttps2piSpec s.MXCSR b)
    (mxOr s.MXCSR (cvttps2piFlags s.MXCSR b))

def cvttps2piMmM64SegOk (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode)
    (s : RamState) : Prop :=
  cvttps2piOk s.MXCSR
    ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s)

@[simp] theorem cvttps2piMmM64SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 3) (am : AddrMode) (s : RamState) :
    (cvttps2piMmM64SegEffect p len base dst am s).components =
      [.fpr dst, .mxcsr, .fsw, .ftw, .rip] := rfl

def cvttps2piMmM64A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (am : AddrMode)
    (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  mmxMxcsrEffect s (p + BitVec.ofNat 64 len) dst (cvttps2piSpec s.MXCSR b)
    (mxOr s.MXCSR (cvttps2piFlags s.MXCSR b))

def cvttps2piMmM64A32Ok (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Prop :=
  cvttps2piOk s.MXCSR
    ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 64).read s)

@[simp] theorem cvttps2piMmM64A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (am : AddrMode) (s : RamState) :
    (cvttps2piMmM64A32Effect p len dst am s).components = [.fpr dst, .mxcsr, .fsw, .ftw, .rip] := rfl

theorem cvttps2pi_mm_m64_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (FpPre (MmxEnterPre (SseLoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 8))
        (cvttps2piMmM64Ok p (3 + am.tail.length) am))
      (codeRange p (0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (cvttps2piMmM64Effect p (3 + am.tail.length) reg am) := by
  intro s h hcode ⟨⟨hpre, hes⟩, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cvttps2pi_mm_m64_step s h hpre.sse hes hpre.sse.feature []
    (by simp) (by simp)
    rfl rfl rfl rfl
    rfl
    reg am hv (AddrContext.legacy _ am hx hb).toSeg
    hcode.bytesAt hlow hpre.read hm hok
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx_mxcsr h _ _ _ _ _, ?_⟩
  exact mmxMxcsrEffect_holds_load h _ _ _ _ _ rfl

theorem cvttps2pi_mm_m64_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (FpPre (MmxEnterPre (SseLoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 8))
        (cvttps2piMmM64Ok p (3 + am.tail.length) am))
      (codeRange p (0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (Effect.post (cvttps2piMmM64Effect p (3 + am.tail.length) reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvttps2piMmM64Effect_components]; simp [Component.Covers]) _)
    (cvttps2pi_mm_m64_effect_step p reg am hv hx hb)

theorem cvttps2pi_mm_m64_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (FpPre (MmxEnterPre (SseLoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8))
        (cvttps2piMmM64Ok p (4 + am.tail.length) am))
      (codeRange p (rex :: 0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (cvttps2piMmM64Effect p (4 + am.tail.length) reg am) := by
  intro s h hcode ⟨⟨hpre, hes⟩, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := cvttps2pi_mm_m64_step s h hpre.sse hes hpre.sse.feature [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl)
    reg am hv (by rw [hc]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow
    (by rw [hc]; exact hpre.read) hm
    (by rw [hc]; exact hok)
  simp only [hc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx_mxcsr h _ _ _ _ _, ?_⟩
  exact mmxMxcsrEffect_holds_load h _ _ _ _ _ rfl

theorem cvttps2pi_mm_m64_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (FpPre (MmxEnterPre (SseLoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8))
        (cvttps2piMmM64Ok p (4 + am.tail.length) am))
      (codeRange p (rex :: 0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (Effect.post (cvttps2piMmM64Effect p (4 + am.tail.length) reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvttps2piMmM64Effect_components]; simp [Component.Covers]) _)
    (cvttps2pi_mm_m64_rex_effect_step p rex hr reg am hv hx hb)

theorem cvttps2pi_mm_m64_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (FpPre (fun s => MmxEnterPre (SseLoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 8) s ∧
        r.Ready base s)
        (cvttps2piMmM64SegOk p (4 + am.tail.length) base am))
      (codeRange p (r.prefixByte :: 0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (cvttps2piMmM64SegEffect p (4 + am.tail.length) base reg am) := by
  intro s h hcode ⟨⟨⟨hpre, hes⟩, hseg, hbase⟩, hm, hok⟩
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
  have hstep := cvttps2pi_mm_m64_step s h hpre.sse hes hpre.sse.feature [r.prefixByte]
    (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow
    (by rw [hsc, segAddr_withSeg]; exact hpre.read) hm
    (by rw [hsc, segAddr_withSeg]; exact hok)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx_mxcsr h _ _ _ _ _, ?_⟩
  exact mmxMxcsrEffect_holds_load h _ _ _ _ _ rfl

theorem cvttps2pi_mm_m64_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (FpPre (fun s => MmxEnterPre (SseLoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 8) s ∧
        r.Ready base s)
        (cvttps2piMmM64SegOk p (4 + am.tail.length) base am))
      (codeRange p (r.prefixByte :: 0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (Effect.post (cvttps2piMmM64SegEffect p (4 + am.tail.length) base reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvttps2piMmM64SegEffect_components]; simp [Component.Covers]) _)
    (cvttps2pi_mm_m64_seg_effect_step p r base reg am hv hx hb)

theorem cvttps2pi_mm_m64_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (FpPre (fun s => MmxEnterPre (SseLoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 8) s ∧
        r.Ready base s)
        (cvttps2piMmM64SegOk p (5 + am.tail.length) base am))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (cvttps2piMmM64SegEffect p (5 + am.tail.length) base reg am) := by
  intro s h hcode ⟨⟨⟨hpre, hes⟩, hseg, hbase⟩, hm, hok⟩
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
  have hstep := cvttps2pi_mm_m64_step s h hpre.sse hes hpre.sse.feature [r.prefixByte, rex]
    (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow
    (by rw [hsc, segAddr_withSeg]; exact hpre.read) hm
    (by rw [hsc, segAddr_withSeg]; exact hok)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx_mxcsr h _ _ _ _ _, ?_⟩
  exact mmxMxcsrEffect_holds_load h _ _ _ _ _ rfl

theorem cvttps2pi_mm_m64_rex_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (FpPre (fun s => MmxEnterPre (SseLoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 8) s ∧
        r.Ready base s)
        (cvttps2piMmM64SegOk p (5 + am.tail.length) base am))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (Effect.post (cvttps2piMmM64SegEffect p (5 + am.tail.length) base reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvttps2piMmM64SegEffect_components]; simp [Component.Covers]) _)
    (cvttps2pi_mm_m64_rex_seg_effect_step p r base rex hr reg am hv hx hb)

theorem cvttps2pi_mm_m64_a32_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (FpPre (MmxEnterPre (SseLoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8))
        (cvttps2piMmM64A32Ok p (4 + am.tail.length) am))
      (codeRange p (0x67 :: 0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (cvttps2piMmM64A32Effect p (4 + am.tail.length) reg am) := by
  intro s h hcode ⟨⟨hpre, hes⟩, hm, hok⟩
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
  have hstep := cvttps2pi_mm_m64_a32_step s h hpre.sse hes hpre.sse.feature [0x67]
    (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow
    (by rw [hsc]; exact hpre.read) hm
    (by rw [hsc]; exact hok)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx_mxcsr h _ _ _ _ _, ?_⟩
  exact mmxMxcsrEffect_holds_load h _ _ _ _ _ rfl

theorem cvttps2pi_mm_m64_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (FpPre (MmxEnterPre (SseLoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8))
        (cvttps2piMmM64A32Ok p (4 + am.tail.length) am))
      (codeRange p (0x67 :: 0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (Effect.post (cvttps2piMmM64A32Effect p (4 + am.tail.length) reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvttps2piMmM64A32Effect_components]; simp [Component.Covers]) _)
    (cvttps2pi_mm_m64_a32_effect_step p reg am hv hx hb)

theorem cvttps2pi_mm_m64_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (FpPre (MmxEnterPre (SseLoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8))
        (cvttps2piMmM64A32Ok p (5 + am.tail.length) am))
      (codeRange p (0x67 :: rex :: 0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (cvttps2piMmM64A32Effect p (5 + am.tail.length) reg am) := by
  intro s h hcode ⟨⟨hpre, hes⟩, hm, hok⟩
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
  have hstep := cvttps2pi_mm_m64_a32_step s h hpre.sse hes hpre.sse.feature [0x67, rex]
    (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow
    (by rw [hsc]; exact hpre.read) hm
    (by rw [hsc]; exact hok)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx_mxcsr h _ _ _ _ _, ?_⟩
  exact mmxMxcsrEffect_holds_load h _ _ _ _ _ rfl

theorem cvttps2pi_mm_m64_rex_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (FpPre (MmxEnterPre (SseLoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8))
        (cvttps2piMmM64A32Ok p (5 + am.tail.length) am))
      (codeRange p (0x67 :: rex :: 0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (Effect.post (cvttps2piMmM64A32Effect p (5 + am.tail.length) reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvttps2piMmM64A32Effect_components]; simp [Component.Covers]) _)
    (cvttps2pi_mm_m64_rex_a32_effect_step p rex hr reg am hv hx hb)

theorem cvttps2pi_mm_m64_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (FpPre (MmxEnterPre (SseLoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeCvttps2piMmM64 dst am).length)) 8))
        (cvttps2piMmM64Ok p (encodeCvttps2piMmM64 dst am).length am))
      (codeRange p (encodeCvttps2piMmM64 dst am))
      (Effect.post (cvttps2piMmM64Effect p (encodeCvttps2piMmM64 dst am).length dst am)) := by
  unfold encodeCvttps2piMmM64
  rcases encodeMmxMem_spec 0x2C dst am with ⟨hbytes, hx, hb⟩ | ⟨hbytes, hrex, hx, hb⟩
  · have hl : (0x0F :: 0x2C :: am.modrm dst :: am.tail : List UInt8).length =
        3 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact cvttps2pi_mm_m64_triple_of_bytes p dst am hv hx hb
  · have hl : (am.rexByte false 0 :: 0x0F :: 0x2C :: am.modrm dst ::
        am.tail).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact cvttps2pi_mm_m64_rex_triple_of_bytes p _ hrex.rexPrefix dst am hv hx hb

theorem cvttps2pi_mm_m64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 3) (am : AddrMode) (hv : am.Valid) :
    Triple
      (FpPre (fun s => MmxEnterPre (SseLoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeCvttps2piMmM64 dst am).length)) 8) s ∧
        r.Ready base s)
        (cvttps2piMmM64SegOk p (r.prefixByte :: encodeCvttps2piMmM64 dst am).length base am))
      (codeRange p (r.prefixByte :: encodeCvttps2piMmM64 dst am))
      (Effect.post (cvttps2piMmM64SegEffect p (r.prefixByte :: encodeCvttps2piMmM64 dst am).length base dst am)) := by
  unfold encodeCvttps2piMmM64
  rcases encodeMmxMem_spec 0x2C dst am with ⟨hbytes, hx, hb⟩ | ⟨hbytes, hrex, hx, hb⟩
  · have hl : (r.prefixByte :: 0x0F :: 0x2C :: am.modrm dst :: am.tail :
        List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact cvttps2pi_mm_m64_seg_triple_of_bytes p r base dst am hv hx hb
  · have hl : (r.prefixByte :: am.rexByte false 0 :: 0x0F :: 0x2C ::
        am.modrm dst :: am.tail).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact cvttps2pi_mm_m64_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix dst am hv hx hb

theorem cvttps2pi_mm_m64_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (FpPre (MmxEnterPre (SseLoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeCvttps2piMmM64 dst am).length)) 8))
        (cvttps2piMmM64A32Ok p (0x67 :: encodeCvttps2piMmM64 dst am).length am))
      (codeRange p (0x67 :: encodeCvttps2piMmM64 dst am))
      (Effect.post (cvttps2piMmM64A32Effect p (0x67 :: encodeCvttps2piMmM64 dst am).length dst am)) := by
  unfold encodeCvttps2piMmM64
  rcases encodeMmxMem_spec 0x2C dst am with ⟨hbytes, hx, hb⟩ | ⟨hbytes, hrex, hx, hb⟩
  · have hl : (0x67 :: 0x0F :: 0x2C :: am.modrm dst :: am.tail :
        List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact cvttps2pi_mm_m64_a32_triple_of_bytes p dst am hv hx hb
  · have hl : (0x67 :: am.rexByte false 0 :: 0x0F :: 0x2C ::
        am.modrm dst :: am.tail).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact cvttps2pi_mm_m64_rex_a32_triple_of_bytes p _ hrex.rexPrefix dst am hv hx hb

attribute [x86_compose] cvttps2piMmM64Effect

@[x86_local] theorem cvttps2piMmM64Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {am : AddrMode} :
    Effect.Local (cvttps2piMmM64Effect p len dst am) := by
  effect_local [cvttps2piMmM64Effect, mmxMxcsrEffect, Effect.withMmx]

attribute [x86_compose] cvttps2piMmM64SegEffect

@[x86_local] theorem cvttps2piMmM64SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 3} {am : AddrMode} :
    Effect.Local (cvttps2piMmM64SegEffect p len base dst am) := by
  effect_local [cvttps2piMmM64SegEffect, mmxMxcsrEffect, Effect.withMmx]

attribute [x86_compose] cvttps2piMmM64A32Effect

@[x86_local] theorem cvttps2piMmM64A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {am : AddrMode} :
    Effect.Local (cvttps2piMmM64A32Effect p len dst am) := by
  effect_local [cvttps2piMmM64A32Effect, mmxMxcsrEffect, Effect.withMmx]

end X86Proofs
