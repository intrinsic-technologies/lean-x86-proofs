import X86Proofs.Instructions.Cvttpd2pi.Generated.MmM.Step
import X86Proofs.Instructions.Cvttpd2pi.Generated.MmM.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cvttpd2piMmM128Effect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (am : AddrMode)
    (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 128).read s
  mmxMxcsrEffect s (p + BitVec.ofNat 64 len) dst (cvttpd2piSpec s.MXCSR b)
    (mxOr s.MXCSR (cvttpd2piFlags s.MXCSR b))

def cvttpd2piMmM128Ok (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Prop :=
  cvttpd2piOk s.MXCSR
    ((Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 128).read s)

@[simp] theorem cvttpd2piMmM128Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (am : AddrMode) (s : RamState) :
    (cvttpd2piMmM128Effect p len dst am s).components = [.fpr dst, .mxcsr, .fsw, .ftw, .rip] := rfl

def cvttpd2piMmM128SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 3)
    (am : AddrMode) (s : RamState) : Effect :=
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 128).read s
  mmxMxcsrEffect s (p + BitVec.ofNat 64 len) dst (cvttpd2piSpec s.MXCSR b)
    (mxOr s.MXCSR (cvttpd2piFlags s.MXCSR b))

def cvttpd2piMmM128SegOk (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode)
    (s : RamState) : Prop :=
  cvttpd2piOk s.MXCSR
    ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 128).read s)

@[simp] theorem cvttpd2piMmM128SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 3) (am : AddrMode) (s : RamState) :
    (cvttpd2piMmM128SegEffect p len base dst am s).components =
      [.fpr dst, .mxcsr, .fsw, .ftw, .rip] := rfl

def cvttpd2piMmM128A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (am : AddrMode)
    (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 128).read s
  mmxMxcsrEffect s (p + BitVec.ofNat 64 len) dst (cvttpd2piSpec s.MXCSR b)
    (mxOr s.MXCSR (cvttpd2piFlags s.MXCSR b))

def cvttpd2piMmM128A32Ok (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Prop :=
  cvttpd2piOk s.MXCSR
    ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 128).read s)

@[simp] theorem cvttpd2piMmM128A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (am : AddrMode) (s : RamState) :
    (cvttpd2piMmM128A32Effect p len dst am s).components = [.fpr dst, .mxcsr, .fsw, .ftw, .rip] := rfl

theorem cvttpd2pi_mm_m128_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (FpPre (MmxEnterPre (Sse2AlignedLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length)))))
        (cvttpd2piMmM128Ok p (4 + am.tail.length) am))
      (codeRange p (0x66 :: 0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (cvttpd2piMmM128Effect p (4 + am.tail.length) reg am) := by
  intro s h hcode ⟨⟨hpre, hes⟩, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cvttpd2pi_mm_m128_step s h hpre.sse hes hpre.sse2 [0x66]
    (by simpa using scanPrefix_66) (by simp)
    rfl rfl rfl rfl
    rfl
    reg am hv (AddrContext.osz _ am hx hb).toSeg
    hcode.bytesAt hlow hpre.aligned hpre.read hm hok
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx_mxcsr h _ _ _ _ _, ?_⟩
  exact mmxMxcsrEffect_holds_load h _ _ _ _ _ rfl

theorem cvttpd2pi_mm_m128_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (FpPre (MmxEnterPre (Sse2AlignedLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length)))))
        (cvttpd2piMmM128Ok p (4 + am.tail.length) am))
      (codeRange p (0x66 :: 0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (Effect.post (cvttpd2piMmM128Effect p (4 + am.tail.length) reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvttpd2piMmM128Effect_components]; simp [Component.Covers]) _)
    (cvttpd2pi_mm_m128_effect_step p reg am hv hx hb)

theorem cvttpd2pi_mm_m128_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (FpPre (MmxEnterPre (Sse2AlignedLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length)))))
        (cvttpd2piMmM128Ok p (5 + am.tail.length) am))
      (codeRange p (0x66 :: rex :: 0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (cvttpd2piMmM128Effect p (5 + am.tail.length) reg am) := by
  intro s h hcode ⟨⟨hpre, hes⟩, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hc := scanContext_66_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := cvttpd2pi_mm_m128_step s h hpre.sse hes hpre.sse2 [0x66, rex]
    (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl)
    reg am hv (by rw [hc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [hc]; exact hpre.aligned)
    (by rw [hc]; exact hpre.read) hm
    (by rw [hc]; exact hok)
  simp only [hc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx_mxcsr h _ _ _ _ _, ?_⟩
  exact mmxMxcsrEffect_holds_load h _ _ _ _ _ rfl

theorem cvttpd2pi_mm_m128_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (FpPre (MmxEnterPre (Sse2AlignedLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length)))))
        (cvttpd2piMmM128Ok p (5 + am.tail.length) am))
      (codeRange p (0x66 :: rex :: 0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (Effect.post (cvttpd2piMmM128Effect p (5 + am.tail.length) reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvttpd2piMmM128Effect_components]; simp [Component.Covers]) _)
    (cvttpd2pi_mm_m128_rex_effect_step p rex hr reg am hv hx hb)

theorem cvttpd2pi_mm_m128_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (FpPre (fun s => MmxEnterPre (Sse2AlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length)))) s ∧
        r.Ready base s)
        (cvttpd2piMmM128SegOk p (5 + am.tail.length) base am))
      (codeRange p (r.prefixByte :: 0x66 :: 0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (cvttpd2piMmM128SegEffect p (5 + am.tail.length) base reg am) := by
  intro s h hcode ⟨⟨⟨hpre, hes⟩, hseg, hbase⟩, hm, hok⟩
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
  have hstep := cvttpd2pi_mm_m128_step s h hpre.sse hes hpre.sse2 [r.prefixByte, 0x66]
    (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.aligned)
    (by rw [hsc, segAddr_withSeg]; exact hpre.read) hm
    (by rw [hsc, segAddr_withSeg]; exact hok)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx_mxcsr h _ _ _ _ _, ?_⟩
  exact mmxMxcsrEffect_holds_load h _ _ _ _ _ rfl

theorem cvttpd2pi_mm_m128_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (FpPre (fun s => MmxEnterPre (Sse2AlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length)))) s ∧
        r.Ready base s)
        (cvttpd2piMmM128SegOk p (5 + am.tail.length) base am))
      (codeRange p (r.prefixByte :: 0x66 :: 0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (Effect.post (cvttpd2piMmM128SegEffect p (5 + am.tail.length) base reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvttpd2piMmM128SegEffect_components]; simp [Component.Covers]) _)
    (cvttpd2pi_mm_m128_seg_effect_step p r base reg am hv hx hb)

theorem cvttpd2pi_mm_m128_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (FpPre (fun s => MmxEnterPre (Sse2AlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (6 + am.tail.length)))) s ∧
        r.Ready base s)
        (cvttpd2piMmM128SegOk p (6 + am.tail.length) base am))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (cvttpd2piMmM128SegEffect p (6 + am.tail.length) base reg am) := by
  intro s h hcode ⟨⟨⟨hpre, hes⟩, hseg, hbase⟩, hm, hok⟩
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
  have hstep := cvttpd2pi_mm_m128_step s h hpre.sse hes hpre.sse2 [r.prefixByte, 0x66, rex]
    (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.aligned)
    (by rw [hsc, segAddr_withSeg]; exact hpre.read) hm
    (by rw [hsc, segAddr_withSeg]; exact hok)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx_mxcsr h _ _ _ _ _, ?_⟩
  exact mmxMxcsrEffect_holds_load h _ _ _ _ _ rfl

theorem cvttpd2pi_mm_m128_rex_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (FpPre (fun s => MmxEnterPre (Sse2AlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (6 + am.tail.length)))) s ∧
        r.Ready base s)
        (cvttpd2piMmM128SegOk p (6 + am.tail.length) base am))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (Effect.post (cvttpd2piMmM128SegEffect p (6 + am.tail.length) base reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvttpd2piMmM128SegEffect_components]; simp [Component.Covers]) _)
    (cvttpd2pi_mm_m128_rex_seg_effect_step p r base rex hr reg am hv hx hb)

theorem cvttpd2pi_mm_m128_a32_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (FpPre (MmxEnterPre (Sse2AlignedLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length)))))
        (cvttpd2piMmM128A32Ok p (5 + am.tail.length) am))
      (codeRange p (0x67 :: 0x66 :: 0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (cvttpd2piMmM128A32Effect p (5 + am.tail.length) reg am) := by
  intro s h hcode ⟨⟨hpre, hes⟩, hm, hok⟩
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
  have hstep := cvttpd2pi_mm_m128_a32_step s h hpre.sse hes hpre.sse2 [0x67, 0x66]
    (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.aligned)
    (by rw [hsc]; exact hpre.read) hm
    (by rw [hsc]; exact hok)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx_mxcsr h _ _ _ _ _, ?_⟩
  exact mmxMxcsrEffect_holds_load h _ _ _ _ _ rfl

theorem cvttpd2pi_mm_m128_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (FpPre (MmxEnterPre (Sse2AlignedLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length)))))
        (cvttpd2piMmM128A32Ok p (5 + am.tail.length) am))
      (codeRange p (0x67 :: 0x66 :: 0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (Effect.post (cvttpd2piMmM128A32Effect p (5 + am.tail.length) reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvttpd2piMmM128A32Effect_components]; simp [Component.Covers]) _)
    (cvttpd2pi_mm_m128_a32_effect_step p reg am hv hx hb)

theorem cvttpd2pi_mm_m128_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (FpPre (MmxEnterPre (Sse2AlignedLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length)))))
        (cvttpd2piMmM128A32Ok p (6 + am.tail.length) am))
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (cvttpd2piMmM128A32Effect p (6 + am.tail.length) reg am) := by
  intro s h hcode ⟨⟨hpre, hes⟩, hm, hok⟩
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
  have hstep := cvttpd2pi_mm_m128_a32_step s h hpre.sse hes hpre.sse2 [0x67, 0x66, rex]
    (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.aligned)
    (by rw [hsc]; exact hpre.read) hm
    (by rw [hsc]; exact hok)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx_mxcsr h _ _ _ _ _, ?_⟩
  exact mmxMxcsrEffect_holds_load h _ _ _ _ _ rfl

theorem cvttpd2pi_mm_m128_rex_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (FpPre (MmxEnterPre (Sse2AlignedLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length)))))
        (cvttpd2piMmM128A32Ok p (6 + am.tail.length) am))
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: 0x2C :: am.modrm reg :: am.tail))
      (Effect.post (cvttpd2piMmM128A32Effect p (6 + am.tail.length) reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvttpd2piMmM128A32Effect_components]; simp [Component.Covers]) _)
    (cvttpd2pi_mm_m128_rex_a32_effect_step p rex hr reg am hv hx hb)

theorem cvttpd2pi_mm_m128_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (FpPre (MmxEnterPre (Sse2AlignedLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeCvttpd2piMmM128 dst am).length))))
        (cvttpd2piMmM128Ok p (encodeCvttpd2piMmM128 dst am).length am))
      (codeRange p (encodeCvttpd2piMmM128 dst am))
      (Effect.post (cvttpd2piMmM128Effect p (encodeCvttpd2piMmM128 dst am).length dst am)) := by
  unfold encodeCvttpd2piMmM128
  rcases encodeMmxMem_spec 0x2C dst am with ⟨hbytes, hx, hb⟩ | ⟨hbytes, hrex, hx, hb⟩
  · have hl : (0x66 :: 0x0F :: 0x2C :: am.modrm dst :: am.tail : List UInt8).length =
        4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact cvttpd2pi_mm_m128_triple_of_bytes p dst am hv hx hb
  · have hl : (0x66 :: am.rexByte false 0 :: 0x0F :: 0x2C :: am.modrm dst ::
        am.tail).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact cvttpd2pi_mm_m128_rex_triple_of_bytes p _ hrex.rexPrefix dst am hv hx hb

theorem cvttpd2pi_mm_m128_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 3) (am : AddrMode) (hv : am.Valid) :
    Triple
      (FpPre (fun s => MmxEnterPre (Sse2AlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeCvttpd2piMmM128 dst am).length))) s ∧
        r.Ready base s)
        (cvttpd2piMmM128SegOk p (r.prefixByte :: encodeCvttpd2piMmM128 dst am).length base am))
      (codeRange p (r.prefixByte :: encodeCvttpd2piMmM128 dst am))
      (Effect.post (cvttpd2piMmM128SegEffect p (r.prefixByte :: encodeCvttpd2piMmM128 dst am).length base dst am)) := by
  unfold encodeCvttpd2piMmM128
  rcases encodeMmxMem_spec 0x2C dst am with ⟨hbytes, hx, hb⟩ | ⟨hbytes, hrex, hx, hb⟩
  · have hl : (r.prefixByte :: 0x66 :: 0x0F :: 0x2C :: am.modrm dst :: am.tail :
        List UInt8).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact cvttpd2pi_mm_m128_seg_triple_of_bytes p r base dst am hv hx hb
  · have hl : (r.prefixByte :: 0x66 :: am.rexByte false 0 :: 0x0F :: 0x2C ::
        am.modrm dst :: am.tail).length = 6 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact cvttpd2pi_mm_m128_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix dst am hv hx hb

theorem cvttpd2pi_mm_m128_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (FpPre (MmxEnterPre (Sse2AlignedLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeCvttpd2piMmM128 dst am).length))))
        (cvttpd2piMmM128A32Ok p (0x67 :: encodeCvttpd2piMmM128 dst am).length am))
      (codeRange p (0x67 :: encodeCvttpd2piMmM128 dst am))
      (Effect.post (cvttpd2piMmM128A32Effect p (0x67 :: encodeCvttpd2piMmM128 dst am).length dst am)) := by
  unfold encodeCvttpd2piMmM128
  rcases encodeMmxMem_spec 0x2C dst am with ⟨hbytes, hx, hb⟩ | ⟨hbytes, hrex, hx, hb⟩
  · have hl : (0x67 :: 0x66 :: 0x0F :: 0x2C :: am.modrm dst :: am.tail :
        List UInt8).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact cvttpd2pi_mm_m128_a32_triple_of_bytes p dst am hv hx hb
  · have hl : (0x67 :: 0x66 :: am.rexByte false 0 :: 0x0F :: 0x2C ::
        am.modrm dst :: am.tail).length = 6 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact cvttpd2pi_mm_m128_rex_a32_triple_of_bytes p _ hrex.rexPrefix dst am hv hx hb

attribute [x86_compose] cvttpd2piMmM128Effect

@[x86_local] theorem cvttpd2piMmM128Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {am : AddrMode} :
    Effect.Local (cvttpd2piMmM128Effect p len dst am) := by
  effect_local [cvttpd2piMmM128Effect, mmxMxcsrEffect, Effect.withMmx]

attribute [x86_compose] cvttpd2piMmM128SegEffect

@[x86_local] theorem cvttpd2piMmM128SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 3} {am : AddrMode} :
    Effect.Local (cvttpd2piMmM128SegEffect p len base dst am) := by
  effect_local [cvttpd2piMmM128SegEffect, mmxMxcsrEffect, Effect.withMmx]

attribute [x86_compose] cvttpd2piMmM128A32Effect

@[x86_local] theorem cvttpd2piMmM128A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {am : AddrMode} :
    Effect.Local (cvttpd2piMmM128A32Effect p len dst am) := by
  effect_local [cvttpd2piMmM128A32Effect, mmxMxcsrEffect, Effect.withMmx]

end X86Proofs
