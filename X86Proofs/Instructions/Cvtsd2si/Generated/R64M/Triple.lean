import X86Proofs.Instructions.Cvtsd2si.Generated.R64M.Step
import X86Proofs.Instructions.Cvtsd2si.Generated.R64M.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cvtsd2siR64M64Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), cvts2siSpec 64 64 s.MXCSR b⟩,
      ⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (cvts2siFlags 64 64 s.MXCSR b)⟩] }

def cvtsd2siR64M64Ok (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Prop :=
  cvts2siOk 64 64 s.MXCSR ((Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s)

@[simp] theorem cvtsd2siR64M64Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (cvtsd2siR64M64Effect p len dst am s).components = [.reg dst, .mxcsr, .rip] := rfl

def cvtsd2siR64M64SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) : Effect :=
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), cvts2siSpec 64 64 s.MXCSR b⟩,
      ⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (cvts2siFlags 64 64 s.MXCSR b)⟩] }

def cvtsd2siR64M64SegOk (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) (s : RamState) :
    Prop :=
  cvts2siOk 64 64 s.MXCSR
    ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s)

@[simp] theorem cvtsd2siR64M64SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (cvtsd2siR64M64SegEffect p len base dst am s).components = [.reg dst, .mxcsr, .rip] := rfl

def cvtsd2siR64M64A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), cvts2siSpec 64 64 s.MXCSR b⟩,
      ⟨(Operand.mxcsr : Operand 32), mxOr s.MXCSR (cvts2siFlags 64 64 s.MXCSR b)⟩] }

def cvtsd2siR64M64A32Ok (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Prop :=
  cvts2siOk 64 64 s.MXCSR ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 64).read s)

@[simp] theorem cvtsd2siR64M64A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (cvtsd2siR64M64A32Effect p len dst am s).components = [.reg dst, .mxcsr, .rip] := rfl

theorem cvtsd2si_r64_m64_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
        (cvtsd2siR64M64Ok p (5 + am.tail.length) am))
      (codeRange p (0xF2 :: rex :: 0x0F :: 0x2D :: am.modrm reg :: am.tail))
      (cvtsd2siR64M64Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hc := scanContext_f2_rex s.DS (PrefixSegments.ofState s) hr.rexPrefix
  have hstep := cvtsd2si_r64_m64_step s h hpre.sse hpre.sse2 [0xF2, rex]
    (by simp [scanPrefix_f2, hr.rexPrefix.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; exact hr.rex_w s.DS) (by rw [hc]; rfl) (by rw [hc]; rfl)
    reg am hv (by rw [hc]; exact (AddrContext.repneRex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [hc]; exact hpre.read) hm
    (by rw [hc]; exact hok)
  simp only [hc] at hstep
  have hdst : gprNumber (repneRexContext s.DS rex.toBitVec).rex_r4
      (repneRexContext s.DS rex.toBitVec).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_reg_mxcsr h _ _ _ _ _,
    ⟨afterStep_load_reg_mxcsr_rip h _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_load_reg_mxcsr s _ _ _ _ _⟩⟩
  refine ⟨?_, ?_⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_writeResult_self]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    rfl
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [writeResult, Operand.write_reg64, Operand.write_mxcsr, Operand.read_mxcsr,
      Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR, beforeFetch_MXCSR]
    rfl

theorem cvtsd2si_r64_m64_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
        (cvtsd2siR64M64Ok p (5 + am.tail.length) am))
      (codeRange p (0xF2 :: rex :: 0x0F :: 0x2D :: am.modrm reg :: am.tail))
      (Effect.post (cvtsd2siR64M64Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvtsd2siR64M64Effect_components]; simp [Component.Covers]) _)
    (cvtsd2si_r64_m64_rex_effect_step p rex hr reg am hv hx hb)

theorem cvtsd2si_r64_m64_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (FpPre (fun s => Sse2LoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (6 + am.tail.length))) 8 s ∧ r.Ready base s)
        (cvtsd2siR64M64SegOk p (6 + am.tail.length) base am))
      (codeRange p (r.prefixByte :: 0xF2 :: rex :: 0x0F :: 0x2D :: am.modrm reg :: am.tail))
      (cvtsd2siR64M64SegEffect p (6 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode ⟨⟨hpre, hseg, hbase⟩, hm, hok⟩
  have hp := hpre.rip
  subst hp hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2, rex] =
      withSeg (repneRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF2, rex]
      (noSegPrefix_cons noSegPrefix_f2 (noSegPrefix_cons hr.rexPrefix.noSegPrefix noSegPrefix_nil)), scanContext_f2_rex s.DS (PrefixSegments.ofState s) hr.rexPrefix]
  have hstep := cvtsd2si_r64_m64_step s h hpre.sse hpre.sse2 [r.prefixByte, 0xF2, rex]
    (scanPrefix_seg_cons r (by simp [scanPrefix_f2, hr.rexPrefix.scanPrefix])) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; exact hr.rex_w s.DS) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.repneRex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.read) hm
    (by rw [hsc, segAddr_withSeg]; exact hok)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (repneRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (repneRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_reg_mxcsr h _ _ _ _ _,
    ⟨afterStep_load_reg_mxcsr_rip h _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_load_reg_mxcsr s _ _ _ _ _⟩⟩
  refine ⟨?_, ?_⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_writeResult_self]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    rfl
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [writeResult, Operand.write_reg64, Operand.write_mxcsr, Operand.read_mxcsr,
      Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR, beforeFetch_MXCSR]
    rfl

theorem cvtsd2si_r64_m64_rex_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (FpPre (fun s => Sse2LoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (6 + am.tail.length))) 8 s ∧ r.Ready base s)
        (cvtsd2siR64M64SegOk p (6 + am.tail.length) base am))
      (codeRange p (r.prefixByte :: 0xF2 :: rex :: 0x0F :: 0x2D :: am.modrm reg :: am.tail))
      (Effect.post (cvtsd2siR64M64SegEffect p (6 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvtsd2siR64M64SegEffect_components]; simp [Component.Covers]) _)
    (cvtsd2si_r64_m64_rex_seg_effect_step p r base rex hr reg am hv hx hb)

theorem cvtsd2si_r64_m64_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 8)
        (cvtsd2siR64M64A32Ok p (6 + am.tail.length) am))
      (codeRange p (0x67 :: 0xF2 :: rex :: 0x0F :: 0x2D :: am.modrm reg :: am.tail))
      (cvtsd2siR64M64A32Effect p (6 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode ⟨hpre, hm, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0xF2, rex] =
      withAsz (repneRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_f2_rex s.DS (PrefixSegments.ofState s) hr.rexPrefix]
  have hstep := cvtsd2si_r64_m64_a32_step s h hpre.sse hpre.sse2 [0x67, 0xF2, rex]
    (scanPrefix_asz_cons (by simp [scanPrefix_f2, hr.rexPrefix.scanPrefix])) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; exact hr.rex_w s.DS) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.repneRex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.read) hm
    (by rw [hsc]; exact hok)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (repneRexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (repneRexContext s.DS rex.toBitVec)).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_reg_mxcsr h _ _ _ _ _,
    ⟨afterStep_load_reg_mxcsr_rip h _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_load_reg_mxcsr s _ _ _ _ _⟩⟩
  refine ⟨?_, ?_⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_writeResult_self]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR,
      beforeFetch_MXCSR]
    rfl
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [writeResult, Operand.write_reg64, Operand.write_mxcsr, Operand.read_mxcsr,
      Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_MXCSR, beforeFetch_MXCSR]
    rfl

theorem cvtsd2si_r64_m64_rex_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 8)
        (cvtsd2siR64M64A32Ok p (6 + am.tail.length) am))
      (codeRange p (0x67 :: 0xF2 :: rex :: 0x0F :: 0x2D :: am.modrm reg :: am.tail))
      (Effect.post (cvtsd2siR64M64A32Effect p (6 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cvtsd2siR64M64A32Effect_components]; simp [Component.Covers]) _)
    (cvtsd2si_r64_m64_rex_a32_effect_step p rex hr reg am hv hx hb)

theorem cvtsd2si_r64_m64_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeCvtsd2siR64M64 dst am).length)) 8)
        (cvtsd2siR64M64Ok p (encodeCvtsd2siR64M64 dst am).length am))
      (codeRange p (encodeCvtsd2siR64M64 dst am))
      (Effect.post (cvtsd2siR64M64Effect p (encodeCvtsd2siR64M64 dst am).length
        (dst.setWidth 5) am)) := by
  unfold encodeCvtsd2siR64M64
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := cvtsd2si_r64_m64_rex_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
  rw [hr, gprNumber_reg] at this
  have hl : (0xF2 :: am.rexByte true dst :: 0x0F :: 0x2D :: am.modrm (regLow dst) ::
      am.tail).length = 5 + am.tail.length := by simp; omega
  unfold encodeSseMemW
  rw [hl]
  exact this

theorem cvtsd2si_r64_m64_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (FpPre (Sse2LoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeCvtsd2siR64M64 dst am).length)) 8)
        (cvtsd2siR64M64A32Ok p (0x67 :: encodeCvtsd2siR64M64 dst am).length am))
      (codeRange p (0x67 :: encodeCvtsd2siR64M64 dst am))
      (Effect.post (cvtsd2siR64M64A32Effect p (0x67 :: encodeCvtsd2siR64M64 dst am).length
        (dst.setWidth 5) am)) := by
  unfold encodeCvtsd2siR64M64
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := cvtsd2si_r64_m64_rex_a32_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
  rw [hr, gprNumber_reg] at this
  have hl : (0x67 :: 0xF2 :: am.rexByte true dst :: 0x0F :: 0x2D :: am.modrm (regLow dst) ::
      am.tail).length = 6 + am.tail.length := by simp; omega
  unfold encodeSseMemW
  rw [hl]
  exact this

theorem cvtsd2si_r64_m64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple
      (FpPre (fun s => Sse2LoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeCvtsd2siR64M64 dst am).length)) 8 s ∧ r.Ready base s)
        (cvtsd2siR64M64SegOk p (r.prefixByte :: encodeCvtsd2siR64M64 dst am).length base am))
      (codeRange p (r.prefixByte :: encodeCvtsd2siR64M64 dst am))
      (Effect.post (cvtsd2siR64M64SegEffect p (r.prefixByte :: encodeCvtsd2siR64M64 dst am).length base
        (dst.setWidth 5) am)) := by
  unfold encodeCvtsd2siR64M64
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := cvtsd2si_r64_m64_rex_seg_triple_of_bytes p r base _ hrex (regLow dst) am hv hx hb
  rw [hr, gprNumber_reg] at this
  have hl : (r.prefixByte :: 0xF2 :: am.rexByte true dst :: 0x0F :: 0x2D ::
      am.modrm (regLow dst) :: am.tail).length = 6 + am.tail.length := by simp; omega
  unfold encodeSseMemW
  rw [hl]
  exact this

attribute [x86_compose] cvtsd2siR64M64Effect

@[x86_local] theorem cvtsd2siR64M64Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (cvtsd2siR64M64Effect p len dst am) := by
  effect_local [cvtsd2siR64M64Effect]

attribute [x86_compose] cvtsd2siR64M64SegEffect

@[x86_local] theorem cvtsd2siR64M64SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (cvtsd2siR64M64SegEffect p len base dst am) := by
  effect_local [cvtsd2siR64M64SegEffect]

attribute [x86_compose] cvtsd2siR64M64A32Effect

@[x86_local] theorem cvtsd2siR64M64A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (cvtsd2siR64M64A32Effect p len dst am) := by
  effect_local [cvtsd2siR64M64A32Effect]

end X86Proofs
