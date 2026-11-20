import X86Proofs.Instructions.Rsqrtps.Generated.XM.Step
import X86Proofs.Instructions.Rsqrtps.Generated.XM.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def rsqrtpsXmmM128Effect [Bindings] (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 128).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), rsqrtpsSpec a b⟩] }

def rsqrtpsXmmM128Ok [Bindings] (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Prop :=
  rsqrtpsOk ((Operand.xmm dst : Operand 128).read s)
    ((Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 128).read s)

theorem rsqrtpsXmmM128Effect_components [Bindings] (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (rsqrtpsXmmM128Effect p len dst am s).components = [.xmm dst, .rip] := rfl

attribute [simp] rsqrtpsXmmM128Effect_components

def rsqrtpsXmmM128SegEffect [Bindings] (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 128).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), rsqrtpsSpec a b⟩] }

def rsqrtpsXmmM128SegOk [Bindings] (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Prop :=
  rsqrtpsOk ((Operand.xmm dst : Operand 128).read s)
    ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 128).read s)

theorem rsqrtpsXmmM128SegEffect_components [Bindings] (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (rsqrtpsXmmM128SegEffect p len base dst am s).components = [.xmm dst, .rip] := rfl

attribute [simp] rsqrtpsXmmM128SegEffect_components

def rsqrtpsXmmM128A32Effect [Bindings] (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 128).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), rsqrtpsSpec a b⟩] }

def rsqrtpsXmmM128A32Ok [Bindings] (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Prop :=
  rsqrtpsOk ((Operand.xmm dst : Operand 128).read s)
    ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 128).read s)

theorem rsqrtpsXmmM128A32Effect_components [Bindings] (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (rsqrtpsXmmM128A32Effect p len dst am s).components = [.xmm dst, .rip] := rfl

attribute [simp] rsqrtpsXmmM128A32Effect_components

theorem rsqrtps_xmm_m128_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (NumPre (SseAlignedLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))))
        (rsqrtpsXmmM128Ok p (3 + am.tail.length) (gprNumber 0 0 reg) am))
      (codeRange p (0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (rsqrtpsXmmM128Effect p (3 + am.tail.length)
        (gprNumber 0 0 reg) am) := by
  intro s h hcode ⟨hpre, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := rsqrtps_xmm_m128_step s h hpre.sse hpre.sse.feature []
    (by simp) (by simp)
    rfl rfl rfl
    rfl rfl rfl
    rfl
    reg am hv (AddrContext.legacy _ am hx hb).toSeg
    hcode.bytesAt hlow hpre.aligned hpre.read hok
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem rsqrtps_xmm_m128_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (NumPre (SseAlignedLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))))
        (rsqrtpsXmmM128Ok p (3 + am.tail.length) (gprNumber 0 0 reg) am))
      (codeRange p (0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (Effect.post (rsqrtpsXmmM128Effect p (3 + am.tail.length)
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [rsqrtpsXmmM128Effect_components]; simp [Component.Covers]) _)
    (rsqrtps_xmm_m128_effect_step p reg am hv hx hb)

theorem rsqrtps_xmm_m128_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (NumPre (SseAlignedLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))))
        (rsqrtpsXmmM128Ok p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (rex :: 0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (rsqrtpsXmmM128Effect p (4 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode ⟨hpre, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := rsqrtps_xmm_m128_step s h hpre.sse hpre.sse.feature [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl)
    reg am hv (by rw [hc]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [hc]; exact hpre.aligned) (by rw [hc]; exact hpre.read)
    (by rw [hc]; exact hok)
  simp only [hc] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem rsqrtps_xmm_m128_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (NumPre (SseAlignedLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))))
        (rsqrtpsXmmM128Ok p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (rex :: 0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (Effect.post (rsqrtpsXmmM128Effect p (4 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [rsqrtpsXmmM128Effect_components]; simp [Component.Covers]) _)
    (rsqrtps_xmm_m128_rex_effect_step p rex hr reg am hv hx hb)

theorem rsqrtps_xmm_m128_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (NumPre (fun s => SseAlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) s ∧ r.Ready base s)
        (rsqrtpsXmmM128SegOk p (4 + am.tail.length) base (gprNumber 0 0 reg) am))
      (codeRange p (r.prefixByte :: 0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (rsqrtpsXmmM128SegEffect p (4 + am.tail.length) base
        (gprNumber 0 0 reg) am) := by
  intro s h hcode ⟨⟨hpre, hseg, hbase⟩, hok⟩
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
  have hstep := rsqrtps_xmm_m128_step s h hpre.sse hpre.sse.feature [r.prefixByte]
    (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.aligned) (by rw [hsc, segAddr_withSeg]; exact hpre.read)
    (by rw [hsc, segAddr_withSeg]; exact hok)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem rsqrtps_xmm_m128_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (NumPre (fun s => SseAlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) s ∧ r.Ready base s)
        (rsqrtpsXmmM128SegOk p (4 + am.tail.length) base (gprNumber 0 0 reg) am))
      (codeRange p (r.prefixByte :: 0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (Effect.post (rsqrtpsXmmM128SegEffect p (4 + am.tail.length) base
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [rsqrtpsXmmM128SegEffect_components]; simp [Component.Covers]) _)
    (rsqrtps_xmm_m128_seg_effect_step p r base reg am hv hx hb)

theorem rsqrtps_xmm_m128_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (NumPre (fun s => SseAlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) s ∧ r.Ready base s)
        (rsqrtpsXmmM128SegOk p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (rsqrtpsXmmM128SegEffect p (5 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode ⟨⟨hpre, hseg, hbase⟩, hok⟩
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
  have hstep := rsqrtps_xmm_m128_step s h hpre.sse hpre.sse.feature [r.prefixByte, rex]
    (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.aligned) (by rw [hsc, segAddr_withSeg]; exact hpre.read)
    (by rw [hsc, segAddr_withSeg]; exact hok)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem rsqrtps_xmm_m128_rex_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (NumPre (fun s => SseAlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) s ∧ r.Ready base s)
        (rsqrtpsXmmM128SegOk p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (Effect.post (rsqrtpsXmmM128SegEffect p (5 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [rsqrtpsXmmM128SegEffect_components]; simp [Component.Covers]) _)
    (rsqrtps_xmm_m128_rex_seg_effect_step p r base rex hr reg am hv hx hb)

theorem rsqrtps_xmm_m128_a32_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (NumPre (SseAlignedLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))))
        (rsqrtpsXmmM128A32Ok p (4 + am.tail.length) (gprNumber 0 0 reg) am))
      (codeRange p (0x67 :: 0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (rsqrtpsXmmM128A32Effect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am) := by
  intro s h hcode ⟨hpre, hok⟩
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
  have hstep := rsqrtps_xmm_m128_a32_step s h hpre.sse hpre.sse.feature [0x67]
    (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.aligned) (by rw [hsc]; exact hpre.read)
    (by rw [hsc]; exact hok)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem rsqrtps_xmm_m128_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (NumPre (SseAlignedLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))))
        (rsqrtpsXmmM128A32Ok p (4 + am.tail.length) (gprNumber 0 0 reg) am))
      (codeRange p (0x67 :: 0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (Effect.post (rsqrtpsXmmM128A32Effect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [rsqrtpsXmmM128A32Effect_components]; simp [Component.Covers]) _)
    (rsqrtps_xmm_m128_a32_effect_step p reg am hv hx hb)

theorem rsqrtps_xmm_m128_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (NumPre (SseAlignedLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))))
        (rsqrtpsXmmM128A32Ok p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (0x67 :: rex :: 0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (rsqrtpsXmmM128A32Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode ⟨hpre, hok⟩
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
  have hstep := rsqrtps_xmm_m128_a32_step s h hpre.sse hpre.sse.feature [0x67, rex]
    (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.aligned) (by rw [hsc]; exact hpre.read)
    (by rw [hsc]; exact hok)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (rexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (rexContext s.DS rex.toBitVec)).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem rsqrtps_xmm_m128_rex_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (NumPre (SseAlignedLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))))
        (rsqrtpsXmmM128A32Ok p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (0x67 :: rex :: 0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (Effect.post (rsqrtpsXmmM128A32Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [rsqrtpsXmmM128A32Effect_components]; simp [Component.Covers]) _)
    (rsqrtps_xmm_m128_rex_a32_effect_step p rex hr reg am hv hx hb)

theorem rsqrtps_xmm_m128_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (NumPre (SseAlignedLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeRsqrtpsXmmM128 dst am).length)))
        (rsqrtpsXmmM128Ok p (encodeRsqrtpsXmmM128 dst am).length (dst.setWidth 5) am))
      (codeRange p (encodeRsqrtpsXmmM128 dst am))
      (Effect.post (rsqrtpsXmmM128Effect p (encodeRsqrtpsXmmM128 dst am).length
        (dst.setWidth 5) am)) := by
  unfold encodeRsqrtpsXmmM128
  rcases encodeSseMem_spec 0x52 dst am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (0x0F :: 0x52 :: am.modrm (regLow dst) :: am.tail :
        List UInt8).length = 3 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact rsqrtps_xmm_m128_triple_of_bytes p (regLow dst) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := rsqrtps_xmm_m128_rex_triple_of_bytes p _ hrex.rexPrefix (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (am.rexByte false dst :: 0x0F :: 0x52 :: am.modrm (regLow dst) ::
        am.tail).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact this

theorem rsqrtps_xmm_m128_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (NumPre (SseAlignedLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeRsqrtpsXmmM128 dst am).length)))
        (rsqrtpsXmmM128A32Ok p (0x67 :: encodeRsqrtpsXmmM128 dst am).length (dst.setWidth 5) am))
      (codeRange p (0x67 :: encodeRsqrtpsXmmM128 dst am))
      (Effect.post (rsqrtpsXmmM128A32Effect p (0x67 :: encodeRsqrtpsXmmM128 dst am).length
        (dst.setWidth 5) am)) := by
  unfold encodeRsqrtpsXmmM128
  rcases encodeSseMem_spec 0x52 dst am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (0x67 :: 0x0F :: 0x52 :: am.modrm (regLow dst) :: am.tail :
        List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact rsqrtps_xmm_m128_a32_triple_of_bytes p (regLow dst) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := rsqrtps_xmm_m128_rex_a32_triple_of_bytes p _ hrex.rexPrefix (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (0x67 :: am.rexByte false dst :: 0x0F :: 0x52 :: am.modrm (regLow dst) ::
        am.tail).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact this

theorem rsqrtps_xmm_m128_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple
      (NumPre (fun s => SseAlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeRsqrtpsXmmM128 dst am).length)) s ∧ r.Ready base s)
        (rsqrtpsXmmM128SegOk p (r.prefixByte :: encodeRsqrtpsXmmM128 dst am).length base (dst.setWidth 5) am))
      (codeRange p (r.prefixByte :: encodeRsqrtpsXmmM128 dst am))
      (Effect.post (rsqrtpsXmmM128SegEffect p (r.prefixByte :: encodeRsqrtpsXmmM128 dst am).length base
        (dst.setWidth 5) am)) := by
  unfold encodeRsqrtpsXmmM128
  rcases encodeSseMem_spec 0x52 dst am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (r.prefixByte :: 0x0F :: 0x52 :: am.modrm (regLow dst) ::
        am.tail : List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact rsqrtps_xmm_m128_seg_triple_of_bytes p r base (regLow dst) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := rsqrtps_xmm_m128_rex_seg_triple_of_bytes p r base _
      hrex.rexPrefix (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (r.prefixByte :: am.rexByte false dst :: 0x0F :: 0x52 ::
        am.modrm (regLow dst) :: am.tail).length = 5 + am.tail.length := by
      simp; omega
    rw [hbytes, hl]
    exact this

attribute [x86_compose] rsqrtpsXmmM128Effect

@[x86_local] theorem rsqrtpsXmmM128Effect_local [Bindings] {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (rsqrtpsXmmM128Effect p len dst am) := by
  effect_local [rsqrtpsXmmM128Effect]

attribute [x86_compose] rsqrtpsXmmM128SegEffect

@[x86_local] theorem rsqrtpsXmmM128SegEffect_local [Bindings] {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (rsqrtpsXmmM128SegEffect p len base dst am) := by
  effect_local [rsqrtpsXmmM128SegEffect]

attribute [x86_compose] rsqrtpsXmmM128A32Effect

@[x86_local] theorem rsqrtpsXmmM128A32Effect_local [Bindings] {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (rsqrtpsXmmM128A32Effect p len dst am) := by
  effect_local [rsqrtpsXmmM128A32Effect]

end X86Proofs
