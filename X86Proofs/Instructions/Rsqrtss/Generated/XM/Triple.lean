import X86Proofs.Instructions.Rsqrtss.Generated.XM.Step
import X86Proofs.Instructions.Rsqrtss.Generated.XM.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def rsqrtssXmmM32Effect [Bindings] (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), rsqrtssSpec a b⟩] }

def rsqrtssXmmM32Ok [Bindings] (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Prop :=
  rsqrtssOk ((Operand.xmm dst : Operand 128).read s)
    ((Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s)

theorem rsqrtssXmmM32Effect_components [Bindings] (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (rsqrtssXmmM32Effect p len dst am s).components = [.xmm dst, .rip] := rfl

attribute [simp] rsqrtssXmmM32Effect_components

def rsqrtssXmmM32SegEffect [Bindings] (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), rsqrtssSpec a b⟩] }

def rsqrtssXmmM32SegOk [Bindings] (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Prop :=
  rsqrtssOk ((Operand.xmm dst : Operand 128).read s)
    ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s)

theorem rsqrtssXmmM32SegEffect_components [Bindings] (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (rsqrtssXmmM32SegEffect p len base dst am s).components = [.xmm dst, .rip] := rfl

attribute [simp] rsqrtssXmmM32SegEffect_components

def rsqrtssXmmM32A32Effect [Bindings] (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := (Operand.xmm dst : Operand 128).read s
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), rsqrtssSpec a b⟩] }

def rsqrtssXmmM32A32Ok [Bindings] (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Prop :=
  rsqrtssOk ((Operand.xmm dst : Operand 128).read s)
    ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 32).read s)

theorem rsqrtssXmmM32A32Effect_components [Bindings] (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (rsqrtssXmmM32A32Effect p len dst am s).components = [.xmm dst, .rip] := rfl

attribute [simp] rsqrtssXmmM32A32Effect_components

theorem rsqrtss_xmm_m32_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (NumPre (SseLoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
        (rsqrtssXmmM32Ok p (4 + am.tail.length) (gprNumber 0 0 reg) am))
      (codeRange p (0xF3 :: 0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (rsqrtssXmmM32Effect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am) := by
  intro s h hcode ⟨hpre, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := rsqrtss_xmm_m32_step s h hpre.sse hpre.sse.feature [0xF3]
    (by simpa using scanPrefix_f3) (by simp)
    rfl rfl rfl
    rfl rfl rfl
    reg am hv (AddrContext.rep _ am hx hb).toSeg
    hcode.bytesAt hlow hpre.read hok
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0xF3]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0xF3]).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem rsqrtss_xmm_m32_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (NumPre (SseLoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
        (rsqrtssXmmM32Ok p (4 + am.tail.length) (gprNumber 0 0 reg) am))
      (codeRange p (0xF3 :: 0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (Effect.post (rsqrtssXmmM32Effect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [rsqrtssXmmM32Effect_components]; simp [Component.Covers]) _)
    (rsqrtss_xmm_m32_effect_step p reg am hv hx hb)

theorem rsqrtss_xmm_m32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (NumPre (SseLoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4)
        (rsqrtssXmmM32Ok p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (0xF3 :: rex :: 0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (rsqrtssXmmM32Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode ⟨hpre, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hc := scanContext_f3_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := rsqrtss_xmm_m32_step s h hpre.sse hpre.sse.feature [0xF3, rex]
    (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    reg am hv (by rw [hc]; exact (AddrContext.repRex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [hc]; exact hpre.read)
    (by rw [hc]; exact hok)
  simp only [hc] at hstep
  have hdst : gprNumber (repRexContext s.DS rex.toBitVec).rex_r4
      (repRexContext s.DS rex.toBitVec).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem rsqrtss_xmm_m32_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (NumPre (SseLoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4)
        (rsqrtssXmmM32Ok p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (0xF3 :: rex :: 0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (Effect.post (rsqrtssXmmM32Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [rsqrtssXmmM32Effect_components]; simp [Component.Covers]) _)
    (rsqrtss_xmm_m32_rex_effect_step p rex hr reg am hv hx hb)

theorem rsqrtss_xmm_m32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (NumPre (fun s => SseLoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 4 s ∧ r.Ready base s)
        (rsqrtssXmmM32SegOk p (5 + am.tail.length) base (gprNumber 0 0 reg) am))
      (codeRange p (r.prefixByte :: 0xF3 :: 0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (rsqrtssXmmM32SegEffect p (5 + am.tail.length) base
        (gprNumber 0 0 reg) am) := by
  intro s h hcode ⟨⟨hpre, hseg, hbase⟩, hok⟩
  have hp := hpre.rip
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3]
      (noSegPrefix_cons noSegPrefix_f3 noSegPrefix_nil)]
  have hstep := rsqrtss_xmm_m32_step s h hpre.sse hpre.sse.feature [r.prefixByte, 0xF3]
    (scanPrefix_seg_cons r (by simpa using scanPrefix_f3)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rep _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.read)
    (by rw [hsc, segAddr_withSeg]; exact hok)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) (r.select (PrefixSegments.ofState s))).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem rsqrtss_xmm_m32_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (NumPre (fun s => SseLoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 4 s ∧ r.Ready base s)
        (rsqrtssXmmM32SegOk p (5 + am.tail.length) base (gprNumber 0 0 reg) am))
      (codeRange p (r.prefixByte :: 0xF3 :: 0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (Effect.post (rsqrtssXmmM32SegEffect p (5 + am.tail.length) base
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [rsqrtssXmmM32SegEffect_components]; simp [Component.Covers]) _)
    (rsqrtss_xmm_m32_seg_effect_step p r base reg am hv hx hb)

theorem rsqrtss_xmm_m32_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (NumPre (fun s => SseLoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (6 + am.tail.length))) 4 s ∧ r.Ready base s)
        (rsqrtssXmmM32SegOk p (6 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (r.prefixByte :: 0xF3 :: rex :: 0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (rsqrtssXmmM32SegEffect p (6 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode ⟨⟨hpre, hseg, hbase⟩, hok⟩
  have hp := hpre.rip
  subst hp hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3, rex] =
      withSeg (repRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3, rex]
      (noSegPrefix_cons noSegPrefix_f3 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_f3_rex s.DS (PrefixSegments.ofState s) hr]
  have hstep := rsqrtss_xmm_m32_step s h hpre.sse hpre.sse.feature [r.prefixByte, 0xF3, rex]
    (scanPrefix_seg_cons r (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.repRex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.read)
    (by rw [hsc, segAddr_withSeg]; exact hok)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (repRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (repRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem rsqrtss_xmm_m32_rex_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (NumPre (fun s => SseLoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (6 + am.tail.length))) 4 s ∧ r.Ready base s)
        (rsqrtssXmmM32SegOk p (6 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (r.prefixByte :: 0xF3 :: rex :: 0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (Effect.post (rsqrtssXmmM32SegEffect p (6 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [rsqrtssXmmM32SegEffect_components]; simp [Component.Covers]) _)
    (rsqrtss_xmm_m32_rex_seg_effect_step p r base rex hr reg am hv hx hb)

theorem rsqrtss_xmm_m32_a32_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (NumPre (SseLoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4)
        (rsqrtssXmmM32A32Ok p (5 + am.tail.length) (gprNumber 0 0 reg) am))
      (codeRange p (0x67 :: 0xF3 :: 0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (rsqrtssXmmM32A32Effect p (5 + am.tail.length)
        (gprNumber 0 0 reg) am) := by
  intro s h hcode ⟨hpre, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0xF3] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) := by
    rw [scanContext_asz_cons]
  have hstep := rsqrtss_xmm_m32_a32_step s h hpre.sse hpre.sse.feature [0x67, 0xF3]
    (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rep _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.read)
    (by rw [hsc]; exact hok)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0xF3])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0xF3])).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem rsqrtss_xmm_m32_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (NumPre (SseLoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4)
        (rsqrtssXmmM32A32Ok p (5 + am.tail.length) (gprNumber 0 0 reg) am))
      (codeRange p (0x67 :: 0xF3 :: 0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (Effect.post (rsqrtssXmmM32A32Effect p (5 + am.tail.length)
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [rsqrtssXmmM32A32Effect_components]; simp [Component.Covers]) _)
    (rsqrtss_xmm_m32_a32_effect_step p reg am hv hx hb)

theorem rsqrtss_xmm_m32_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (NumPre (SseLoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 4)
        (rsqrtssXmmM32A32Ok p (6 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (0x67 :: 0xF3 :: rex :: 0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (rsqrtssXmmM32A32Effect p (6 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode ⟨hpre, hok⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0xF3, rex] =
      withAsz (repRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_f3_rex s.DS (PrefixSegments.ofState s) hr]
  have hstep := rsqrtss_xmm_m32_a32_step s h hpre.sse hpre.sse.feature [0x67, 0xF3, rex]
    (scanPrefix_asz_cons (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.repRex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.read)
    (by rw [hsc]; exact hok)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (repRexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (repRexContext s.DS rex.toBitVec)).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem rsqrtss_xmm_m32_rex_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (NumPre (SseLoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 4)
        (rsqrtssXmmM32A32Ok p (6 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am))
      (codeRange p (0x67 :: 0xF3 :: rex :: 0x0F :: 0x52 :: am.modrm reg :: am.tail))
      (Effect.post (rsqrtssXmmM32A32Effect p (6 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [rsqrtssXmmM32A32Effect_components]; simp [Component.Covers]) _)
    (rsqrtss_xmm_m32_rex_a32_effect_step p rex hr reg am hv hx hb)

theorem rsqrtss_xmm_m32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (NumPre (SseLoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeRsqrtssXmmM32 dst am).length)) 4)
        (rsqrtssXmmM32Ok p (encodeRsqrtssXmmM32 dst am).length (dst.setWidth 5) am))
      (codeRange p (encodeRsqrtssXmmM32 dst am))
      (Effect.post (rsqrtssXmmM32Effect p (encodeRsqrtssXmmM32 dst am).length
        (dst.setWidth 5) am)) := by
  unfold encodeRsqrtssXmmM32
  rcases encodeSseMem_spec 0x52 dst am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (0xF3 :: 0x0F :: 0x52 :: am.modrm (regLow dst) :: am.tail :
        List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact rsqrtss_xmm_m32_triple_of_bytes p (regLow dst) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := rsqrtss_xmm_m32_rex_triple_of_bytes p _ hrex.rexPrefix (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (0xF3 :: am.rexByte false dst :: 0x0F :: 0x52 :: am.modrm (regLow dst) ::
        am.tail).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact this

theorem rsqrtss_xmm_m32_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (NumPre (SseLoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeRsqrtssXmmM32 dst am).length)) 4)
        (rsqrtssXmmM32A32Ok p (0x67 :: encodeRsqrtssXmmM32 dst am).length (dst.setWidth 5) am))
      (codeRange p (0x67 :: encodeRsqrtssXmmM32 dst am))
      (Effect.post (rsqrtssXmmM32A32Effect p (0x67 :: encodeRsqrtssXmmM32 dst am).length
        (dst.setWidth 5) am)) := by
  unfold encodeRsqrtssXmmM32
  rcases encodeSseMem_spec 0x52 dst am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (0x67 :: 0xF3 :: 0x0F :: 0x52 :: am.modrm (regLow dst) :: am.tail :
        List UInt8).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact rsqrtss_xmm_m32_a32_triple_of_bytes p (regLow dst) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := rsqrtss_xmm_m32_rex_a32_triple_of_bytes p _ hrex.rexPrefix (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (0x67 :: 0xF3 :: am.rexByte false dst :: 0x0F :: 0x52 :: am.modrm (regLow dst) ::
        am.tail).length = 6 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact this

theorem rsqrtss_xmm_m32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple
      (NumPre (fun s => SseLoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeRsqrtssXmmM32 dst am).length)) 4 s ∧ r.Ready base s)
        (rsqrtssXmmM32SegOk p (r.prefixByte :: encodeRsqrtssXmmM32 dst am).length base (dst.setWidth 5) am))
      (codeRange p (r.prefixByte :: encodeRsqrtssXmmM32 dst am))
      (Effect.post (rsqrtssXmmM32SegEffect p (r.prefixByte :: encodeRsqrtssXmmM32 dst am).length base
        (dst.setWidth 5) am)) := by
  unfold encodeRsqrtssXmmM32
  rcases encodeSseMem_spec 0x52 dst am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (r.prefixByte :: 0xF3 :: 0x0F :: 0x52 :: am.modrm (regLow dst) ::
        am.tail : List UInt8).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact rsqrtss_xmm_m32_seg_triple_of_bytes p r base (regLow dst) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := rsqrtss_xmm_m32_rex_seg_triple_of_bytes p r base _
      hrex.rexPrefix (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (r.prefixByte :: 0xF3 :: am.rexByte false dst :: 0x0F :: 0x52 ::
        am.modrm (regLow dst) :: am.tail).length = 6 + am.tail.length := by
      simp; omega
    rw [hbytes, hl]
    exact this

attribute [x86_compose] rsqrtssXmmM32Effect

@[x86_local] theorem rsqrtssXmmM32Effect_local [Bindings] {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (rsqrtssXmmM32Effect p len dst am) := by
  effect_local [rsqrtssXmmM32Effect]

attribute [x86_compose] rsqrtssXmmM32SegEffect

@[x86_local] theorem rsqrtssXmmM32SegEffect_local [Bindings] {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (rsqrtssXmmM32SegEffect p len base dst am) := by
  effect_local [rsqrtssXmmM32SegEffect]

attribute [x86_compose] rsqrtssXmmM32A32Effect

@[x86_local] theorem rsqrtssXmmM32A32Effect_local [Bindings] {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (rsqrtssXmmM32A32Effect p len dst am) := by
  effect_local [rsqrtssXmmM32A32Effect]

end X86Proofs
