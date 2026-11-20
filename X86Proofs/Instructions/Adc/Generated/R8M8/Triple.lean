import X86Proofs.Instructions.Adc.Generated.R8M8.Step
import X86Proofs.Instructions.Adc.Generated.R8M8.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def adcR8M8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (c : Bool) (s : RamState) :
    Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (a + b + BitVec.ofNat 8 c.toNat) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR8M8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (c : Bool) (s : RamState) : (adcR8M8Effect p len dst am c s).components = [.reg dst, .flags, .rip] := rfl

theorem adc_r8_m8_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (2 + am.tail.length))) 1 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x12 :: am.modrm reg :: am.tail))
      (adcR8M8Effect p (2 + am.tail.length) (gprNumber 0 0 reg) am c) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := adc_r8_m8_step s h [] (by simp) (by simp)
    (by rfl) (by rfl)
    (by rfl) reg
    (.inr (by exact gprNumber_low4 reg hreg)) am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r8_m8_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (2 + am.tail.length))) 1 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x12 :: am.modrm reg :: am.tail))
      (Effect.post (adcR8M8Effect p (2 + am.tail.length) (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR8M8Effect_components]; simp [Component.Covers]) _)
    (adc_r8_m8_effect_step p reg hreg am hv hx hb c)

theorem adc_r8_m8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (3 + am.tail.length))) 1 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x12 :: am.modrm reg :: am.tail))
      (adcR8M8Effect p (3 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := adc_r8_m8_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg
    (.inl (by rw [scanContext_rex _ _ hr]; rfl)) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r8_m8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (3 + am.tail.length))) 1 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x12 :: am.modrm reg :: am.tail))
      (Effect.post (adcR8M8Effect p (3 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR8M8Effect_components]; simp [Component.Covers]) _)
    (adc_r8_m8_rex_effect_step p rex hr reg am hv hx hb c)

theorem adc_r8_m8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (encodeAdcR8M8 dst am).length)) 1 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcR8M8 dst am))
      (Effect.post (adcR8M8Effect p (encodeAdcR8M8 dst am).length (dst.setWidth 5) am c)) := by
  unfold encodeAdcR8M8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec dst hs
    have := adc_r8_m8_triple_of_bytes p (regLow dst) hl am hv hx hb c
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 = 2 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := adc_r8_m8_rex_triple_of_bytes p _ hrex.rexPrefix (regLow dst) am hv hx hb c
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]

attribute [x86_compose] adcR8M8Effect

@[x86_local] theorem adcR8M8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {am : AddrMode}
    {c : Bool} :
    Effect.Local (adcR8M8Effect p len dst am c) := by
  effect_local [adcR8M8Effect]

def adcR8M8SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (c : Bool) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (a + b + BitVec.ofNat 8 c.toNat) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR8M8SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (c : Bool) (s : RamState) :
    (adcR8M8SegEffect p len base dst am c s).components =
      [.reg dst, .flags, .rip] := rfl

theorem adc_r8_m8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => SegLoadPre p r base
        (fun u => am.addr u (p + BitVec.ofNat 64 (3 + am.tail.length))) 1 s ∧
        (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: 0x12 :: am.modrm reg :: am.tail))
      (adcR8M8SegEffect p (3 + am.tail.length) base (gprNumber 0 0 reg) am c) := by
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, hc⟩
  subst hp hbase
  subst hc
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := adc_r8_m8_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inr (by rw [hsc]; exact gprNumber_low4 reg hreg)) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r8_m8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => SegLoadPre p r base
        (fun u => am.addr u (p + BitVec.ofNat 64 (3 + am.tail.length))) 1 s ∧
        (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: 0x12 :: am.modrm reg :: am.tail))
      (Effect.post (adcR8M8SegEffect p (3 + am.tail.length) base (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR8M8SegEffect_components]; simp [Component.Covers]) _)
    (adc_r8_m8_seg_effect_step p r base reg hreg am hv hx hb c)

theorem adc_r8_m8_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => SegLoadPre p r base
        (fun u => am.addr u (p + BitVec.ofNat 64 (4 + am.tail.length))) 1 s ∧
        (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: rex :: 0x12 :: am.modrm reg :: am.tail))
      (adcR8M8SegEffect p (4 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, hc⟩
  subst hp hbase
  subst hc
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := adc_r8_m8_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inl (by rw [hsc]; rfl)) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r8_m8_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => SegLoadPre p r base
        (fun u => am.addr u (p + BitVec.ofNat 64 (4 + am.tail.length))) 1 s ∧
        (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: rex :: 0x12 :: am.modrm reg :: am.tail))
      (Effect.post (adcR8M8SegEffect p (4 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR8M8SegEffect_components]; simp [Component.Covers]) _)
    (adc_r8_m8_rex_seg_effect_step p r base rex hr reg am hv hx hb c)

theorem adc_r8_m8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s => SegLoadPre p r base
        (fun u => am.addr u (p + BitVec.ofNat 64 (r.prefixByte :: encodeAdcR8M8 dst am).length)) 1 s ∧
        (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: encodeAdcR8M8 dst am))
      (Effect.post (adcR8M8SegEffect p (r.prefixByte :: encodeAdcR8M8 dst am).length base (dst.setWidth 5) am c)) := by
  unfold encodeAdcR8M8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec dst hs
    have := adc_r8_m8_seg_triple_of_bytes p r base (regLow dst) hl am hv hx hb c
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := adc_r8_m8_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix (regLow dst) am hv
      hx hb c
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

attribute [x86_compose] adcR8M8SegEffect

@[x86_local] theorem adcR8M8SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} {c : Bool} :
    Effect.Local (adcR8M8SegEffect p len base dst am c) := by
  effect_local [adcR8M8SegEffect]

def adcR8M8NoRexEffect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (am : AddrMode) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.byteReg dst).read s
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (byteRegGpr dst) : Operand 64),
      mergeByteReg dst (a + b + BitVec.ofNat 8 c.toNat) ((Operand.reg (byteRegGpr dst) : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR8M8NoRexEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (am : AddrMode) (c : Bool) (s : RamState) :
    (adcR8M8NoRexEffect p len dst am c s).components =
      [.reg (byteRegGpr dst), .flags, .rip] := rfl

def adcR8M8NoRexSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 3) (am : AddrMode) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.byteReg dst).read s
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (byteRegGpr dst) : Operand 64),
      mergeByteReg dst (a + b + BitVec.ofNat 8 c.toNat) ((Operand.reg (byteRegGpr dst) : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR8M8NoRexSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 3)
    (am : AddrMode) (c : Bool) (s : RamState) :
    (adcR8M8NoRexSegEffect p len base dst am c s).components =
      [.reg (byteRegGpr dst), .flags, .rip] := rfl

def adcR8M8NoRexA32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (am : AddrMode) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.byteReg dst).read s
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (byteRegGpr dst) : Operand 64),
      mergeByteReg dst (a + b + BitVec.ofNat 8 c.toNat) ((Operand.reg (byteRegGpr dst) : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR8M8NoRexA32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (am : AddrMode) (c : Bool) (s : RamState) :
    (adcR8M8NoRexA32Effect p len dst am c s).components =
      [.reg (byteRegGpr dst), .flags, .rip] := rfl

theorem adc_r8_m8_norex_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (2 + am.tail.length))) 1 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x12 :: am.modrm reg :: am.tail))
      (adcR8M8NoRexEffect p (2 + am.tail.length) reg am c) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := adc_r8_m8_gpr8_step s h [] (by simp) (by simp)
    (by rfl) (by rfl)
    (by rfl) reg am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  have hdst : Operand.gpr8 (gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 reg)
      (byteRex (scanContext s.DS (PrefixSegments.ofState s) [])) = Operand.byteReg reg := rfl
  rw [hdst] at hstep
  simp only [writeOutputs_byteReg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_RFLAGS,
      beforeFetch_RFLAGS]
    exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r8_m8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (2 + am.tail.length))) 1 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x12 :: am.modrm reg :: am.tail))
      (Effect.post (adcR8M8NoRexEffect p (2 + am.tail.length) reg am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR8M8NoRexEffect_components]; simp [Component.Covers]) _)
    (adc_r8_m8_norex_effect_step p reg am hv hx hb c)

theorem adc_r8_m8_norex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => SegLoadPre p r base
        (fun u => am.addr u (p + BitVec.ofNat 64 (3 + am.tail.length))) 1 s ∧
        (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: 0x12 :: am.modrm reg :: am.tail))
      (adcR8M8NoRexSegEffect p (3 + am.tail.length) base reg am c) := by
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, hc⟩
  subst hp hbase
  subst hc
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := adc_r8_m8_gpr8_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : Operand.gpr8 (gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r3 reg)
      (byteRex (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)))) = Operand.byteReg reg := rfl
  rw [hdst] at hstep
  simp only [writeOutputs_byteReg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_RFLAGS,
      beforeFetch_RFLAGS]
    exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r8_m8_norex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => SegLoadPre p r base
        (fun u => am.addr u (p + BitVec.ofNat 64 (3 + am.tail.length))) 1 s ∧
        (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: 0x12 :: am.modrm reg :: am.tail))
      (Effect.post (adcR8M8NoRexSegEffect p (3 + am.tail.length) base reg am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR8M8NoRexSegEffect_components]; simp [Component.Covers]) _)
    (adc_r8_m8_norex_seg_effect_step p r base reg am hv hx hb c)

theorem adc_r8_m8_norex_a32_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (3 + am.tail.length))) 1 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: 0x12 :: am.modrm reg :: am.tail))
      (adcR8M8NoRexA32Effect p (3 + am.tail.length) reg am c) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := adc_r8_m8_gpr8_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hdst : Operand.gpr8 (gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r3 reg)
      (byteRex (withAsz (scanContext s.DS (PrefixSegments.ofState s) []))) = Operand.byteReg reg := rfl
  rw [hdst] at hstep
  simp only [writeOutputs_byteReg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_RFLAGS,
      beforeFetch_RFLAGS]
    exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r8_m8_norex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (3 + am.tail.length))) 1 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: 0x12 :: am.modrm reg :: am.tail))
      (Effect.post (adcR8M8NoRexA32Effect p (3 + am.tail.length) reg am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR8M8NoRexA32Effect_components]; simp [Component.Covers]) _)
    (adc_r8_m8_norex_a32_effect_step p reg am hv hx hb c)

theorem adc_r8_m8_norex_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (2 + am.tail.length))) 1 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcR8M8NoRex dst am))
      (Effect.post (adcR8M8NoRexEffect p (2 + am.tail.length) dst am c)) :=
  adc_r8_m8_norex_triple_of_bytes p dst am hv hx hb c

theorem adc_r8_m8_norex_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => SegLoadPre p r base
        (fun u => am.addr u (p + BitVec.ofNat 64 (3 + am.tail.length))) 1 s ∧
        (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: encodeAdcR8M8NoRex dst am))
      (Effect.post (adcR8M8NoRexSegEffect p (3 + am.tail.length) base dst am c)) :=
  adc_r8_m8_norex_seg_triple_of_bytes p r base dst am hv hx hb c

theorem adc_r8_m8_norex_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (3 + am.tail.length))) 1 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: encodeAdcR8M8NoRex dst am))
      (Effect.post (adcR8M8NoRexA32Effect p (3 + am.tail.length) dst am c)) :=
  adc_r8_m8_norex_a32_triple_of_bytes p dst am hv hx hb c

attribute [x86_compose] adcR8M8NoRexEffect adcR8M8NoRexSegEffect adcR8M8NoRexA32Effect

@[x86_local] theorem adcR8M8NoRexEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {am : AddrMode} {c : Bool} : Effect.Local (adcR8M8NoRexEffect p len dst am c) := by
  effect_local [adcR8M8NoRexEffect]

@[x86_local] theorem adcR8M8NoRexSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 3} {am : AddrMode} {c : Bool} :
    Effect.Local (adcR8M8NoRexSegEffect p len base dst am c) := by
  effect_local [adcR8M8NoRexSegEffect]

@[x86_local] theorem adcR8M8NoRexA32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {am : AddrMode} {c : Bool} : Effect.Local (adcR8M8NoRexA32Effect p len dst am c) := by
  effect_local [adcR8M8NoRexA32Effect]

def adcR8M8A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (a + b + BitVec.ofNat 8 c.toNat) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR8M8A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (c : Bool) (s : RamState) :
    (adcR8M8A32Effect p len dst am c s).components = [.reg dst, .flags, .rip] := rfl

theorem adc_r8_m8_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (3 + am.tail.length))) 1 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: 0x12 :: am.modrm reg :: am.tail))
      (adcR8M8A32Effect p (3 + am.tail.length) (gprNumber 0 0 reg) am c) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := adc_r8_m8_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inr (by rw [hsc]; exact gprNumber_low4 reg hreg)) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r8_m8_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (3 + am.tail.length))) 1 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: 0x12 :: am.modrm reg :: am.tail))
      (Effect.post (adcR8M8A32Effect p (3 + am.tail.length) (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR8M8A32Effect_components]; simp [Component.Covers]) _)
    (adc_r8_m8_a32_effect_step p reg hreg am hv hx hb c)

theorem adc_r8_m8_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (4 + am.tail.length))) 1 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: rex :: 0x12 :: am.modrm reg :: am.tail))
      (adcR8M8A32Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := adc_r8_m8_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inl (by rw [hsc]; rfl)) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (rexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (rexContext s.DS rex.toBitVec)).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r8_m8_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (4 + am.tail.length))) 1 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: rex :: 0x12 :: am.modrm reg :: am.tail))
      (Effect.post (adcR8M8A32Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR8M8A32Effect_components]; simp [Component.Covers]) _)
    (adc_r8_m8_rex_a32_effect_step p rex hr reg am hv hx hb c)

theorem adc_r8_m8_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (0x67 :: encodeAdcR8M8 dst am).length)) 1 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: encodeAdcR8M8 dst am))
      (Effect.post (adcR8M8A32Effect p (0x67 :: encodeAdcR8M8 dst am).length (dst.setWidth 5) am c)) := by
  unfold encodeAdcR8M8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec dst hs
    have := adc_r8_m8_a32_triple_of_bytes p (regLow dst) hl am hv hx hb c
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := adc_r8_m8_rex_a32_triple_of_bytes p _ hrex.rexPrefix (regLow dst) am hv hx
      hb c
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

attribute [x86_compose] adcR8M8A32Effect

@[x86_local] theorem adcR8M8A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} {c : Bool} :
    Effect.Local (adcR8M8A32Effect p len dst am c) := by
  effect_local [adcR8M8A32Effect]

end X86Proofs
