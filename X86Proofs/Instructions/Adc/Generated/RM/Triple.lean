import X86Proofs.Instructions.Adc.Generated.RM.Step
import X86Proofs.Instructions.Adc.Generated.RM.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def adcR64M64Effect (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (c : Bool) (s : RamState) :
    Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 (movLoadLen am)
    writes := [⟨(Operand.reg dst : Operand 64), a + b + BitVec.ofNat 64 c.toNat⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR64M64Effect_components (p : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (c : Bool) (s : RamState) : (adcR64M64Effect p dst am c s).components = [.reg dst, .flags, .rip] := rfl

def adcR32M32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (c : Bool) (s : RamState) :
    Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (a + b + BitVec.ofNat 32 c.toNat).setWidth 64⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR32M32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (c : Bool) (s : RamState) : (adcR32M32Effect p len dst am c s).components = [.reg dst, .flags, .rip] := rfl

def adcR16M16Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (c : Bool) (s : RamState) :
    Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (a + b + BitVec.ofNat 16 c.toNat) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR16M16Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (c : Bool) (s : RamState) : (adcR16M16Effect p len dst am c s).components = [.reg dst, .flags, .rip] := rfl

theorem adc_r64_m64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (movLoadLen am))) 8 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x13 :: am.modrm reg :: am.tail))
      (adcR64M64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := adc_r_m_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
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
    simp only [Operand.read_writeOutputs_self, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r64_m64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (movLoadLen am))) 8 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x13 :: am.modrm reg :: am.tail))
      (Effect.post (adcR64M64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR64M64Effect_components]; simp [Component.Covers]) _)
    (adc_r64_m64_effect_step p rex hrex reg am hv hx hb c)

theorem adc_r32_m32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (2 + am.tail.length))) 4 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x13 :: am.modrm reg :: am.tail))
      (adcR32M32Effect p (2 + am.tail.length) (gprNumber 0 0 reg) am c) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := adc_r_m_step s h [] (by simp) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) reg am hv
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
    simp only [Operand.read_writeOutputs_self32, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r32_m32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (2 + am.tail.length))) 4 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x13 :: am.modrm reg :: am.tail))
      (Effect.post (adcR32M32Effect p (2 + am.tail.length) (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR32M32Effect_components]; simp [Component.Covers]) _)
    (adc_r32_m32_effect_step p reg am hv hx hb c)

theorem adc_r32_m32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (3 + am.tail.length))) 4 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x13 :: am.modrm reg :: am.tail))
      (adcR32M32Effect p (3 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := adc_r_m_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
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
    simp only [Operand.read_writeOutputs_self32, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r32_m32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (3 + am.tail.length))) 4 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x13 :: am.modrm reg :: am.tail))
      (Effect.post (adcR32M32Effect p (3 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR32M32Effect_components]; simp [Component.Covers]) _)
    (adc_r32_m32_rex_effect_step p rex hrex reg am hv hx hb c)

theorem adc_r16_m16_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x66 :: 0x13 :: am.modrm reg :: am.tail))
      (adcR16M16Effect p (3 + am.tail.length) (gprNumber 0 0 reg) am c) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := adc_r16_m16_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) reg am hv
    (by exact (AddrContext.osz _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r3 reg = (gprNumber 0 0 reg) := rfl
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

theorem adc_r16_m16_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x66 :: 0x13 :: am.modrm reg :: am.tail))
      (Effect.post (adcR16M16Effect p (3 + am.tail.length) (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR16M16Effect_components]; simp [Component.Covers]) _)
    (adc_r16_m16_effect_step p reg am hv hx hb c)

theorem adc_r16_m16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x66 :: rex :: 0x13 :: am.modrm reg :: am.tail))
      (adcR16M16Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := adc_r16_m16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_66_rex _ _ hr]; exact (AddrContext.oszRex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_66_rex _ _ hr]; exact hread)
  simp only [scanContext_66_rex _ _ hr] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_r4
      (oszRexContext s.DS rex.toBitVec).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
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

theorem adc_r16_m16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x66 :: rex :: 0x13 :: am.modrm reg :: am.tail))
      (Effect.post (adcR16M16Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR16M16Effect_components]; simp [Component.Covers]) _)
    (adc_r16_m16_rex_effect_step p rex hrex reg am hv hx hb c)

theorem adc_r64_m64_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (movLoadLen am))) 8 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcR64M64 dst am))
      (Effect.post (adcR64M64Effect p (dst.setWidth 5) am c)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := adc_r64_m64_triple_of_bytes p _ hrex (regLow dst) am hv hx hb c
  rwa [hr, gprNumber_reg] at this

theorem adc_r32_m32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (encodeAdcR32M32 dst am).length)) 4 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcR32M32 dst am))
      (Effect.post (adcR32M32Effect p (encodeAdcR32M32 dst am).length (dst.setWidth 5) am c)) := by
  unfold encodeAdcR32M32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := adc_r32_m32_triple_of_bytes p (regLow dst) am hv hx hb c
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 = 2 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := adc_r32_m32_rex_triple_of_bytes p _ hrex (regLow dst) am hv hx hb c
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]

theorem adc_r16_m16_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (encodeAdcR16M16 dst am).length)) 2 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcR16M16 dst am))
      (Effect.post (adcR16M16Effect p (encodeAdcR16M16 dst am).length (dst.setWidth 5) am c)) := by
  unfold encodeAdcR16M16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := adc_r16_m16_triple_of_bytes p (regLow dst) am hv hx hb c
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := adc_r16_m16_rex_triple_of_bytes p _ hrex (regLow dst) am hv hx hb c
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

attribute [x86_compose] adcR64M64Effect adcR32M32Effect adcR16M16Effect

@[x86_local] theorem adcR64M64Effect_local {p : BitVec 64} {dst : BitVec 5} {am : AddrMode}
    {c : Bool} :
    Effect.Local (adcR64M64Effect p dst am c) := by
  effect_local [adcR64M64Effect]

@[x86_local] theorem adcR32M32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {am : AddrMode}
    {c : Bool} :
    Effect.Local (adcR32M32Effect p len dst am c) := by
  effect_local [adcR32M32Effect]

@[x86_local] theorem adcR16M16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {am : AddrMode}
    {c : Bool} :
    Effect.Local (adcR16M16Effect p len dst am c) := by
  effect_local [adcR16M16Effect]

def adcR64M64SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (c : Bool) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), a + b + BitVec.ofNat 64 c.toNat⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR64M64SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (c : Bool) (s : RamState) :
    (adcR64M64SegEffect p len base dst am c s).components =
      [.reg dst, .flags, .rip] := rfl

theorem adc_r64_m64_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => SegLoadPre p r base
        (fun u => am.addr u (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧
        (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: rex :: 0x13 :: am.modrm reg :: am.tail))
      (adcR64M64SegEffect p (4 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg)
        am c) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, hc⟩
  subst hp hbase
  subst hc
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := adc_r_m_step s h [r.prefixByte, rex] (by simp [r.scanPrefix, hr.scanPrefix])
    (by simp) 64 (.inl rfl)
    (by rw [scanContext_seg_rex _ _ r hr]; exact hrex.operand_size_seg _ _)
    (by rw [scanContext_seg_rex _ _ r hr]; rfl) (by rw [scanContext_seg_rex _ _ r hr]; rfl)
    (by rw [scanContext_seg_rex _ _ r hr]; rfl) reg am hv
    (by rw [scanContext_seg_rex _ _ r hr]; exact SegAddrContext.seg_rex _ _ hseg _ am hx hb)
    hcode.bytesAt hlow (by rw [scanContext_seg_rex _ _ r hr, segAddr_segRexContext]; exact hread)
  simp only [scanContext_seg_rex _ _ r hr, segAddr_segRexContext] at hstep
  have hdst : gprNumber (segRexContext s.DS (r.select (PrefixSegments.ofState s)) rex.toBitVec).rex_r4
      (segRexContext s.DS (r.select (PrefixSegments.ofState s)) rex.toBitVec).rex_r3 reg =
      gprNumber 0 (rexR rex.toBitVec) reg := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r64_m64_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => SegLoadPre p r base
        (fun u => am.addr u (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧
        (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: rex :: 0x13 :: am.modrm reg :: am.tail))
      (Effect.post (adcR64M64SegEffect p (4 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR64M64SegEffect_components]; simp [Component.Covers]) _)
    (adc_r64_m64_seg_effect_step p r base rex hrex reg am hv hx hb c)

theorem adc_r64_m64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s => SegLoadPre p r base
        (fun u => am.addr u (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧
        (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: encodeAdcR64M64 dst am))
      (Effect.post (adcR64M64SegEffect p (4 + am.tail.length) base (dst.setWidth 5) am c)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := adc_r64_m64_seg_triple_of_bytes p r base _ hrex (regLow dst) am hv hx hb c
  rwa [hr, gprNumber_reg] at this

attribute [x86_compose] adcR64M64SegEffect

@[x86_local] theorem adcR64M64SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} {c : Bool} :
    Effect.Local (adcR64M64SegEffect p len base dst am c) := by
  effect_local [adcR64M64SegEffect]

def adcR32M32SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (c : Bool) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (a + b + BitVec.ofNat 32 c.toNat).setWidth 64⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR32M32SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (c : Bool) (s : RamState) :
    (adcR32M32SegEffect p len base dst am c s).components =
      [.reg dst, .flags, .rip] := rfl

def adcR16M16SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (c : Bool) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (a + b + BitVec.ofNat 16 c.toNat) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR16M16SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (c : Bool) (s : RamState) :
    (adcR16M16SegEffect p len base dst am c s).components =
      [.reg dst, .flags, .rip] := rfl

theorem adc_r32_m32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => SegLoadPre p r base
        (fun u => am.addr u (p + BitVec.ofNat 64 (3 + am.tail.length))) 4 s ∧
        (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: 0x13 :: am.modrm reg :: am.tail))
      (adcR32M32SegEffect p (3 + am.tail.length) base (gprNumber 0 0 reg) am c) := by
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
  have hstep := adc_r_m_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
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
    simp only [Operand.read_writeOutputs_self32, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r32_m32_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => SegLoadPre p r base
        (fun u => am.addr u (p + BitVec.ofNat 64 (3 + am.tail.length))) 4 s ∧
        (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: 0x13 :: am.modrm reg :: am.tail))
      (Effect.post (adcR32M32SegEffect p (3 + am.tail.length) base (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR32M32SegEffect_components]; simp [Component.Covers]) _)
    (adc_r32_m32_seg_effect_step p r base reg am hv hx hb c)

theorem adc_r32_m32_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => SegLoadPre p r base
        (fun u => am.addr u (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧
        (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: rex :: 0x13 :: am.modrm reg :: am.tail))
      (adcR32M32SegEffect p (4 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  have hr := hrex.rexPrefix
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
  have hstep := adc_r_m_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
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
    simp only [Operand.read_writeOutputs_self32, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r32_m32_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => SegLoadPre p r base
        (fun u => am.addr u (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧
        (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: rex :: 0x13 :: am.modrm reg :: am.tail))
      (Effect.post (adcR32M32SegEffect p (4 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR32M32SegEffect_components]; simp [Component.Covers]) _)
    (adc_r32_m32_rex_seg_effect_step p r base rex hrex reg am hv hx hb c)

theorem adc_r16_m16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => SegLoadPre p r base
        (fun u => am.addr u (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
        (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: 0x66 :: 0x13 :: am.modrm reg :: am.tail))
      (adcR16M16SegEffect p (4 + am.tail.length) base (gprNumber 0 0 reg) am c) := by
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, hc⟩
  subst hp hbase
  subst hc
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66]
      (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := adc_r16_m16_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s))).rex_r3 reg = (gprNumber 0 0 reg) := rfl
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

theorem adc_r16_m16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => SegLoadPre p r base
        (fun u => am.addr u (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
        (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: 0x66 :: 0x13 :: am.modrm reg :: am.tail))
      (Effect.post (adcR16M16SegEffect p (4 + am.tail.length) base (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR16M16SegEffect_components]; simp [Component.Covers]) _)
    (adc_r16_m16_seg_effect_step p r base reg am hv hx hb c)

theorem adc_r16_m16_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => SegLoadPre p r base
        (fun u => am.addr u (p + BitVec.ofNat 64 (5 + am.tail.length))) 2 s ∧
        (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x13 :: am.modrm reg :: am.tail))
      (adcR16M16SegEffect p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, hc⟩
  subst hp hbase
  subst hc
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66, rex] =
      withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66, rex]
      (noSegPrefix_cons noSegPrefix_66 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_66_rex _ _ hr]
  have hstep := adc_r16_m16_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
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

theorem adc_r16_m16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => SegLoadPre p r base
        (fun u => am.addr u (p + BitVec.ofNat 64 (5 + am.tail.length))) 2 s ∧
        (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x13 :: am.modrm reg :: am.tail))
      (Effect.post (adcR16M16SegEffect p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR16M16SegEffect_components]; simp [Component.Covers]) _)
    (adc_r16_m16_rex_seg_effect_step p r base rex hrex reg am hv hx hb c)

theorem adc_r32_m32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s => SegLoadPre p r base
        (fun u => am.addr u (p + BitVec.ofNat 64 (r.prefixByte :: encodeAdcR32M32 dst am).length)) 4 s ∧
        (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: encodeAdcR32M32 dst am))
      (Effect.post (adcR32M32SegEffect p (r.prefixByte :: encodeAdcR32M32 dst am).length base (dst.setWidth 5) am c)) := by
  unfold encodeAdcR32M32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := adc_r32_m32_seg_triple_of_bytes p r base (regLow dst) am hv hx hb c
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := adc_r32_m32_rex_seg_triple_of_bytes p r base _ hrex (regLow dst) am hv
      hx hb c
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem adc_r16_m16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s => SegLoadPre p r base
        (fun u => am.addr u (p + BitVec.ofNat 64 (r.prefixByte :: encodeAdcR16M16 dst am).length)) 2 s ∧
        (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: encodeAdcR16M16 dst am))
      (Effect.post (adcR16M16SegEffect p (r.prefixByte :: encodeAdcR16M16 dst am).length base (dst.setWidth 5) am c)) := by
  unfold encodeAdcR16M16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := adc_r16_m16_seg_triple_of_bytes p r base (regLow dst) am hv hx hb c
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := adc_r16_m16_rex_seg_triple_of_bytes p r base _ hrex (regLow dst) am hv
      hx hb c
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

attribute [x86_compose] adcR32M32SegEffect

@[x86_local] theorem adcR32M32SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} {c : Bool} :
    Effect.Local (adcR32M32SegEffect p len base dst am c) := by
  effect_local [adcR32M32SegEffect]

attribute [x86_compose] adcR16M16SegEffect

@[x86_local] theorem adcR16M16SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} {c : Bool} :
    Effect.Local (adcR16M16SegEffect p len base dst am c) := by
  effect_local [adcR16M16SegEffect]

def adcR64M64A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), a + b + BitVec.ofNat 64 c.toNat⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR64M64A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (c : Bool) (s : RamState) :
    (adcR64M64A32Effect p len dst am c s).components = [.reg dst, .flags, .rip] := rfl

def adcR32M32A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (a + b + BitVec.ofNat 32 c.toNat).setWidth 64⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR32M32A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (c : Bool) (s : RamState) :
    (adcR32M32A32Effect p len dst am c s).components = [.reg dst, .flags, .rip] := rfl

def adcR16M16A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (a + b + BitVec.ofNat 16 c.toNat) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (adcSpec c a b).2) }

@[simp] theorem adcR16M16A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (c : Bool) (s : RamState) :
    (adcR16M16A32Effect p len dst am c s).components = [.reg dst, .flags, .rip] := rfl

theorem adc_r64_m64_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: rex :: 0x13 :: am.modrm reg :: am.tail))
      (adcR64M64A32Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  have hr := hrex.rexPrefix
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
  have hstep := adc_r_m_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
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
    simp only [Operand.read_writeOutputs_self, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r64_m64_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: rex :: 0x13 :: am.modrm reg :: am.tail))
      (Effect.post (adcR64M64A32Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR64M64A32Effect_components]; simp [Component.Covers]) _)
    (adc_r64_m64_a32_effect_step p rex hrex reg am hv hx hb c)

theorem adc_r32_m32_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (3 + am.tail.length))) 4 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: 0x13 :: am.modrm reg :: am.tail))
      (adcR32M32A32Effect p (3 + am.tail.length) (gprNumber 0 0 reg) am c) := by
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
  have hstep := adc_r_m_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
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
    simp only [Operand.read_writeOutputs_self32, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r32_m32_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (3 + am.tail.length))) 4 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: 0x13 :: am.modrm reg :: am.tail))
      (Effect.post (adcR32M32A32Effect p (3 + am.tail.length) (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR32M32A32Effect_components]; simp [Component.Covers]) _)
    (adc_r32_m32_a32_effect_step p reg am hv hx hb c)

theorem adc_r32_m32_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: rex :: 0x13 :: am.modrm reg :: am.tail))
      (adcR32M32A32Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  have hr := hrex.rexPrefix
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
  have hstep := adc_r_m_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
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
    simp only [Operand.read_writeOutputs_self32, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_r32_m32_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: rex :: 0x13 :: am.modrm reg :: am.tail))
      (Effect.post (adcR32M32A32Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR32M32A32Effect_components]; simp [Component.Covers]) _)
    (adc_r32_m32_rex_a32_effect_step p rex hrex reg am hv hx hb c)

theorem adc_r16_m16_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: 0x66 :: 0x13 :: am.modrm reg :: am.tail))
      (adcR16M16A32Effect p (4 + am.tail.length) (gprNumber 0 0 reg) am c) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66]) := by
    rw [scanContext_asz_cons]
  have hstep := adc_r16_m16_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66])).rex_r3 reg = (gprNumber 0 0 reg) := rfl
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

theorem adc_r16_m16_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: 0x66 :: 0x13 :: am.modrm reg :: am.tail))
      (Effect.post (adcR16M16A32Effect p (4 + am.tail.length) (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR16M16A32Effect_components]; simp [Component.Covers]) _)
    (adc_r16_m16_a32_effect_step p reg am hv hx hb c)

theorem adc_r16_m16_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (5 + am.tail.length))) 2 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x13 :: am.modrm reg :: am.tail))
      (adcR16M16A32Effect p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, rex] =
      withAsz (oszRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_66_rex _ _ hr]
  have hstep := adc_r16_m16_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (oszRexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (oszRexContext s.DS rex.toBitVec)).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
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

theorem adc_r16_m16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (5 + am.tail.length))) 2 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x13 :: am.modrm reg :: am.tail))
      (Effect.post (adcR16M16A32Effect p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [adcR16M16A32Effect_components]; simp [Component.Covers]) _)
    (adc_r16_m16_rex_a32_effect_step p rex hrex reg am hv hx hb c)

theorem adc_r64_m64_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (0x67 :: encodeAdcR64M64 dst am).length)) 8 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: encodeAdcR64M64 dst am))
      (Effect.post (adcR64M64A32Effect p (0x67 :: encodeAdcR64M64 dst am).length (dst.setWidth 5) am c)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := adc_r64_m64_a32_triple_of_bytes p _ hrex (regLow dst) am hv hx hb c
  rw [hr, gprNumber_reg] at this
  unfold encodeAdcR64M64
  simp only [List.length_cons]
  rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem adc_r32_m32_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (0x67 :: encodeAdcR32M32 dst am).length)) 4 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: encodeAdcR32M32 dst am))
      (Effect.post (adcR32M32A32Effect p (0x67 :: encodeAdcR32M32 dst am).length (dst.setWidth 5) am c)) := by
  unfold encodeAdcR32M32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := adc_r32_m32_a32_triple_of_bytes p (regLow dst) am hv hx hb c
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := adc_r32_m32_rex_a32_triple_of_bytes p _ hrex (regLow dst) am hv hx
      hb c
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem adc_r16_m16_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (c : Bool) :
    Triple (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (0x67 :: encodeAdcR16M16 dst am).length)) 2 s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: encodeAdcR16M16 dst am))
      (Effect.post (adcR16M16A32Effect p (0x67 :: encodeAdcR16M16 dst am).length (dst.setWidth 5) am c)) := by
  unfold encodeAdcR16M16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := adc_r16_m16_a32_triple_of_bytes p (regLow dst) am hv hx hb c
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := adc_r16_m16_rex_a32_triple_of_bytes p _ hrex (regLow dst) am hv hx
      hb c
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

attribute [x86_compose] adcR64M64A32Effect adcR32M32A32Effect adcR16M16A32Effect

@[x86_local] theorem adcR64M64A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} {c : Bool} :
    Effect.Local (adcR64M64A32Effect p len dst am c) := by
  effect_local [adcR64M64A32Effect]

@[x86_local] theorem adcR32M32A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} {c : Bool} :
    Effect.Local (adcR32M32A32Effect p len dst am c) := by
  effect_local [adcR32M32A32Effect]

@[x86_local] theorem adcR16M16A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} {c : Bool} :
    Effect.Local (adcR16M16A32Effect p len dst am c) := by
  effect_local [adcR16M16A32Effect]

end X86Proofs
