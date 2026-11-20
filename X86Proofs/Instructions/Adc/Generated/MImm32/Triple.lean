import X86Proofs.Instructions.Adc.Generated.MImm32.Step
import X86Proofs.Instructions.Adc.Generated.MImm32.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def adcMImm32Effect (p : BitVec 64) (len n : Nat) (am : AddrMode) (imm : BitVec 32) (c : Bool) (s : RamState) :
    Effect :=
  let a := am.addr s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand n).read s
  let y := imm.signExtend n
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand n), x + y + BitVec.ofNat n c.toNat⟩]
    flags := some (.ofStatusFlags (adcSpec c x y).2) }

@[simp] theorem adcMImm32Effect_components (p : BitVec 64) (len n : Nat) (am : AddrMode)
    (imm : BitVec 32) (c : Bool) (s : RamState) : (adcMImm32Effect p len n am imm c s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) (n / 8), .flags, .rip] := rfl

def adcMImm32SegEffect (p : BitVec 64) (len n : Nat) (base : BitVec 64) (am : AddrMode)
    (imm : BitVec 32) (c : Bool) (s : RamState) : Effect :=
  let a := base + am.addr s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand n).read s
  let y := imm.signExtend n
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand n), x + y + BitVec.ofNat n c.toNat⟩]
    flags := some (.ofStatusFlags (adcSpec c x y).2) }

@[simp] theorem adcMImm32SegEffect_components (p : BitVec 64) (len n : Nat) (base : BitVec 64) (am : AddrMode)
    (imm : BitVec 32) (c : Bool) (s : RamState) : (adcMImm32SegEffect p len n base am imm c s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) (n / 8), .flags, .rip] := rfl

def adcMImm32A32Effect (p : BitVec 64) (len n : Nat) (am : AddrMode) (imm : BitVec 32) (c : Bool) (s : RamState) :
    Effect :=
  let a := am.addr32 s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand n).read s
  let y := imm.signExtend n
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand n), x + y + BitVec.ofNat n c.toNat⟩]
    flags := some (.ofStatusFlags (adcSpec c x y).2) }

@[simp] theorem adcMImm32A32Effect_components (p : BitVec 64) (len n : Nat) (am : AddrMode)
    (imm : BitVec 32) (c : Bool) (s : RamState) : (adcMImm32A32Effect p len n am imm c s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) (n / 8), .flags, .rip] := rfl

def adcM16Imm16Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 16) (c : Bool) (s : RamState) :
    Effect :=
  let a := am.addr s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand 16).read s
  let y := imm.signExtend 16
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand 16), x + y + BitVec.ofNat 16 c.toNat⟩]
    flags := some (.ofStatusFlags (adcSpec c x y).2) }

@[simp] theorem adcM16Imm16Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (imm : BitVec 16) (c : Bool) (s : RamState) : (adcM16Imm16Effect p len am imm c s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) 2, .flags, .rip] := by
  simp [adcM16Imm16Effect, Effect.components]

def adcM16Imm16SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode)
    (imm : BitVec 16) (c : Bool) (s : RamState) : Effect :=
  let a := base + am.addr s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand 16).read s
  let y := imm.signExtend 16
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand 16), x + y + BitVec.ofNat 16 c.toNat⟩]
    flags := some (.ofStatusFlags (adcSpec c x y).2) }

@[simp] theorem adcM16Imm16SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode)
    (imm : BitVec 16) (c : Bool) (s : RamState) : (adcM16Imm16SegEffect p len base am imm c s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) 2, .flags, .rip] := by
  simp [adcM16Imm16SegEffect, Effect.components]

def adcM16Imm16A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 16) (c : Bool) (s : RamState) :
    Effect :=
  let a := am.addr32 s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand 16).read s
  let y := imm.signExtend 16
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand 16), x + y + BitVec.ofNat 16 c.toNat⟩]
    flags := some (.ofStatusFlags (adcSpec c x y).2) }

@[simp] theorem adcM16Imm16A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (imm : BitVec 16) (c : Bool) (s : RamState) : (adcM16Imm16A32Effect p len am imm c s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) 2, .flags, .rip] := by
  simp [adcM16Imm16A32Effect, Effect.components]

theorem adc_m64_imm32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) (c : Bool) :
    StepEffect (fun s => RmwPre p am 8 (7 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 32 imm)))
      (adcMImm32Effect p (7 + am.tail.length) 64 am imm c) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := adc_m_imm32_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_m64_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) (c : Bool) :
    Triple (fun s => RmwPre p am 8 (7 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (adcMImm32Effect p (7 + am.tail.length) 64 am imm c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [adcMImm32Effect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (adc_m64_imm32_effect_step p rex hrex am hv hx hb imm c)

theorem adc_m32_imm32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) (c : Bool) :
    StepEffect (fun s => RmwPre p am 4 (6 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x81 :: am.modrm 2 :: (am.tail ++ immBytes 32 imm)))
      (adcMImm32Effect p (6 + am.tail.length) 32 am imm c) := by
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := adc_m_imm32_step s h [] (by simp) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_m32_imm32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) (c : Bool) :
    Triple (fun s => RmwPre p am 4 (6 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x81 :: am.modrm 2 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (adcMImm32Effect p (6 + am.tail.length) 32 am imm c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [adcMImm32Effect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (adc_m32_imm32_effect_step p am hv hx hb imm c)

theorem adc_m32_imm32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) (c : Bool) :
    StepEffect (fun s => RmwPre p am 4 (7 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 32 imm)))
      (adcMImm32Effect p (7 + am.tail.length) 32 am imm c) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := adc_m_imm32_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_m32_imm32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) (c : Bool) :
    Triple (fun s => RmwPre p am 4 (7 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (adcMImm32Effect p (7 + am.tail.length) 32 am imm c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [adcMImm32Effect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (adc_m32_imm32_rex_effect_step p rex hrex am hv hx hb imm c)

theorem adc_m16_imm16_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) (c : Bool) :
    StepEffect (fun s => RmwPre p am 2 (5 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x66 :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 16 imm)))
      (adcM16Imm16Effect p (5 + am.tail.length) am imm c) := by
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := adc_m16_imm16_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.osz _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_m16_imm16_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) (c : Bool) :
    Triple (fun s => RmwPre p am 2 (5 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x66 :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 16 imm)))
      (Effect.post (adcM16Imm16Effect p (5 + am.tail.length) am imm c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [adcM16Imm16Effect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (adc_m16_imm16_effect_step p am hv hx hb imm c)

theorem adc_m16_imm16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 16) (c : Bool) :
    StepEffect (fun s => RmwPre p am 2 (6 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x66 :: rex :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 16 imm)))
      (adcM16Imm16Effect p (6 + am.tail.length) am imm c) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := adc_m16_imm16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_66_rex _ _ hr]; exact (AddrContext.oszRex _ _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_66_rex _ _ hr]; exact hread)
  simp only [scanContext_66_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_m16_imm16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 16) (c : Bool) :
    Triple (fun s => RmwPre p am 2 (6 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x66 :: rex :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 16 imm)))
      (Effect.post (adcM16Imm16Effect p (6 + am.tail.length) am imm c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [adcM16Imm16Effect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (adc_m16_imm16_rex_effect_step p rex hrex am hv hx hb imm c)

theorem adc_m64_imm32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) (c : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 8 (8 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: rex :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 32 imm)))
      (adcMImm32SegEffect p (8 + am.tail.length) 64 base am imm c) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  subst hc
  have hlow : s.RIP.toNat + (8 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := adc_m_imm32_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_m64_imm32_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 8 (8 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: rex :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (adcMImm32SegEffect p (8 + am.tail.length) 64 base am imm c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [adcMImm32SegEffect_components]; exact mem_components_rmw _ _) hpre.1.store.code (by simp; omega))
    (adc_m64_imm32_seg_effect_step p r base rex hrex am hv hx hb imm c)

theorem adc_m32_imm32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) (c : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 4 (7 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 32 imm)))
      (adcMImm32SegEffect p (7 + am.tail.length) 32 base am imm c) := by
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  subst hc
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := adc_m_imm32_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_m32_imm32_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 4 (7 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (adcMImm32SegEffect p (7 + am.tail.length) 32 base am imm c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [adcMImm32SegEffect_components]; exact mem_components_rmw _ _) hpre.1.store.code (by simp; omega))
    (adc_m32_imm32_seg_effect_step p r base am hv hx hb imm c)

theorem adc_m32_imm32_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) (c : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 4 (8 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: rex :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 32 imm)))
      (adcMImm32SegEffect p (8 + am.tail.length) 32 base am imm c) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  subst hc
  have hlow : s.RIP.toNat + (8 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := adc_m_imm32_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_m32_imm32_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 4 (8 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: rex :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (adcMImm32SegEffect p (8 + am.tail.length) 32 base am imm c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [adcMImm32SegEffect_components]; exact mem_components_rmw _ _) hpre.1.store.code (by simp; omega))
    (adc_m32_imm32_rex_seg_effect_step p r base rex hrex am hv hx hb imm c)

theorem adc_m16_imm16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) (c : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 2 (6 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: 0x66 :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 16 imm)))
      (adcM16Imm16SegEffect p (6 + am.tail.length) base am imm c) := by
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  subst hc
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66]
      (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := adc_m16_imm16_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_m16_imm16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 2 (6 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: 0x66 :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 16 imm)))
      (Effect.post (adcM16Imm16SegEffect p (6 + am.tail.length) base am imm c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [adcM16Imm16SegEffect_components]; exact mem_components_rmw _ _) hpre.1.store.code (by simp; omega))
    (adc_m16_imm16_seg_effect_step p r base am hv hx hb imm c)

theorem adc_m16_imm16_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 16) (c : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 2 (7 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 16 imm)))
      (adcM16Imm16SegEffect p (7 + am.tail.length) base am imm c) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  subst hc
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66, rex] =
      withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66, rex]
      (noSegPrefix_cons noSegPrefix_66 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_66_rex _ _ hr]
  have hstep := adc_m16_imm16_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_m16_imm16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 16) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 2 (7 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 16 imm)))
      (Effect.post (adcM16Imm16SegEffect p (7 + am.tail.length) base am imm c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [adcM16Imm16SegEffect_components]; exact mem_components_rmw _ _) hpre.1.store.code (by simp; omega))
    (adc_m16_imm16_rex_seg_effect_step p r base rex hrex am hv hx hb imm c)

theorem adc_m64_imm32_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) (c : Bool) :
    StepEffect (fun s => Rmw32Pre p am 8 (8 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: rex :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 32 imm)))
      (adcMImm32A32Effect p (8 + am.tail.length) 64 am imm c) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (8 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := adc_m_imm32_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_m64_imm32_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 8 (8 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: rex :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (adcMImm32A32Effect p (8 + am.tail.length) 64 am imm c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [adcMImm32A32Effect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (adc_m64_imm32_a32_effect_step p rex hrex am hv hx hb imm c)

theorem adc_m32_imm32_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) (c : Bool) :
    StepEffect (fun s => Rmw32Pre p am 4 (7 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 32 imm)))
      (adcMImm32A32Effect p (7 + am.tail.length) 32 am imm c) := by
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := adc_m_imm32_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_m32_imm32_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 4 (7 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (adcMImm32A32Effect p (7 + am.tail.length) 32 am imm c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [adcMImm32A32Effect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (adc_m32_imm32_a32_effect_step p am hv hx hb imm c)

theorem adc_m32_imm32_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) (c : Bool) :
    StepEffect (fun s => Rmw32Pre p am 4 (8 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: rex :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 32 imm)))
      (adcMImm32A32Effect p (8 + am.tail.length) 32 am imm c) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (8 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := adc_m_imm32_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_m32_imm32_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 4 (8 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: rex :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (adcMImm32A32Effect p (8 + am.tail.length) 32 am imm c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [adcMImm32A32Effect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (adc_m32_imm32_rex_a32_effect_step p rex hrex am hv hx hb imm c)

theorem adc_m16_imm16_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) (c : Bool) :
    StepEffect (fun s => Rmw32Pre p am 2 (6 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: 0x66 :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 16 imm)))
      (adcM16Imm16A32Effect p (6 + am.tail.length) am imm c) := by
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66]) := by
    rw [scanContext_asz_cons]
  have hstep := adc_m16_imm16_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_m16_imm16_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 2 (6 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: 0x66 :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 16 imm)))
      (Effect.post (adcM16Imm16A32Effect p (6 + am.tail.length) am imm c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [adcM16Imm16A32Effect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (adc_m16_imm16_a32_effect_step p am hv hx hb imm c)

theorem adc_m16_imm16_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 16) (c : Bool) :
    StepEffect (fun s => Rmw32Pre p am 2 (7 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 16 imm)))
      (adcM16Imm16A32Effect p (7 + am.tail.length) am imm c) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, rex] =
      withAsz (oszRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_66_rex _ _ hr]
  have hstep := adc_m16_imm16_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem adc_m16_imm16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 16) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 2 (7 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 16 imm)))
      (Effect.post (adcM16Imm16A32Effect p (7 + am.tail.length) am imm c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [adcM16Imm16A32Effect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (adc_m16_imm16_rex_a32_effect_step p rex hrex am hv hx hb imm c)

theorem adc_m64_imm32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 32) (c : Bool) :
    Triple (fun s => RmwPre p am 8 (7 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcM64Imm32 am imm))
      (Effect.post (adcMImm32Effect p (7 + am.tail.length) 64 am imm c)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact adc_m64_imm32_triple_of_bytes p _ hrex am hv hx hb imm c

theorem adc_m32_imm32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 32) (c : Bool) :
    Triple (fun s => RmwPre p am 4 (encodeAdcM32Imm32 am imm).length s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcM32Imm32 am imm))
      (Effect.post (adcMImm32Effect p (encodeAdcM32Imm32 am imm).length 32 am imm c)) := by
  unfold encodeAdcM32Imm32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := adc_m32_imm32_triple_of_bytes p am hv hx hb imm c
    rwa [show (0x81 :: am.modrm 2 :: (am.tail ++ immBytes 32 imm)).length =
      6 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := adc_m32_imm32_rex_triple_of_bytes p _ hrex am hv hx hb imm c
    rwa [show (am.rexByte false 0 :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 32 imm)).length =
      7 + am.tail.length by simp; omega]

theorem adc_m16_imm16_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 16) (c : Bool) :
    Triple (fun s => RmwPre p am 2 (encodeAdcM16Imm16 am imm).length s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeAdcM16Imm16 am imm))
      (Effect.post (adcM16Imm16Effect p (encodeAdcM16Imm16 am imm).length am imm c)) := by
  unfold encodeAdcM16Imm16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := adc_m16_imm16_triple_of_bytes p am hv hx hb imm c
    rwa [show (0x66 :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 16 imm)).length =
      5 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := adc_m16_imm16_rex_triple_of_bytes p _ hrex am hv hx hb imm c
    rwa [show (0x66 :: am.rexByte false 0 :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 16 imm)).length =
      6 + am.tail.length by simp; omega]

theorem adc_m64_imm32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (imm : BitVec 32) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 8 (8 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: encodeAdcM64Imm32 am imm))
      (Effect.post (adcMImm32SegEffect p (8 + am.tail.length) 64 base am
        imm c)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact adc_m64_imm32_seg_triple_of_bytes p r base _ hrex am hv hx hb imm c

theorem adc_m32_imm32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (imm : BitVec 32) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 4 (r.prefixByte :: encodeAdcM32Imm32 am imm).length s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: encodeAdcM32Imm32 am imm))
      (Effect.post (adcMImm32SegEffect p (r.prefixByte :: encodeAdcM32Imm32 am imm).length 32 base am
        imm c)) := by
  unfold encodeAdcM32Imm32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := adc_m32_imm32_seg_triple_of_bytes p r base am hv hx hb imm c
    rwa [show (r.prefixByte :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 32 imm)).length =
      7 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := adc_m32_imm32_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb imm c
    rwa [show (r.prefixByte :: am.rexByte false 0 :: 0x81 :: am.modrm 2 ::
      (am.tail ++ immBytes 32 imm)).length = 8 + am.tail.length by simp; omega]

theorem adc_m16_imm16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (imm : BitVec 16) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 2 (r.prefixByte :: encodeAdcM16Imm16 am imm).length s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (r.prefixByte :: encodeAdcM16Imm16 am imm))
      (Effect.post (adcM16Imm16SegEffect p (r.prefixByte :: encodeAdcM16Imm16 am imm).length base am
        imm c)) := by
  unfold encodeAdcM16Imm16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := adc_m16_imm16_seg_triple_of_bytes p r base am hv hx hb imm c
    rwa [show (r.prefixByte :: 0x66 :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 16 imm)).length =
      6 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := adc_m16_imm16_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb imm c
    rwa [show (r.prefixByte :: 0x66 :: am.rexByte false 0 :: 0x81 :: am.modrm 2 ::
      (am.tail ++ immBytes 16 imm)).length = 7 + am.tail.length by simp; omega]

theorem adc_m64_imm32_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 32) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 8 (8 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: encodeAdcM64Imm32 am imm))
      (Effect.post (adcMImm32A32Effect p (8 + am.tail.length) 64 am imm c)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact adc_m64_imm32_a32_triple_of_bytes p _ hrex am hv hx hb imm c

theorem adc_m32_imm32_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 32) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 4 (0x67 :: encodeAdcM32Imm32 am imm).length s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: encodeAdcM32Imm32 am imm))
      (Effect.post (adcMImm32A32Effect p (0x67 :: encodeAdcM32Imm32 am imm).length 32 am imm c)) := by
  unfold encodeAdcM32Imm32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := adc_m32_imm32_a32_triple_of_bytes p am hv hx hb imm c
    rwa [show (0x67 :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 32 imm)).length =
      7 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := adc_m32_imm32_rex_a32_triple_of_bytes p _ hrex am hv hx hb imm c
    rwa [show (0x67 :: am.rexByte false 0 :: 0x81 :: am.modrm 2 ::
      (am.tail ++ immBytes 32 imm)).length = 8 + am.tail.length by simp; omega]

theorem adc_m16_imm16_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 16) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 2 (0x67 :: encodeAdcM16Imm16 am imm).length s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x67 :: encodeAdcM16Imm16 am imm))
      (Effect.post (adcM16Imm16A32Effect p (0x67 :: encodeAdcM16Imm16 am imm).length am imm c)) := by
  unfold encodeAdcM16Imm16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := adc_m16_imm16_a32_triple_of_bytes p am hv hx hb imm c
    rwa [show (0x67 :: 0x66 :: 0x81 :: am.modrm 2 :: (am.tail ++ immBytes 16 imm)).length =
      6 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := adc_m16_imm16_rex_a32_triple_of_bytes p _ hrex am hv hx hb imm c
    rwa [show (0x67 :: 0x66 :: am.rexByte false 0 :: 0x81 :: am.modrm 2 ::
      (am.tail ++ immBytes 16 imm)).length = 7 + am.tail.length by simp; omega]

attribute [x86_compose] adcMImm32Effect adcM16Imm16Effect
  adcMImm32SegEffect adcM16Imm16SegEffect
  adcMImm32A32Effect adcM16Imm16A32Effect

theorem adcMImm32Effect_local {p : BitVec 64} {len n : Nat} {am : AddrMode} {imm32 : BitVec 32}
    {c : Bool}
    (hn : n % 8 = 0) :
    Effect.Local (adcMImm32Effect p len n am imm32 c) := by
  effect_local [adcMImm32Effect, hn]

@[x86_local] theorem adcMImm32Effect_local64 {p : BitVec 64} {len : Nat} {am : AddrMode}
    {imm32 : BitVec 32} {c : Bool} :
    Effect.Local (adcMImm32Effect p len 64 am imm32 c) :=
  adcMImm32Effect_local (by decide)

@[x86_local] theorem adcMImm32Effect_local32 {p : BitVec 64} {len : Nat} {am : AddrMode}
    {imm32 : BitVec 32} {c : Bool} :
    Effect.Local (adcMImm32Effect p len 32 am imm32 c) :=
  adcMImm32Effect_local (by decide)

theorem adcMImm32SegEffect_local {p : BitVec 64} {len n : Nat} {base : BitVec 64} {am : AddrMode} {imm32 : BitVec 32}
    {c : Bool}
    (hn : n % 8 = 0) :
    Effect.Local (adcMImm32SegEffect p len n base am imm32 c) := by
  effect_local [adcMImm32SegEffect, hn]

@[x86_local] theorem adcMImm32SegEffect_local64 {p : BitVec 64} {len : Nat} {base : BitVec 64} {am : AddrMode}
    {imm32 : BitVec 32} {c : Bool} :
    Effect.Local (adcMImm32SegEffect p len 64 base am imm32 c) :=
  adcMImm32SegEffect_local (by decide)

@[x86_local] theorem adcMImm32SegEffect_local32 {p : BitVec 64} {len : Nat} {base : BitVec 64} {am : AddrMode}
    {imm32 : BitVec 32} {c : Bool} :
    Effect.Local (adcMImm32SegEffect p len 32 base am imm32 c) :=
  adcMImm32SegEffect_local (by decide)

theorem adcMImm32A32Effect_local {p : BitVec 64} {len n : Nat} {am : AddrMode} {imm32 : BitVec 32}
    {c : Bool}
    (hn : n % 8 = 0) :
    Effect.Local (adcMImm32A32Effect p len n am imm32 c) := by
  effect_local [adcMImm32A32Effect, hn]

@[x86_local] theorem adcMImm32A32Effect_local64 {p : BitVec 64} {len : Nat} {am : AddrMode}
    {imm32 : BitVec 32} {c : Bool} :
    Effect.Local (adcMImm32A32Effect p len 64 am imm32 c) :=
  adcMImm32A32Effect_local (by decide)

@[x86_local] theorem adcMImm32A32Effect_local32 {p : BitVec 64} {len : Nat} {am : AddrMode}
    {imm32 : BitVec 32} {c : Bool} :
    Effect.Local (adcMImm32A32Effect p len 32 am imm32 c) :=
  adcMImm32A32Effect_local (by decide)

@[x86_local] theorem adcM16Imm16Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode}
    {imm16 : BitVec 16} {c : Bool} :
    Effect.Local (adcM16Imm16Effect p len am imm16 c) := by
  effect_local [adcM16Imm16Effect]

@[x86_local] theorem adcM16Imm16SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} {am : AddrMode}
    {imm16 : BitVec 16} {c : Bool} :
    Effect.Local (adcM16Imm16SegEffect p len base am imm16 c) := by
  effect_local [adcM16Imm16SegEffect]

@[x86_local] theorem adcM16Imm16A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode}
    {imm16 : BitVec 16} {c : Bool} :
    Effect.Local (adcM16Imm16A32Effect p len am imm16 c) := by
  effect_local [adcM16Imm16A32Effect]

end X86Proofs
