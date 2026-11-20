import X86Proofs.Instructions.Xadd.Generated.MR.Step
import X86Proofs.Instructions.Xadd.Generated.MR.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def xaddMREffect (p : BitVec 64) (len n : Nat) (src : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := am.addr s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand n).read s
  let y := (Operand.reg src : Operand n).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand n), (xaddSpec x y).1⟩,
      ⟨(Operand.reg src : Operand 64), mergeGPR n x ((Operand.reg src : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (xaddSpec x y).2.2) }

@[simp] theorem xaddMREffect_components (p : BitVec 64) (len n : Nat) (src : BitVec 5)
    (am : AddrMode) (s : RamState) : (xaddMREffect p len n src am s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) (n / 8), .reg src, .flags, .rip] := rfl

def xaddMRSegEffect (p : BitVec 64) (len n : Nat) (base : BitVec 64) (src : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := base + am.addr s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand n).read s
  let y := (Operand.reg src : Operand n).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand n), (xaddSpec x y).1⟩,
      ⟨(Operand.reg src : Operand 64), mergeGPR n x ((Operand.reg src : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (xaddSpec x y).2.2) }

@[simp] theorem xaddMRSegEffect_components (p : BitVec 64) (len n : Nat) (base : BitVec 64)
    (src : BitVec 5) (am : AddrMode) (s : RamState) :
    (xaddMRSegEffect p len n base src am s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) (n / 8),
        .reg src, .flags, .rip] := rfl

def xaddMRA32Effect (p : BitVec 64) (len n : Nat) (src : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := am.addr32 s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand n).read s
  let y := (Operand.reg src : Operand n).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand n), (xaddSpec x y).1⟩,
      ⟨(Operand.reg src : Operand 64), mergeGPR n x ((Operand.reg src : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (xaddSpec x y).2.2) }

@[simp] theorem xaddMRA32Effect_components (p : BitVec 64) (len n : Nat) (src : BitVec 5)
    (am : AddrMode) (s : RamState) : (xaddMRA32Effect p len n src am s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) (n / 8), .reg src, .flags,
        .rip] := rfl

theorem xadd_m64_r64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 8 (4 + am.tail.length))
      (codeRange p (rex :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (xaddMREffect p (4 + am.tail.length) 64
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := xadd_m_r_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    refine ⟨Operand.read_afterStep_rmwReg_mem (n := 64) s _ (by decide) (by decide) _ _ _ _ _ _, ?_⟩
    rw [Operand.read_afterStep_rmwReg_reg]
    simp only [xaddSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem xadd_m64_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 8 (4 + am.tail.length))
      (codeRange p (rex :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (Effect.post (xaddMREffect p (4 + am.tail.length) 64
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xaddMREffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.code
    (by simp; omega))
    (xadd_m64_r64_effect_step p rex hrex reg am hv hx hb)

theorem xadd_m32_r32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (RmwPre p am 4 (3 + am.tail.length))
      (codeRange p (0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (xaddMREffect p (3 + am.tail.length) 32
        (gprNumber 0 0 reg) am) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := xadd_m_r_step s h [] (by simp)
    (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) reg am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    refine ⟨Operand.read_afterStep_rmwReg_mem (n := 32) s _ (by decide) (by decide) _ _ _ _ _ _, ?_⟩
    rw [Operand.read_afterStep_rmwReg_reg]
    simp only [xaddSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem xadd_m32_r32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (RmwPre p am 4 (3 + am.tail.length))
      (codeRange p (0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (Effect.post (xaddMREffect p (3 + am.tail.length) 32
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xaddMREffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.code
    (by simp; omega))
    (xadd_m32_r32_effect_step p reg am hv hx hb)

theorem xadd_m32_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 4 (4 + am.tail.length))
      (codeRange p (rex :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (xaddMREffect p (4 + am.tail.length) 32
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := xadd_m_r_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    refine ⟨Operand.read_afterStep_rmwReg_mem (n := 32) s _ (by decide) (by decide) _ _ _ _ _ _, ?_⟩
    rw [Operand.read_afterStep_rmwReg_reg]
    simp only [xaddSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem xadd_m32_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 4 (4 + am.tail.length))
      (codeRange p (rex :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (Effect.post (xaddMREffect p (4 + am.tail.length) 32
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xaddMREffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.code
    (by simp; omega))
    (xadd_m32_r32_rex_effect_step p rex hrex reg am hv hx hb)

theorem xadd_m16_r16_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (RmwPre p am 2 (4 + am.tail.length))
      (codeRange p (0x66 :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (xaddMREffect p (4 + am.tail.length) 16
        (gprNumber 0 0 reg) am) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := xadd_m16_r16_step s h [0x66] (by simpa using scanPrefix_66)
    (by simp)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) reg am hv
    (by exact (AddrContext.osz _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    refine ⟨Operand.read_afterStep_rmwReg_mem (n := 16) s _ (by decide) (by decide) _ _ _ _ _ _, ?_⟩
    rw [Operand.read_afterStep_rmwReg_reg]
    simp only [xaddSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem xadd_m16_r16_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (RmwPre p am 2 (4 + am.tail.length))
      (codeRange p (0x66 :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (Effect.post (xaddMREffect p (4 + am.tail.length) 16
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xaddMREffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.code
    (by simp; omega))
    (xadd_m16_r16_effect_step p reg am hv hx hb)

theorem xadd_m16_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 2 (5 + am.tail.length))
      (codeRange p (0x66 :: rex :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (xaddMREffect p (5 + am.tail.length) 16
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := xadd_m16_r16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix])
    (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_66_rex _ _ hr]; exact (AddrContext.oszRex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_66_rex _ _ hr]; exact hread)
  simp only [scanContext_66_rex _ _ hr] at hstep
  have hsrc : gprNumber (oszRexContext s.DS rex.toBitVec).rex_r4
      (oszRexContext s.DS rex.toBitVec).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    refine ⟨Operand.read_afterStep_rmwReg_mem (n := 16) s _ (by decide) (by decide) _ _ _ _ _ _, ?_⟩
    rw [Operand.read_afterStep_rmwReg_reg]
    simp only [xaddSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem xadd_m16_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 2 (5 + am.tail.length))
      (codeRange p (0x66 :: rex :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (Effect.post (xaddMREffect p (5 + am.tail.length) 16
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xaddMREffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.code
    (by simp; omega))
    (xadd_m16_r16_rex_effect_step p rex hrex reg am hv hx hb)

theorem xadd_m64_r64_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegRmwPre p r base am 8 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (xaddMRSegEffect p (5 + am.tail.length) 64 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := xadd_m_r_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix))
    (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    refine ⟨Operand.read_afterStep_rmwReg_mem (n := 64) s _ (by decide) (by decide) _ _ _ _ _ _, ?_⟩
    rw [Operand.read_afterStep_rmwReg_reg]
    simp only [xaddSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem xadd_m64_r64_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegRmwPre p r base am 8 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (Effect.post (xaddMRSegEffect p (5 + am.tail.length) 64 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xaddMRSegEffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.store.code
    (by simp; omega))
    (xadd_m64_r64_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem xadd_m32_r32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SegRmwPre p r base am 4 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (xaddMRSegEffect p (4 + am.tail.length) 32 base
        (gprNumber 0 0 reg) am) := by
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
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
  have hstep := xadd_m_r_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp))
    (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    refine ⟨Operand.read_afterStep_rmwReg_mem (n := 32) s _ (by decide) (by decide) _ _ _ _ _ _, ?_⟩
    rw [Operand.read_afterStep_rmwReg_reg]
    simp only [xaddSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem xadd_m32_r32_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegRmwPre p r base am 4 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (Effect.post (xaddMRSegEffect p (4 + am.tail.length) 32 base
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xaddMRSegEffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.store.code
    (by simp; omega))
    (xadd_m32_r32_seg_effect_step p r base reg am hv hx hb)

theorem xadd_m32_r32_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegRmwPre p r base am 4 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (xaddMRSegEffect p (5 + am.tail.length) 32 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := xadd_m_r_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix))
    (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    refine ⟨Operand.read_afterStep_rmwReg_mem (n := 32) s _ (by decide) (by decide) _ _ _ _ _ _, ?_⟩
    rw [Operand.read_afterStep_rmwReg_reg]
    simp only [xaddSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem xadd_m32_r32_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegRmwPre p r base am 4 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (Effect.post (xaddMRSegEffect p (5 + am.tail.length) 32 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xaddMRSegEffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.store.code
    (by simp; omega))
    (xadd_m32_r32_rex_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem xadd_m16_r16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SegRmwPre p r base am 2 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (xaddMRSegEffect p (5 + am.tail.length) 16 base
        (gprNumber 0 0 reg) am) := by
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
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
  have hstep := xadd_m16_r16_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66))
    (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    refine ⟨Operand.read_afterStep_rmwReg_mem (n := 16) s _ (by decide) (by decide) _ _ _ _ _ _, ?_⟩
    rw [Operand.read_afterStep_rmwReg_reg]
    simp only [xaddSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem xadd_m16_r16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegRmwPre p r base am 2 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (Effect.post (xaddMRSegEffect p (5 + am.tail.length) 16 base
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xaddMRSegEffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.store.code
    (by simp; omega))
    (xadd_m16_r16_seg_effect_step p r base reg am hv hx hb)

theorem xadd_m16_r16_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegRmwPre p r base am 2 (6 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (xaddMRSegEffect p (6 + am.tail.length) 16 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66, rex] =
      withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66, rex]
      (noSegPrefix_cons noSegPrefix_66 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_66_rex _ _ hr]
  have hstep := xadd_m16_r16_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix]))
    (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    refine ⟨Operand.read_afterStep_rmwReg_mem (n := 16) s _ (by decide) (by decide) _ _ _ _ _ _, ?_⟩
    rw [Operand.read_afterStep_rmwReg_reg]
    simp only [xaddSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem xadd_m16_r16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegRmwPre p r base am 2 (6 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (Effect.post (xaddMRSegEffect p (6 + am.tail.length) 16 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xaddMRSegEffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.store.code
    (by simp; omega))
    (xadd_m16_r16_rex_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem xadd_m64_r64_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Rmw32Pre p am 8 (5 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (xaddMRA32Effect p (5 + am.tail.length) 64
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := xadd_m_r_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix))
    (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (rexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (rexContext s.DS rex.toBitVec)).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    refine ⟨Operand.read_afterStep_rmwReg_mem (n := 64) s _ (by decide) (by decide) _ _ _ _ _ _, ?_⟩
    rw [Operand.read_afterStep_rmwReg_reg]
    simp only [xaddSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem xadd_m64_r64_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (Rmw32Pre p am 8 (5 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (Effect.post (xaddMRA32Effect p (5 + am.tail.length) 64
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xaddMRA32Effect_components]; exact mem_components_rmwReg _ _ _)
    hpre.code
    (by simp; omega))
    (xadd_m64_r64_a32_effect_step p rex hrex reg am hv hx hb)

theorem xadd_m32_r32_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (Rmw32Pre p am 4 (4 + am.tail.length))
      (codeRange p (0x67 :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (xaddMRA32Effect p (4 + am.tail.length) 32
        (gprNumber 0 0 reg) am) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := xadd_m_r_a32_step s h [0x67] (scanPrefix_asz_cons (by simp))
    (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    refine ⟨Operand.read_afterStep_rmwReg_mem (n := 32) s _ (by decide) (by decide) _ _ _ _ _ _, ?_⟩
    rw [Operand.read_afterStep_rmwReg_reg]
    simp only [xaddSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem xadd_m32_r32_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (Rmw32Pre p am 4 (4 + am.tail.length))
      (codeRange p (0x67 :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (Effect.post (xaddMRA32Effect p (4 + am.tail.length) 32
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xaddMRA32Effect_components]; exact mem_components_rmwReg _ _ _)
    hpre.code
    (by simp; omega))
    (xadd_m32_r32_a32_effect_step p reg am hv hx hb)

theorem xadd_m32_r32_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Rmw32Pre p am 4 (5 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (xaddMRA32Effect p (5 + am.tail.length) 32
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := xadd_m_r_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix))
    (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (rexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (rexContext s.DS rex.toBitVec)).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    refine ⟨Operand.read_afterStep_rmwReg_mem (n := 32) s _ (by decide) (by decide) _ _ _ _ _ _, ?_⟩
    rw [Operand.read_afterStep_rmwReg_reg]
    simp only [xaddSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem xadd_m32_r32_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (Rmw32Pre p am 4 (5 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (Effect.post (xaddMRA32Effect p (5 + am.tail.length) 32
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xaddMRA32Effect_components]; exact mem_components_rmwReg _ _ _)
    hpre.code
    (by simp; omega))
    (xadd_m32_r32_rex_a32_effect_step p rex hrex reg am hv hx hb)

theorem xadd_m16_r16_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (Rmw32Pre p am 2 (5 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (xaddMRA32Effect p (5 + am.tail.length) 16
        (gprNumber 0 0 reg) am) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66]) := by
    rw [scanContext_asz_cons]
  have hstep := xadd_m16_r16_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66))
    (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66])).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    refine ⟨Operand.read_afterStep_rmwReg_mem (n := 16) s _ (by decide) (by decide) _ _ _ _ _ _, ?_⟩
    rw [Operand.read_afterStep_rmwReg_reg]
    simp only [xaddSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem xadd_m16_r16_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (Rmw32Pre p am 2 (5 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (Effect.post (xaddMRA32Effect p (5 + am.tail.length) 16
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xaddMRA32Effect_components]; exact mem_components_rmwReg _ _ _)
    hpre.code
    (by simp; omega))
    (xadd_m16_r16_a32_effect_step p reg am hv hx hb)

theorem xadd_m16_r16_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Rmw32Pre p am 2 (6 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (xaddMRA32Effect p (6 + am.tail.length) 16
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, rex] =
      withAsz (oszRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_66_rex _ _ hr]
  have hstep := xadd_m16_r16_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix]))
    (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (oszRexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (oszRexContext s.DS rex.toBitVec)).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    refine ⟨Operand.read_afterStep_rmwReg_mem (n := 16) s _ (by decide) (by decide) _ _ _ _ _ _, ?_⟩
    rw [Operand.read_afterStep_rmwReg_reg]
    simp only [xaddSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem xadd_m16_r16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (Rmw32Pre p am 2 (6 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: 0xC1 :: am.modrm reg :: am.tail))
      (Effect.post (xaddMRA32Effect p (6 + am.tail.length) 16
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xaddMRA32Effect_components]; exact mem_components_rmwReg _ _ _)
    hpre.code
    (by simp; omega))
    (xadd_m16_r16_rex_a32_effect_step p rex hrex reg am hv hx hb)

theorem xadd_m64_r64_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (RmwPre p am 8 (4 + am.tail.length))
      (codeRange p (encodeXaddM64R64 src am))
      (Effect.post (xaddMREffect p (4 + am.tail.length) 64 (src.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := xadd_m64_r64_triple_of_bytes p _ hrex (regLow src) am hv hx hb
  rwa [hr, gprNumber_reg] at this

theorem xadd_m32_r32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (RmwPre p am 4 (encodeXaddM32R32 src am).length)
      (codeRange p (encodeXaddM32R32 src am))
      (Effect.post
        (xaddMREffect p (encodeXaddM32R32 src am).length 32 (src.setWidth 5) am)) := by
  unfold encodeXaddM32R32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := xadd_m32_r32_triple_of_bytes p (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := xadd_m32_r32_rex_triple_of_bytes p _ hrex (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem xadd_m16_r16_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (RmwPre p am 2 (encodeXaddM16R16 src am).length)
      (codeRange p (encodeXaddM16R16 src am))
      (Effect.post
        (xaddMREffect p (encodeXaddM16R16 src am).length 16 (src.setWidth 5) am)) := by
  unfold encodeXaddM16R16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := xadd_m16_r16_triple_of_bytes p (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := xadd_m16_r16_rex_triple_of_bytes p _ hrex (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

theorem xadd_m64_r64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (SegRmwPre p r base am 8 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: encodeXaddM64R64 src am))
      (Effect.post (xaddMRSegEffect p (5 + am.tail.length) 64 base (src.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := xadd_m64_r64_seg_triple_of_bytes p r base _ hrex (regLow src) am hv hx hb
  rwa [hr, gprNumber_reg] at this

theorem xadd_m32_r32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (SegRmwPre p r base am 4 (r.prefixByte :: encodeXaddM32R32 src am).length)
      (codeRange p (r.prefixByte :: encodeXaddM32R32 src am))
      (Effect.post (xaddMRSegEffect p (r.prefixByte :: encodeXaddM32R32 src am).length 32 base
        (src.setWidth 5) am)) := by
  unfold encodeXaddM32R32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := xadd_m32_r32_seg_triple_of_bytes p r base (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := xadd_m32_r32_rex_seg_triple_of_bytes p r base _ hrex (regLow src) am
      hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

theorem xadd_m16_r16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (SegRmwPre p r base am 2 (r.prefixByte :: encodeXaddM16R16 src am).length)
      (codeRange p (r.prefixByte :: encodeXaddM16R16 src am))
      (Effect.post (xaddMRSegEffect p (r.prefixByte :: encodeXaddM16R16 src am).length 16 base
        (src.setWidth 5) am)) := by
  unfold encodeXaddM16R16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := xadd_m16_r16_seg_triple_of_bytes p r base (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := xadd_m16_r16_rex_seg_triple_of_bytes p r base _ hrex (regLow src) am
      hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 + 1 = 6 + am.tail.length by omega]

theorem xadd_m64_r64_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (Rmw32Pre p am 8 (5 + am.tail.length))
      (codeRange p (0x67 :: encodeXaddM64R64 src am))
      (Effect.post (xaddMRA32Effect p (5 + am.tail.length) 64 (src.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := xadd_m64_r64_a32_triple_of_bytes p _ hrex (regLow src) am hv hx hb
  rwa [hr, gprNumber_reg] at this

theorem xadd_m32_r32_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (Rmw32Pre p am 4 (0x67 :: encodeXaddM32R32 src am).length)
      (codeRange p (0x67 :: encodeXaddM32R32 src am))
      (Effect.post
        (xaddMRA32Effect p (0x67 :: encodeXaddM32R32 src am).length 32 (src.setWidth 5) am)) := by
  unfold encodeXaddM32R32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := xadd_m32_r32_a32_triple_of_bytes p (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := xadd_m32_r32_rex_a32_triple_of_bytes p _ hrex (regLow src) am hv hx
      hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

theorem xadd_m16_r16_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (Rmw32Pre p am 2 (0x67 :: encodeXaddM16R16 src am).length)
      (codeRange p (0x67 :: encodeXaddM16R16 src am))
      (Effect.post
        (xaddMRA32Effect p (0x67 :: encodeXaddM16R16 src am).length 16 (src.setWidth 5) am)) := by
  unfold encodeXaddM16R16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := xadd_m16_r16_a32_triple_of_bytes p (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := xadd_m16_r16_rex_a32_triple_of_bytes p _ hrex (regLow src) am hv hx
      hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 + 1 = 6 + am.tail.length by omega]

attribute [x86_compose] xaddMREffect

theorem xaddMREffect_local {p : BitVec 64} {len n : Nat} {src : BitVec 5} {am : AddrMode}
    (hn : n % 8 = 0) :
    Effect.Local (xaddMREffect p len n src am) := by
  effect_local [xaddMREffect, hn]

@[x86_local] theorem xaddMREffect_local64 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} :
    Effect.Local (xaddMREffect p len 64 src am) :=
  xaddMREffect_local (by decide)

@[x86_local] theorem xaddMREffect_local32 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} :
    Effect.Local (xaddMREffect p len 32 src am) :=
  xaddMREffect_local (by decide)

@[x86_local] theorem xaddMREffect_local16 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} :
    Effect.Local (xaddMREffect p len 16 src am) :=
  xaddMREffect_local (by decide)

@[x86_local] theorem xaddMREffect_local8 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} :
    Effect.Local (xaddMREffect p len 8 src am) :=
  xaddMREffect_local (by decide)

attribute [x86_compose] xaddMRSegEffect

theorem xaddMRSegEffect_local {p : BitVec 64} {len n : Nat} {base : BitVec 64} {src : BitVec 5}
    {am : AddrMode} (hn : n % 8 = 0) :
    Effect.Local (xaddMRSegEffect p len n base src am) := by
  effect_local [xaddMRSegEffect, hn]

@[x86_local] theorem xaddMRSegEffect_local64 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 5} {am : AddrMode} :
    Effect.Local (xaddMRSegEffect p len 64 base src am) :=
  xaddMRSegEffect_local (by decide)

@[x86_local] theorem xaddMRSegEffect_local32 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 5} {am : AddrMode} :
    Effect.Local (xaddMRSegEffect p len 32 base src am) :=
  xaddMRSegEffect_local (by decide)

@[x86_local] theorem xaddMRSegEffect_local16 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 5} {am : AddrMode} :
    Effect.Local (xaddMRSegEffect p len 16 base src am) :=
  xaddMRSegEffect_local (by decide)

@[x86_local] theorem xaddMRSegEffect_local8 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 5} {am : AddrMode} :
    Effect.Local (xaddMRSegEffect p len 8 base src am) :=
  xaddMRSegEffect_local (by decide)

attribute [x86_compose] xaddMRA32Effect

theorem xaddMRA32Effect_local {p : BitVec 64} {len n : Nat} {src : BitVec 5}
    {am : AddrMode} (hn : n % 8 = 0) :
    Effect.Local (xaddMRA32Effect p len n src am) := by
  effect_local [xaddMRA32Effect, hn]

@[x86_local] theorem xaddMRA32Effect_local64 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} :
    Effect.Local (xaddMRA32Effect p len 64 src am) :=
  xaddMRA32Effect_local (by decide)

@[x86_local] theorem xaddMRA32Effect_local32 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} :
    Effect.Local (xaddMRA32Effect p len 32 src am) :=
  xaddMRA32Effect_local (by decide)

@[x86_local] theorem xaddMRA32Effect_local16 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} :
    Effect.Local (xaddMRA32Effect p len 16 src am) :=
  xaddMRA32Effect_local (by decide)

@[x86_local] theorem xaddMRA32Effect_local8 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} :
    Effect.Local (xaddMRA32Effect p len 8 src am) :=
  xaddMRA32Effect_local (by decide)

end X86Proofs
