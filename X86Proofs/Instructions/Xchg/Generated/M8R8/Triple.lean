import X86Proofs.Instructions.Xchg.Generated.M8R8.Step
import X86Proofs.Instructions.Xchg.Generated.M8R8.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Xchg.Generated.MR.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem xchg_m8_r8_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LockedRmwPre p am 1 (2 + am.tail.length))
      (codeRange p (0x86 :: am.modrm reg :: am.tail))
      (xchgMREffect p (2 + am.tail.length) 8
        (gprNumber 0 0 reg) am) := by
  intro s h hcode hpre
  have hlk := lockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := xchg_m8_r8_step s h [] (by simp)
    (by simp)
    (by rfl) (by rfl)
    (by rfl) reg
    (.inr (by exact gprNumber_low4 reg hreg)) am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
    (by exact hlk)
  dsimp only at hstep
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwRegResult h _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwRegResult_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_rmwRegResult s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  refine ⟨Operand.read_afterStep_rmwRegResult_mem (n := 8) s _ (by decide) (by decide) _ _ _ _ _,
    ?_⟩
  rw [Operand.read_afterStep_rmwRegResult_reg]
  rfl

theorem xchg_m8_r8_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LockedRmwPre p am 1 (2 + am.tail.length))
      (codeRange p (0x86 :: am.modrm reg :: am.tail))
      (Effect.post (xchgMREffect p (2 + am.tail.length) 8
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgMREffect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.code (by simp; omega))
    (xchg_m8_r8_effect_step p reg hreg am hv hx hb)

theorem xchg_m8_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LockedRmwPre p am 1 (3 + am.tail.length))
      (codeRange p (rex :: 0x86 :: am.modrm reg :: am.tail))
      (xchgMREffect p (3 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode hpre
  have hlk := lockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := xchg_m8_r8_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg
    (.inl (by rw [scanContext_rex _ _ hr]; rfl)) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
    (by rw [scanContext_rex _ _ hr]; exact hlk)
  simp only [scanContext_rex _ _ hr] at hstep
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwRegResult h _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwRegResult_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_rmwRegResult s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  refine ⟨Operand.read_afterStep_rmwRegResult_mem (n := 8) s _ (by decide) (by decide) _ _ _ _ _,
    ?_⟩
  rw [Operand.read_afterStep_rmwRegResult_reg]
  rfl

theorem xchg_m8_r8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LockedRmwPre p am 1 (3 + am.tail.length))
      (codeRange p (rex :: 0x86 :: am.modrm reg :: am.tail))
      (Effect.post (xchgMREffect p (3 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgMREffect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.code (by simp; omega))
    (xchg_m8_r8_rex_effect_step p rex hr reg am hv hx hb)

theorem xchg_m8_r8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SegLockedRmwPre p r base am 1 (3 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x86 :: am.modrm reg :: am.tail))
      (xchgMRSegEffect p (3 + am.tail.length) 8 base
        (gprNumber 0 0 reg) am) := by
  intro s h hcode hpre
  have hlk := segLockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := xchg_m8_r8_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp))
    (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inr (by rw [hsc]; exact gprNumber_low4 reg hreg)) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
    (by rw [hsc, segAddr_withSeg]; exact hlk)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwRegResult h _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwRegResult_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_rmwRegResult s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  refine ⟨Operand.read_afterStep_rmwRegResult_mem (n := 8) s _ (by decide) (by decide) _ _ _ _ _,
    ?_⟩
  rw [Operand.read_afterStep_rmwRegResult_reg]
  rfl

theorem xchg_m8_r8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegLockedRmwPre p r base am 1 (3 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x86 :: am.modrm reg :: am.tail))
      (Effect.post (xchgMRSegEffect p (3 + am.tail.length) 8 base
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgMRSegEffect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.store.code (by simp; omega))
    (xchg_m8_r8_seg_effect_step p r base reg hreg am hv hx hb)

theorem xchg_m8_r8_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegLockedRmwPre p r base am 1 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0x86 :: am.modrm reg :: am.tail))
      (xchgMRSegEffect p (4 + am.tail.length) 8 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode hpre
  have hlk := segLockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := xchg_m8_r8_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix))
    (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inl (by rw [hsc]; rfl)) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
    (by rw [hsc, segAddr_withSeg]; exact hlk)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwRegResult h _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwRegResult_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_rmwRegResult s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  refine ⟨Operand.read_afterStep_rmwRegResult_mem (n := 8) s _ (by decide) (by decide) _ _ _ _ _,
    ?_⟩
  rw [Operand.read_afterStep_rmwRegResult_reg]
  rfl

theorem xchg_m8_r8_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegLockedRmwPre p r base am 1 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0x86 :: am.modrm reg :: am.tail))
      (Effect.post (xchgMRSegEffect p (4 + am.tail.length) 8 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgMRSegEffect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.store.code (by simp; omega))
    (xchg_m8_r8_rex_seg_effect_step p r base rex hr reg am hv hx hb)

theorem xchg_m8_r8_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LockedRmw32Pre p am 1 (3 + am.tail.length))
      (codeRange p (0x67 :: 0x86 :: am.modrm reg :: am.tail))
      (xchgMRA32Effect p (3 + am.tail.length) 8
        (gprNumber 0 0 reg) am) := by
  intro s h hcode hpre
  have hlk := lockedRmw32_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := xchg_m8_r8_a32_step s h [0x67] (scanPrefix_asz_cons (by simp))
    (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inr (by rw [hsc]; exact gprNumber_low4 reg hreg)) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
    (by rw [hsc]; exact hlk)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwRegResult h _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwRegResult_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_rmwRegResult s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  refine ⟨Operand.read_afterStep_rmwRegResult_mem (n := 8) s _ (by decide) (by decide) _ _ _ _ _,
    ?_⟩
  rw [Operand.read_afterStep_rmwRegResult_reg]
  rfl

theorem xchg_m8_r8_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LockedRmw32Pre p am 1 (3 + am.tail.length))
      (codeRange p (0x67 :: 0x86 :: am.modrm reg :: am.tail))
      (Effect.post (xchgMRA32Effect p (3 + am.tail.length) 8
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgMRA32Effect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.code (by simp; omega))
    (xchg_m8_r8_a32_effect_step p reg hreg am hv hx hb)

theorem xchg_m8_r8_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LockedRmw32Pre p am 1 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0x86 :: am.modrm reg :: am.tail))
      (xchgMRA32Effect p (4 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode hpre
  have hlk := lockedRmw32_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := xchg_m8_r8_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix))
    (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inl (by rw [hsc]; rfl)) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
    (by rw [hsc]; exact hlk)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (rexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (rexContext s.DS rex.toBitVec)).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwRegResult h _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwRegResult_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_rmwRegResult s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  refine ⟨Operand.read_afterStep_rmwRegResult_mem (n := 8) s _ (by decide) (by decide) _ _ _ _ _,
    ?_⟩
  rw [Operand.read_afterStep_rmwRegResult_reg]
  rfl

theorem xchg_m8_r8_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LockedRmw32Pre p am 1 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0x86 :: am.modrm reg :: am.tail))
      (Effect.post (xchgMRA32Effect p (4 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgMRA32Effect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.code (by simp; omega))
    (xchg_m8_r8_rex_a32_effect_step p rex hr reg am hv hx hb)

theorem xchg_m8_r8_triple [Bindings] (p : BitVec 64) (src : BitVec 4)
    (am : AddrMode) (hv : am.Valid) :
    Triple (LockedRmwPre p am 1 (encodeXchgM8R8 src am).length)
      (codeRange p (encodeXchgM8R8 src am))
      (Effect.post (xchgMREffect p (encodeXchgM8R8 src am).length 8 (src.setWidth 5) am)) := by
  unfold encodeXchgM8R8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec src hs
    have := xchg_m8_r8_triple_of_bytes p (regLow src) hl am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 = 2 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := xchg_m8_r8_rex_triple_of_bytes p _ hrex.rexPrefix (regLow src) am hv
      hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]

theorem xchg_m8_r8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) (src : BitVec 4)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegLockedRmwPre p r base am 1 (r.prefixByte :: encodeXchgM8R8 src am).length)
      (codeRange p (r.prefixByte :: encodeXchgM8R8 src am))
      (Effect.post (xchgMRSegEffect p (r.prefixByte :: encodeXchgM8R8 src am).length 8 base (src.setWidth 5) am)) := by
  unfold encodeXchgM8R8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec src hs
    have := xchg_m8_r8_seg_triple_of_bytes p r base (regLow src) hl am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := xchg_m8_r8_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix (regLow src) am hv
      hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem xchg_m8_r8_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4)
    (am : AddrMode) (hv : am.Valid) :
    Triple (LockedRmw32Pre p am 1 (0x67 :: encodeXchgM8R8 src am).length)
      (codeRange p (0x67 :: encodeXchgM8R8 src am))
      (Effect.post (xchgMRA32Effect p (0x67 :: encodeXchgM8R8 src am).length 8 (src.setWidth 5) am)) := by
  unfold encodeXchgM8R8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec src hs
    have := xchg_m8_r8_a32_triple_of_bytes p (regLow src) hl am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := xchg_m8_r8_rex_a32_triple_of_bytes p _ hrex.rexPrefix (regLow src) am hv
      hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

def xchgM8R8NoRexEffect (p : BitVec 64) (len : Nat) (src : BitVec 3) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := am.addr s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand 8).read s
  let y := (Operand.byteReg src).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand 8), y⟩,
      ⟨(Operand.reg (byteRegGpr src) : Operand 64),
        mergeByteReg src x ((Operand.reg (byteRegGpr src) : Operand 64).read s)⟩] }

@[simp] theorem xchgM8R8NoRexEffect_components (p : BitVec 64) (len : Nat) (src : BitVec 3)
    (am : AddrMode) (s : RamState) : (xchgM8R8NoRexEffect p len src am s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) (8 / 8), .reg (byteRegGpr src), .rip] := rfl

def xchgM8R8NoRexSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (src : BitVec 3) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := base + am.addr s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand 8).read s
  let y := (Operand.byteReg src).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand 8), y⟩,
      ⟨(Operand.reg (byteRegGpr src) : Operand 64),
        mergeByteReg src x ((Operand.reg (byteRegGpr src) : Operand 64).read s)⟩] }

@[simp] theorem xchgM8R8NoRexSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64) (src : BitVec 3)
    (am : AddrMode) (s : RamState) : (xchgM8R8NoRexSegEffect p len base src am s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) (8 / 8), .reg (byteRegGpr src), .rip] := rfl

def xchgM8R8NoRexA32Effect (p : BitVec 64) (len : Nat) (src : BitVec 3) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := am.addr32 s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand 8).read s
  let y := (Operand.byteReg src).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand 8), y⟩,
      ⟨(Operand.reg (byteRegGpr src) : Operand 64),
        mergeByteReg src x ((Operand.reg (byteRegGpr src) : Operand 64).read s)⟩] }

@[simp] theorem xchgM8R8NoRexA32Effect_components (p : BitVec 64) (len : Nat) (src : BitVec 3)
    (am : AddrMode) (s : RamState) : (xchgM8R8NoRexA32Effect p len src am s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) (8 / 8), .reg (byteRegGpr src), .rip] := rfl

theorem xchg_m8_r8_norex_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LockedRmwPre p am 1 (2 + am.tail.length))
      (codeRange p (0x86 :: am.modrm reg :: am.tail))
      (xchgM8R8NoRexEffect p (2 + am.tail.length) reg am) := by
  intro s h hcode hpre
  have hlk := lockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := xchg_m8_r8_gpr8_step s h [] (by simp)
    (by simp)
    (by rfl) (by rfl)
    (by rfl) reg am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
    (by exact hlk)
  dsimp only at hstep
  have hsrc : Operand.gpr8 (gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 reg)
      (byteRex (scanContext s.DS (PrefixSegments.ofState s) [])) = Operand.byteReg reg := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwByteResult h _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwByteResult_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_rmwByteResult s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  refine ⟨(Operand.read_afterStep_rmwByteResult_mem s _ _ _ _ _ _).trans ?_,
    (Operand.read_afterStep_rmwByteResult_reg s _ _ _ _ _ _).trans ?_⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    rfl

theorem xchg_m8_r8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LockedRmwPre p am 1 (2 + am.tail.length))
      (codeRange p (0x86 :: am.modrm reg :: am.tail))
      (Effect.post (xchgM8R8NoRexEffect p (2 + am.tail.length) reg am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgM8R8NoRexEffect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.code (by simp; omega))
    (xchg_m8_r8_norex_effect_step p reg am hv hx hb)

theorem xchg_m8_r8_norex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SegLockedRmwPre p r base am 1 (3 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x86 :: am.modrm reg :: am.tail))
      (xchgM8R8NoRexSegEffect p (3 + am.tail.length) base reg am) := by
  intro s h hcode hpre
  have hlk := segLockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := xchg_m8_r8_gpr8_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp))
    (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
    (by rw [hsc, segAddr_withSeg]; exact hlk)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : Operand.gpr8 (gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r3 reg)
      (byteRex (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)))) = Operand.byteReg reg := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwByteResult h _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwByteResult_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_rmwByteResult s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  refine ⟨(Operand.read_afterStep_rmwByteResult_mem s _ _ _ _ _ _).trans ?_,
    (Operand.read_afterStep_rmwByteResult_reg s _ _ _ _ _ _).trans ?_⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    rfl

theorem xchg_m8_r8_norex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegLockedRmwPre p r base am 1 (3 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x86 :: am.modrm reg :: am.tail))
      (Effect.post (xchgM8R8NoRexSegEffect p (3 + am.tail.length) base reg am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgM8R8NoRexSegEffect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.store.code (by simp; omega))
    (xchg_m8_r8_norex_seg_effect_step p r base reg am hv hx hb)

theorem xchg_m8_r8_norex_a32_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LockedRmw32Pre p am 1 (3 + am.tail.length))
      (codeRange p (0x67 :: 0x86 :: am.modrm reg :: am.tail))
      (xchgM8R8NoRexA32Effect p (3 + am.tail.length) reg am) := by
  intro s h hcode hpre
  have hlk := lockedRmw32_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := xchg_m8_r8_gpr8_a32_step s h [0x67] (scanPrefix_asz_cons (by simp))
    (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
    (by rw [hsc]; exact hlk)
  simp only [hsc] at hstep
  have hsrc : Operand.gpr8 (gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r3 reg)
      (byteRex (withAsz (scanContext s.DS (PrefixSegments.ofState s) []))) = Operand.byteReg reg := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwByteResult h _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwByteResult_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_rmwByteResult s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  refine ⟨(Operand.read_afterStep_rmwByteResult_mem s _ _ _ _ _ _).trans ?_,
    (Operand.read_afterStep_rmwByteResult_reg s _ _ _ _ _ _).trans ?_⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    rfl

theorem xchg_m8_r8_norex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LockedRmw32Pre p am 1 (3 + am.tail.length))
      (codeRange p (0x67 :: 0x86 :: am.modrm reg :: am.tail))
      (Effect.post (xchgM8R8NoRexA32Effect p (3 + am.tail.length) reg am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgM8R8NoRexA32Effect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.code (by simp; omega))
    (xchg_m8_r8_norex_a32_effect_step p reg am hv hx hb)

theorem xchg_m8_r8_norex_triple [Bindings] (p : BitVec 64) (src : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LockedRmwPre p am 1 (2 + am.tail.length))
      (codeRange p (encodeXchgM8R8NoRex src am))
      (Effect.post (xchgM8R8NoRexEffect p (2 + am.tail.length) src am)) :=
  xchg_m8_r8_norex_triple_of_bytes p src am hv hx hb

theorem xchg_m8_r8_norex_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegLockedRmwPre p r base am 1 (3 + am.tail.length))
      (codeRange p (r.prefixByte :: encodeXchgM8R8NoRex src am))
      (Effect.post (xchgM8R8NoRexSegEffect p (3 + am.tail.length) base src am)) :=
  xchg_m8_r8_norex_seg_triple_of_bytes p r base src am hv hx hb

theorem xchg_m8_r8_norex_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LockedRmw32Pre p am 1 (3 + am.tail.length))
      (codeRange p (0x67 :: encodeXchgM8R8NoRex src am))
      (Effect.post (xchgM8R8NoRexA32Effect p (3 + am.tail.length) src am)) :=
  xchg_m8_r8_norex_a32_triple_of_bytes p src am hv hx hb

attribute [x86_compose] xchgM8R8NoRexEffect xchgM8R8NoRexSegEffect xchgM8R8NoRexA32Effect

@[x86_local] theorem xchgM8R8NoRexEffect_local {p : BitVec 64} {len : Nat} {src : BitVec 3}
    {am : AddrMode} : Effect.Local (xchgM8R8NoRexEffect p len src am) := by
  effect_local [xchgM8R8NoRexEffect]

@[x86_local] theorem xchgM8R8NoRexSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 3} {am : AddrMode} : Effect.Local (xchgM8R8NoRexSegEffect p len base src am) := by
  effect_local [xchgM8R8NoRexSegEffect]

@[x86_local] theorem xchgM8R8NoRexA32Effect_local {p : BitVec 64} {len : Nat} {src : BitVec 3}
    {am : AddrMode} : Effect.Local (xchgM8R8NoRexA32Effect p len src am) := by
  effect_local [xchgM8R8NoRexA32Effect]

end X86Proofs
