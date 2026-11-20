import X86Proofs.Instructions.And.Generated.M8R8Lock.Step
import X86Proofs.Instructions.And.Generated.M8R8Lock.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose
import X86Proofs.Instructions.And.Generated.M8R8.Triple
import X86Proofs.Instructions.And.Generated.MR.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem and_lock_m8_r8_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LockedRmwPre p am 1 (3 + am.tail.length))
      (codeRange p (0xF0 :: 0x20 :: am.modrm reg :: am.tail))
      (andMREffect p (3 + am.tail.length) 8
        (gprNumber 0 0 reg) am) := by
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
  have hstep := and_lock_m8_r8_step s h [0xF0] (scanPrefix_lock_cons (by simp)) (by simp)
    (by rw [scanContext_lock_cons]; rfl) (by rw [scanContext_lock_cons]; rfl)
    (by rw [scanContext_lock_cons]; rfl) reg
    (.inr (by rw [scanContext_lock_cons]; exact gprNumber_low4 reg hreg)) am hv
    (by rw [scanContext_lock_cons]; exact ((AddrContext.legacy _ am hx hb).withLock).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_lock_cons]; exact hread)
    (by rw [scanContext_lock_cons]; exact hlk)
  simp only [scanContext_lock_cons] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem and_lock_m8_r8_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LockedRmwPre p am 1 (3 + am.tail.length))
      (codeRange p (0xF0 :: 0x20 :: am.modrm reg :: am.tail))
      (Effect.post (andMREffect p (3 + am.tail.length) 8
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [andMREffect_components]; exact mem_components_rmw _ _) hpre.rmw.code (by simp; omega))
    (and_lock_m8_r8_effect_step p reg hreg am hv hx hb)

theorem and_lock_m8_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LockedRmwPre p am 1 (4 + am.tail.length))
      (codeRange p (0xF0 :: rex :: 0x20 :: am.modrm reg :: am.tail))
      (andMREffect p (4 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode hpre
  have hlk := lockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := and_lock_m8_r8_step s h [0xF0, rex] (scanPrefix_lock_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; rfl) (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; rfl) reg
    (.inl (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; rfl)) am hv
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; exact ((AddrContext.rex _ _ am hx hb).withLock).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; exact hread)
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; exact hlk)
  simp only [scanContext_lock_cons, scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem and_lock_m8_r8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LockedRmwPre p am 1 (4 + am.tail.length))
      (codeRange p (0xF0 :: rex :: 0x20 :: am.modrm reg :: am.tail))
      (Effect.post (andMREffect p (4 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [andMREffect_components]; exact mem_components_rmw _ _) hpre.rmw.code (by simp; omega))
    (and_lock_m8_r8_rex_effect_step p rex hr reg am hv hx hb)

theorem and_lock_m8_r8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SegLockedRmwPre p r base am 1 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF0 :: 0x20 :: am.modrm reg :: am.tail))
      (andMRSegEffect p (4 + am.tail.length) 8 base
        (gprNumber 0 0 reg) am) := by
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
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF0] =
      withSeg (withLock (scanContext s.DS (PrefixSegments.ofState s) [])) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF0]
      (noSegPrefix_cons noSegPrefix_f0 noSegPrefix_nil), scanContext_lock_cons]
  have hstep := and_lock_m8_r8_step s h [r.prefixByte, 0xF0] (scanPrefix_seg_cons r (scanPrefix_lock_cons (by simp))) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inr (by rw [hsc]; exact gprNumber_low4 reg hreg)) am hv
    (by rw [hsc]; exact ((AddrContext.legacy _ am hx hb).withLock).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
    (by rw [hsc, segAddr_withSeg]; exact hlk)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem and_lock_m8_r8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegLockedRmwPre p r base am 1 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF0 :: 0x20 :: am.modrm reg :: am.tail))
      (Effect.post (andMRSegEffect p (4 + am.tail.length) 8 base
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [andMRSegEffect_components]; exact mem_components_rmw _ _) hpre.rmw.store.code (by simp; omega))
    (and_lock_m8_r8_seg_effect_step p r base reg hreg am hv hx hb)

theorem and_lock_m8_r8_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegLockedRmwPre p r base am 1 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF0 :: rex :: 0x20 :: am.modrm reg :: am.tail))
      (andMRSegEffect p (5 + am.tail.length) 8 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode hpre
  have hlk := segLockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF0, rex] =
      withSeg (withLock (rexContext s.DS rex.toBitVec)) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF0, rex]
      (noSegPrefix_cons noSegPrefix_f0 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_lock_cons, scanContext_rex _ _ hr]
  have hstep := and_lock_m8_r8_step s h [r.prefixByte, 0xF0, rex] (scanPrefix_seg_cons r (scanPrefix_lock_cons (by simpa using hr.scanPrefix))) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inl (by rw [hsc]; rfl)) am hv
    (by rw [hsc]; exact ((AddrContext.rex _ _ am hx hb).withLock).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
    (by rw [hsc, segAddr_withSeg]; exact hlk)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem and_lock_m8_r8_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegLockedRmwPre p r base am 1 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF0 :: rex :: 0x20 :: am.modrm reg :: am.tail))
      (Effect.post (andMRSegEffect p (5 + am.tail.length) 8 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [andMRSegEffect_components]; exact mem_components_rmw _ _) hpre.rmw.store.code (by simp; omega))
    (and_lock_m8_r8_rex_seg_effect_step p r base rex hr reg am hv hx hb)

theorem and_lock_m8_r8_norex_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LockedRmwPre p am 1 (3 + am.tail.length))
      (codeRange p (0xF0 :: 0x20 :: am.modrm reg :: am.tail))
      (andM8R8NoRexEffect p (3 + am.tail.length)
        reg am) := by
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
  have hstep := and_lock_m8_r8_gpr8_step s h [0xF0] (scanPrefix_lock_cons (by simp)) (by simp)
    (by rw [scanContext_lock_cons]; rfl) (by rw [scanContext_lock_cons]; rfl)
    (by rw [scanContext_lock_cons]; rfl) reg am hv
    (by rw [scanContext_lock_cons]; exact ((AddrContext.legacy _ am hx hb).withLock).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_lock_cons]; exact hread)
    (by rw [scanContext_lock_cons]; exact hlk)
  simp only [scanContext_lock_cons] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · refine (Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _).trans ?_
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem and_lock_m8_r8_norex_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LockedRmwPre p am 1 (3 + am.tail.length))
      (codeRange p (0xF0 :: 0x20 :: am.modrm reg :: am.tail))
      (Effect.post (andM8R8NoRexEffect p (3 + am.tail.length)
        reg am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [andM8R8NoRexEffect_components]; exact mem_components_rmw _ _) hpre.rmw.code (by simp; omega))
    (and_lock_m8_r8_norex_effect_step p reg am hv hx hb)

theorem and_lock_m8_r8_norex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SegLockedRmwPre p r base am 1 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF0 :: 0x20 :: am.modrm reg :: am.tail))
      (andM8R8NoRexSegEffect p (4 + am.tail.length) base
        reg am) := by
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
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF0] =
      withSeg (withLock (scanContext s.DS (PrefixSegments.ofState s) [])) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF0]
      (noSegPrefix_cons noSegPrefix_f0 noSegPrefix_nil), scanContext_lock_cons]
  have hstep := and_lock_m8_r8_gpr8_step s h [r.prefixByte, 0xF0] (scanPrefix_seg_cons r (scanPrefix_lock_cons (by simp))) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact ((AddrContext.legacy _ am hx hb).withLock).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
    (by rw [hsc, segAddr_withSeg]; exact hlk)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · refine (Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _).trans ?_
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem and_lock_m8_r8_norex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegLockedRmwPre p r base am 1 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF0 :: 0x20 :: am.modrm reg :: am.tail))
      (Effect.post (andM8R8NoRexSegEffect p (4 + am.tail.length) base
        reg am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [andM8R8NoRexSegEffect_components]; exact mem_components_rmw _ _) hpre.rmw.store.code (by simp; omega))
    (and_lock_m8_r8_norex_seg_effect_step p r base reg am hv hx hb)

theorem and_lock_m8_r8_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (LockedRmwPre p am 1 (encodeAndLockM8R8 src am).length)
      (codeRange p (encodeAndLockM8R8 src am))
      (Effect.post (andMREffect p (encodeAndLockM8R8 src am).length 8 (src.setWidth 5) am)) := by
  unfold encodeAndLockM8R8 encodeAndM8R8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec src hs
    have := and_lock_m8_r8_triple_of_bytes p (regLow src) hl am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := and_lock_m8_r8_rex_triple_of_bytes p _ hrex.rexPrefix (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem and_lock_m8_r8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (SegLockedRmwPre p r base am 1 (r.prefixByte :: encodeAndLockM8R8 src am).length)
      (codeRange p (r.prefixByte :: encodeAndLockM8R8 src am))
      (Effect.post (andMRSegEffect p (r.prefixByte :: encodeAndLockM8R8 src am).length 8 base
        (src.setWidth 5) am)) := by
  unfold encodeAndLockM8R8 encodeAndM8R8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec src hs
    have := and_lock_m8_r8_seg_triple_of_bytes p r base (regLow src) hl am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := and_lock_m8_r8_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix (regLow src) am hv
      hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

theorem and_lock_m8_r8_norex_triple [Bindings] (p : BitVec 64) (src : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LockedRmwPre p am 1 (3 + am.tail.length))
      (codeRange p (encodeAndLockM8R8NoRex src am))
      (Effect.post (andM8R8NoRexEffect p (3 + am.tail.length) src am)) :=
  and_lock_m8_r8_norex_triple_of_bytes p src am hv hx hb

theorem and_lock_m8_r8_norex_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegLockedRmwPre p r base am 1 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: encodeAndLockM8R8NoRex src am))
      (Effect.post (andM8R8NoRexSegEffect p (4 + am.tail.length) base src am)) :=
  and_lock_m8_r8_norex_seg_triple_of_bytes p r base src am hv hx hb

theorem and_lock_m8_r8_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LockedRmw32Pre p am 1 (4 + am.tail.length))
      (codeRange p (0x67 :: 0xF0 :: 0x20 :: am.modrm reg :: am.tail))
      (andMRA32Effect p (4 + am.tail.length) 8
        (gprNumber 0 0 reg) am) := by
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
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0xF0] =
      withAsz (withLock (scanContext s.DS (PrefixSegments.ofState s) [])) := by
    rw [scanContext_asz_cons, scanContext_lock_cons]
  have hstep := and_lock_m8_r8_a32_step s h [0x67, 0xF0] (scanPrefix_asz_cons (scanPrefix_lock_cons (by simp))) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inr (by rw [hsc]; exact gprNumber_low4 reg hreg)) am hv
    (by rw [hsc]; exact ((AddrContext.legacy _ am hx hb).withLock).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
    (by rw [hsc]; exact hlk)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem and_lock_m8_r8_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LockedRmw32Pre p am 1 (4 + am.tail.length))
      (codeRange p (0x67 :: 0xF0 :: 0x20 :: am.modrm reg :: am.tail))
      (Effect.post (andMRA32Effect p (4 + am.tail.length) 8
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [andMRA32Effect_components]; exact mem_components_rmw _ _) hpre.rmw.code (by simp; omega))
    (and_lock_m8_r8_a32_effect_step p reg hreg am hv hx hb)

theorem and_lock_m8_r8_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LockedRmw32Pre p am 1 (5 + am.tail.length))
      (codeRange p (0x67 :: 0xF0 :: rex :: 0x20 :: am.modrm reg :: am.tail))
      (andMRA32Effect p (5 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode hpre
  have hlk := lockedRmw32_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0xF0, rex] =
      withAsz (withLock (rexContext s.DS rex.toBitVec)) := by
    rw [scanContext_asz_cons, scanContext_lock_cons, scanContext_rex _ _ hr]
  have hstep := and_lock_m8_r8_a32_step s h [0x67, 0xF0, rex] (scanPrefix_asz_cons (scanPrefix_lock_cons (by simpa using hr.scanPrefix))) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inl (by rw [hsc]; rfl)) am hv
    (by rw [hsc]; exact ((AddrContext.rex _ _ am hx hb).withLock).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
    (by rw [hsc]; exact hlk)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem and_lock_m8_r8_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LockedRmw32Pre p am 1 (5 + am.tail.length))
      (codeRange p (0x67 :: 0xF0 :: rex :: 0x20 :: am.modrm reg :: am.tail))
      (Effect.post (andMRA32Effect p (5 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [andMRA32Effect_components]; exact mem_components_rmw _ _) hpre.rmw.code (by simp; omega))
    (and_lock_m8_r8_rex_a32_effect_step p rex hr reg am hv hx hb)

theorem and_lock_m8_r8_norex_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LockedRmw32Pre p am 1 (4 + am.tail.length))
      (codeRange p (0x67 :: 0xF0 :: 0x20 :: am.modrm reg :: am.tail))
      (andM8R8NoRexA32Effect p (4 + am.tail.length)
        reg am) := by
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
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0xF0] =
      withAsz (withLock (scanContext s.DS (PrefixSegments.ofState s) [])) := by
    rw [scanContext_asz_cons, scanContext_lock_cons]
  have hstep := and_lock_m8_r8_gpr8_a32_step s h [0x67, 0xF0] (scanPrefix_asz_cons (scanPrefix_lock_cons (by simp))) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact ((AddrContext.legacy _ am hx hb).withLock).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
    (by rw [hsc]; exact hlk)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · refine (Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _).trans ?_
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem and_lock_m8_r8_norex_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LockedRmw32Pre p am 1 (4 + am.tail.length))
      (codeRange p (0x67 :: 0xF0 :: 0x20 :: am.modrm reg :: am.tail))
      (Effect.post (andM8R8NoRexA32Effect p (4 + am.tail.length)
        reg am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [andM8R8NoRexA32Effect_components]; exact mem_components_rmw _ _) hpre.rmw.code (by simp; omega))
    (and_lock_m8_r8_norex_a32_effect_step p reg am hv hx hb)

theorem and_lock_m8_r8_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (LockedRmw32Pre p am 1 (0x67 :: encodeAndLockM8R8 src am).length)
      (codeRange p (0x67 :: encodeAndLockM8R8 src am))
      (Effect.post (andMRA32Effect p (0x67 :: encodeAndLockM8R8 src am).length 8 (src.setWidth 5) am)) := by
  unfold encodeAndLockM8R8 encodeAndM8R8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec src hs
    have := and_lock_m8_r8_a32_triple_of_bytes p (regLow src) hl am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := and_lock_m8_r8_rex_a32_triple_of_bytes p _ hrex.rexPrefix (regLow src) am hv
      hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

theorem and_lock_m8_r8_norex_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LockedRmw32Pre p am 1 (4 + am.tail.length))
      (codeRange p (0x67 :: encodeAndLockM8R8NoRex src am))
      (Effect.post (andM8R8NoRexA32Effect p (4 + am.tail.length) src am)) :=
  and_lock_m8_r8_norex_a32_triple_of_bytes p src am hv hx hb

end X86Proofs
