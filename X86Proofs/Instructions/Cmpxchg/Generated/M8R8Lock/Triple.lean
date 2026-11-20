import X86Proofs.Instructions.Cmpxchg.Generated.M8R8Lock.Step
import X86Proofs.Instructions.Cmpxchg.Generated.M8R8Lock.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Cmpxchg.Generated.MR.Triple
import X86Proofs.Instructions.Cmpxchg.Generated.M8R8.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem cmpxchg_lock_m8_r8_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => LockedRmwPre p am 1 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0xF0 :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (cmpxchgMREffect p (4 + am.tail.length) 8
        (gprNumber 0 0 reg) am c) := by
  intro s h hcode ⟨hpre, hc⟩
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
  have hstep := cmpxchg_lock_m8_r8_step s h [0xF0] (scanPrefix_lock_cons (by simp))
    (by simp)
    (by rw [scanContext_lock_cons]; rfl) (by rw [scanContext_lock_cons]; rfl)
    (by rw [scanContext_lock_cons]; rfl) reg
    (.inr (by rw [scanContext_lock_cons]; exact gprNumber_low4 reg hreg)) am hv
    (by rw [scanContext_lock_cons]; exact ((AddrContext.legacy _ am hx hb).withLock).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_lock_cons]; exact hread)
    (by rw [scanContext_lock_cons]; exact hlk)
  simp only [scanContext_lock_cons] at hstep
  have hsrc : gprNumber (withLock (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r4
      (withLock (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (withLock (scanContext s.DS (PrefixSegments.ofState s) [])) (am.addrAt s (4 + am.tail.length)) = am.addrAt s (4 + am.tail.length) from rfl]
    at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 8).read s =
        (Operand.mem (am.addrAt s (4 + am.tail.length)) : Operand 8).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 8) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 8).read s =
        (Operand.mem (am.addrAt s (4 + am.tail.length)) : Operand 8).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (4 + am.tail.length) (n := 8)
      (am.addrAt s (4 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 0 reg) : Operand 8).read s,
        cmpSpec ((Operand.reg 0 : Operand 8).read s)
          ((Operand.mem (am.addrAt s (4 + am.tail.length)) : Operand 8).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (am.addrAt s (4 + am.tail.length)) (8 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt s (4 + am.tail.length)) (8 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_lock_m8_r8_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => LockedRmwPre p am 1 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0xF0 :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMREffect p (4 + am.tail.length) 8
        (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMREffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.rmw.code
    (by simp; omega))
    (cmpxchg_lock_m8_r8_effect_step p reg hreg am hv hx hb c)

theorem cmpxchg_lock_m8_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => LockedRmwPre p am 1 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0xF0 :: rex :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (cmpxchgMREffect p (5 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  intro s h hcode ⟨hpre, hc⟩
  have hlk := lockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cmpxchg_lock_m8_r8_step s h [0xF0, rex] (scanPrefix_lock_cons (by simpa using hr.scanPrefix))
    (by simp)
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; rfl) (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; rfl) reg
    (.inl (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; rfl)) am hv
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; exact ((AddrContext.rex _ _ am hx hb).withLock).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; exact hread)
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; exact hlk)
  simp only [scanContext_lock_cons, scanContext_rex _ _ hr] at hstep
  have hsrc : gprNumber (withLock (rexContext s.DS rex.toBitVec)).rex_r4
      (withLock (rexContext s.DS rex.toBitVec)).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (withLock (rexContext s.DS rex.toBitVec)) (am.addrAt s (5 + am.tail.length)) = am.addrAt s (5 + am.tail.length) from rfl]
    at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 8).read s =
        (Operand.mem (am.addrAt s (5 + am.tail.length)) : Operand 8).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 8) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 8).read s =
        (Operand.mem (am.addrAt s (5 + am.tail.length)) : Operand 8).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (5 + am.tail.length) (n := 8)
      (am.addrAt s (5 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 8).read s,
        cmpSpec ((Operand.reg 0 : Operand 8).read s)
          ((Operand.mem (am.addrAt s (5 + am.tail.length)) : Operand 8).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (5 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (am.addrAt s (5 + am.tail.length)) (8 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt s (5 + am.tail.length)) (8 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_lock_m8_r8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => LockedRmwPre p am 1 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0xF0 :: rex :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMREffect p (5 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMREffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.rmw.code
    (by simp; omega))
    (cmpxchg_lock_m8_r8_rex_effect_step p rex hr reg am hv hx hb c)

theorem cmpxchg_lock_m8_r8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => SegLockedRmwPre p r base am 1 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (r.prefixByte :: 0xF0 :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (cmpxchgMRSegEffect p (5 + am.tail.length) 8 base
        (gprNumber 0 0 reg) am c) := by
  intro s h hcode ⟨hpre, hc⟩
  have hlk := segLockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF0] =
      withSeg (withLock (scanContext s.DS (PrefixSegments.ofState s) [])) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF0]
      (noSegPrefix_cons noSegPrefix_f0 noSegPrefix_nil), scanContext_lock_cons]
  have hstep := cmpxchg_lock_m8_r8_step s h [r.prefixByte, 0xF0] (scanPrefix_seg_cons r (scanPrefix_lock_cons (by simp)))
    (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inr (by rw [hsc]; exact gprNumber_low4 reg hreg)) am hv
    (by rw [hsc]; exact ((AddrContext.legacy _ am hx hb).withLock).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
    (by rw [hsc, segAddr_withSeg]; exact hlk)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (withLock (scanContext s.DS (PrefixSegments.ofState s) [])) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (withLock (scanContext s.DS (PrefixSegments.ofState s) [])) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 8).read s =
        (Operand.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) : Operand 8).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 8) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 8).read s =
        (Operand.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) : Operand 8).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (5 + am.tail.length) (n := 8)
      (segBase (r.read s) + am.addrAt s (5 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 0 reg) : Operand 8).read s,
        cmpSpec ((Operand.reg 0 : Operand 8).read s)
          ((Operand.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) : Operand 8).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (5 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) (8 / 8), .flags, .rip],
        x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) (8 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_lock_m8_r8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => SegLockedRmwPre p r base am 1 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (r.prefixByte :: 0xF0 :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMRSegEffect p (5 + am.tail.length) 8 base
        (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMRSegEffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.rmw.store.code
    (by simp; omega))
    (cmpxchg_lock_m8_r8_seg_effect_step p r base reg hreg am hv hx hb c)

theorem cmpxchg_lock_m8_r8_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => SegLockedRmwPre p r base am 1 (6 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (r.prefixByte :: 0xF0 :: rex :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (cmpxchgMRSegEffect p (6 + am.tail.length) 8 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  intro s h hcode ⟨hpre, hc⟩
  have hlk := segLockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF0, rex] =
      withSeg (withLock (rexContext s.DS rex.toBitVec)) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF0, rex]
      (noSegPrefix_cons noSegPrefix_f0 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_lock_cons, scanContext_rex _ _ hr]
  have hstep := cmpxchg_lock_m8_r8_step s h [r.prefixByte, 0xF0, rex] (scanPrefix_seg_cons r (scanPrefix_lock_cons (by simpa using hr.scanPrefix)))
    (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inl (by rw [hsc]; rfl)) am hv
    (by rw [hsc]; exact ((AddrContext.rex _ _ am hx hb).withLock).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
    (by rw [hsc, segAddr_withSeg]; exact hlk)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (withLock (rexContext s.DS rex.toBitVec)) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (withLock (rexContext s.DS rex.toBitVec)) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 8).read s =
        (Operand.mem (segBase (r.read s) + am.addrAt s (6 + am.tail.length)) : Operand 8).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 8) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 8).read s =
        (Operand.mem (segBase (r.read s) + am.addrAt s (6 + am.tail.length)) : Operand 8).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (6 + am.tail.length) (n := 8)
      (segBase (r.read s) + am.addrAt s (6 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 8).read s,
        cmpSpec ((Operand.reg 0 : Operand 8).read s)
          ((Operand.mem (segBase (r.read s) + am.addrAt s (6 + am.tail.length)) : Operand 8).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (6 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (6 + am.tail.length)) (8 / 8), .flags, .rip],
        x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (6 + am.tail.length)) (8 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_lock_m8_r8_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => SegLockedRmwPre p r base am 1 (6 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (r.prefixByte :: 0xF0 :: rex :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMRSegEffect p (6 + am.tail.length) 8 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMRSegEffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.rmw.store.code
    (by simp; omega))
    (cmpxchg_lock_m8_r8_rex_seg_effect_step p r base rex hr reg am hv hx hb c)

theorem cmpxchg_lock_m8_r8_norex_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => LockedRmwPre p am 1 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0xF0 :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (cmpxchgM8R8NoRexEffect p (4 + am.tail.length)
        reg am c) := by
  intro s h hcode ⟨hpre, hc⟩
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
  have hstep := cmpxchg_lock_m8_r8_gpr8_step s h [0xF0] (scanPrefix_lock_cons (by simp))
    (by simp)
    (by rw [scanContext_lock_cons]; rfl) (by rw [scanContext_lock_cons]; rfl)
    (by rw [scanContext_lock_cons]; rfl) reg am hv
    (by rw [scanContext_lock_cons]; exact ((AddrContext.legacy _ am hx hb).withLock).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_lock_cons]; exact hread)
    (by rw [scanContext_lock_cons]; exact hlk)
  simp only [scanContext_lock_cons] at hstep
  have hsrc : Operand.gpr8 (gprNumber (withLock (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r4
      (withLock (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r3 reg)
      (byteRex (withLock (scanContext s.DS (PrefixSegments.ofState s) []))) = Operand.byteReg reg := rfl
  rw [hsrc] at hstep
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (withLock (scanContext s.DS (PrefixSegments.ofState s) [])) (am.addrAt s (4 + am.tail.length)) = am.addrAt s (4 + am.tail.length) from rfl]
    at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 8).read s =
        (Operand.mem (am.addrAt s (4 + am.tail.length)) : Operand 8).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 8) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 8).read s =
        (Operand.mem (am.addrAt s (4 + am.tail.length)) : Operand 8).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (4 + am.tail.length) (n := 8)
      (am.addrAt s (4 + am.tail.length))
      (fun _ => ((Operand.byteReg reg).read s,
        cmpSpec ((Operand.reg 0 : Operand 8).read s)
          ((Operand.mem (am.addrAt s (4 + am.tail.length)) : Operand 8).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (am.addrAt s (4 + am.tail.length)) (8 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt s (4 + am.tail.length)) (8 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_lock_m8_r8_norex_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => LockedRmwPre p am 1 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0xF0 :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgM8R8NoRexEffect p (4 + am.tail.length)
        reg am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgM8R8NoRexEffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.rmw.code
    (by simp; omega))
    (cmpxchg_lock_m8_r8_norex_effect_step p reg am hv hx hb c)

theorem cmpxchg_lock_m8_r8_norex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => SegLockedRmwPre p r base am 1 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (r.prefixByte :: 0xF0 :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (cmpxchgM8R8NoRexSegEffect p (5 + am.tail.length) base
        reg am c) := by
  intro s h hcode ⟨hpre, hc⟩
  have hlk := segLockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF0] =
      withSeg (withLock (scanContext s.DS (PrefixSegments.ofState s) [])) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF0]
      (noSegPrefix_cons noSegPrefix_f0 noSegPrefix_nil), scanContext_lock_cons]
  have hstep := cmpxchg_lock_m8_r8_gpr8_step s h [r.prefixByte, 0xF0] (scanPrefix_seg_cons r (scanPrefix_lock_cons (by simp)))
    (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact ((AddrContext.legacy _ am hx hb).withLock).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
    (by rw [hsc, segAddr_withSeg]; exact hlk)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : Operand.gpr8 (gprNumber (withSeg (withLock (scanContext s.DS (PrefixSegments.ofState s) [])) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (withLock (scanContext s.DS (PrefixSegments.ofState s) [])) (r.select (PrefixSegments.ofState s))).rex_r3 reg)
      (byteRex (withSeg (withLock (scanContext s.DS (PrefixSegments.ofState s) [])) (r.select (PrefixSegments.ofState s)))) = Operand.byteReg reg := rfl
  rw [hsrc] at hstep
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 8).read s =
        (Operand.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) : Operand 8).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 8) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 8).read s =
        (Operand.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) : Operand 8).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (5 + am.tail.length) (n := 8)
      (segBase (r.read s) + am.addrAt s (5 + am.tail.length))
      (fun _ => ((Operand.byteReg reg).read s,
        cmpSpec ((Operand.reg 0 : Operand 8).read s)
          ((Operand.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) : Operand 8).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (5 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) (8 / 8), .flags, .rip],
        x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) (8 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_lock_m8_r8_norex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => SegLockedRmwPre p r base am 1 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (r.prefixByte :: 0xF0 :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgM8R8NoRexSegEffect p (5 + am.tail.length) base
        reg am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgM8R8NoRexSegEffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.rmw.store.code
    (by simp; omega))
    (cmpxchg_lock_m8_r8_norex_seg_effect_step p r base reg am hv hx hb c)

theorem cmpxchg_lock_m8_r8_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => LockedRmw32Pre p am 1 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0x67 :: 0xF0 :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (cmpxchgMRA32Effect p (5 + am.tail.length) 8
        (gprNumber 0 0 reg) am c) := by
  intro s h hcode ⟨hpre, hc⟩
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
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0xF0] =
      withAsz (withLock (scanContext s.DS (PrefixSegments.ofState s) [])) := by
    rw [scanContext_asz_cons, scanContext_lock_cons]
  have hstep := cmpxchg_lock_m8_r8_a32_step s h [0x67, 0xF0] (scanPrefix_asz_cons (scanPrefix_lock_cons (by simp)))
    (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inr (by rw [hsc]; exact gprNumber_low4 reg hreg)) am hv
    (by rw [hsc]; exact ((AddrContext.legacy _ am hx hb).withLock).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
    (by rw [hsc]; exact hlk)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (withLock (scanContext s.DS (PrefixSegments.ofState s) []))).rex_r4
      (withAsz (withLock (scanContext s.DS (PrefixSegments.ofState s) []))).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (withAsz (withLock (scanContext s.DS (PrefixSegments.ofState s) []))) (am.addrAt32 s (5 + am.tail.length)) = am.addrAt32 s (5 + am.tail.length) from rfl]
    at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 8).read s =
        (Operand.mem (am.addrAt32 s (5 + am.tail.length)) : Operand 8).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 8) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 8).read s =
        (Operand.mem (am.addrAt32 s (5 + am.tail.length)) : Operand 8).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (5 + am.tail.length) (n := 8)
      (am.addrAt32 s (5 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 0 reg) : Operand 8).read s,
        cmpSpec ((Operand.reg 0 : Operand 8).read s)
          ((Operand.mem (am.addrAt32 s (5 + am.tail.length)) : Operand 8).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (5 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (am.addrAt32 s (5 + am.tail.length)) (8 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt32 s (5 + am.tail.length)) (8 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_lock_m8_r8_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => LockedRmw32Pre p am 1 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0x67 :: 0xF0 :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMRA32Effect p (5 + am.tail.length) 8
        (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMRA32Effect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.rmw.code
    (by simp; omega))
    (cmpxchg_lock_m8_r8_a32_effect_step p reg hreg am hv hx hb c)

theorem cmpxchg_lock_m8_r8_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => LockedRmw32Pre p am 1 (6 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0x67 :: 0xF0 :: rex :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (cmpxchgMRA32Effect p (6 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  intro s h hcode ⟨hpre, hc⟩
  have hlk := lockedRmw32_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0xF0, rex] =
      withAsz (withLock (rexContext s.DS rex.toBitVec)) := by
    rw [scanContext_asz_cons, scanContext_lock_cons, scanContext_rex _ _ hr]
  have hstep := cmpxchg_lock_m8_r8_a32_step s h [0x67, 0xF0, rex] (scanPrefix_asz_cons (scanPrefix_lock_cons (by simpa using hr.scanPrefix)))
    (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inl (by rw [hsc]; rfl)) am hv
    (by rw [hsc]; exact ((AddrContext.rex _ _ am hx hb).withLock).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
    (by rw [hsc]; exact hlk)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (withLock (rexContext s.DS rex.toBitVec))).rex_r4
      (withAsz (withLock (rexContext s.DS rex.toBitVec))).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (withAsz (withLock (rexContext s.DS rex.toBitVec))) (am.addrAt32 s (6 + am.tail.length)) = am.addrAt32 s (6 + am.tail.length) from rfl]
    at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 8).read s =
        (Operand.mem (am.addrAt32 s (6 + am.tail.length)) : Operand 8).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 8) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 8).read s =
        (Operand.mem (am.addrAt32 s (6 + am.tail.length)) : Operand 8).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (6 + am.tail.length) (n := 8)
      (am.addrAt32 s (6 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 8).read s,
        cmpSpec ((Operand.reg 0 : Operand 8).read s)
          ((Operand.mem (am.addrAt32 s (6 + am.tail.length)) : Operand 8).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (6 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (am.addrAt32 s (6 + am.tail.length)) (8 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt32 s (6 + am.tail.length)) (8 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_lock_m8_r8_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => LockedRmw32Pre p am 1 (6 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0x67 :: 0xF0 :: rex :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMRA32Effect p (6 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMRA32Effect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.rmw.code
    (by simp; omega))
    (cmpxchg_lock_m8_r8_rex_a32_effect_step p rex hr reg am hv hx hb c)

theorem cmpxchg_lock_m8_r8_norex_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => LockedRmw32Pre p am 1 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0x67 :: 0xF0 :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (cmpxchgM8R8NoRexA32Effect p (5 + am.tail.length)
        reg am c) := by
  intro s h hcode ⟨hpre, hc⟩
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
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0xF0] =
      withAsz (withLock (scanContext s.DS (PrefixSegments.ofState s) [])) := by
    rw [scanContext_asz_cons, scanContext_lock_cons]
  have hstep := cmpxchg_lock_m8_r8_gpr8_a32_step s h [0x67, 0xF0] (scanPrefix_asz_cons (scanPrefix_lock_cons (by simp)))
    (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact ((AddrContext.legacy _ am hx hb).withLock).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
    (by rw [hsc]; exact hlk)
  simp only [hsc] at hstep
  have hsrc : Operand.gpr8 (gprNumber (withAsz (withLock (scanContext s.DS (PrefixSegments.ofState s) []))).rex_r4
      (withAsz (withLock (scanContext s.DS (PrefixSegments.ofState s) []))).rex_r3 reg)
      (byteRex (withAsz (withLock (scanContext s.DS (PrefixSegments.ofState s) [])))) = Operand.byteReg reg := rfl
  rw [hsrc] at hstep
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (withAsz (withLock (scanContext s.DS (PrefixSegments.ofState s) []))) (am.addrAt32 s (5 + am.tail.length)) = am.addrAt32 s (5 + am.tail.length) from rfl]
    at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 8).read s =
        (Operand.mem (am.addrAt32 s (5 + am.tail.length)) : Operand 8).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 8) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 8).read s =
        (Operand.mem (am.addrAt32 s (5 + am.tail.length)) : Operand 8).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (5 + am.tail.length) (n := 8)
      (am.addrAt32 s (5 + am.tail.length))
      (fun _ => ((Operand.byteReg reg).read s,
        cmpSpec ((Operand.reg 0 : Operand 8).read s)
          ((Operand.mem (am.addrAt32 s (5 + am.tail.length)) : Operand 8).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (5 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (am.addrAt32 s (5 + am.tail.length)) (8 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt32 s (5 + am.tail.length)) (8 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_lock_m8_r8_norex_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => LockedRmw32Pre p am 1 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0x67 :: 0xF0 :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgM8R8NoRexA32Effect p (5 + am.tail.length)
        reg am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgM8R8NoRexA32Effect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.rmw.code
    (by simp; omega))
    (cmpxchg_lock_m8_r8_norex_a32_effect_step p reg am hv hx hb c)

theorem cmpxchg_lock_m8_r8_norex_triple [Bindings] (p : BitVec 64) (src : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => LockedRmwPre p am 1 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (encodeCmpxchgLockM8R8NoRex src am))
      (Effect.post (cmpxchgM8R8NoRexEffect p (4 + am.tail.length) src am c)) :=
  cmpxchg_lock_m8_r8_norex_triple_of_bytes p src am hv hx hb c

theorem cmpxchg_lock_m8_r8_norex_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => SegLockedRmwPre p r base am 1 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (r.prefixByte :: encodeCmpxchgLockM8R8NoRex src am))
      (Effect.post (cmpxchgM8R8NoRexSegEffect p (5 + am.tail.length) base src am c)) :=
  cmpxchg_lock_m8_r8_norex_seg_triple_of_bytes p r base src am hv hx hb c

theorem cmpxchg_lock_m8_r8_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (c : Bool) :
    Triple (fun s => LockedRmwPre p am 1 (encodeCmpxchgLockM8R8 src am).length s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (encodeCmpxchgLockM8R8 src am).length)) :
          Operand 8).read s) = c)
      (codeRange p (encodeCmpxchgLockM8R8 src am))
      (Effect.post
        (cmpxchgMREffect p (encodeCmpxchgLockM8R8 src am).length 8 (src.setWidth 5) am c)) := by
  unfold encodeCmpxchgLockM8R8 encodeCmpxchgM8R8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec src hs
    have := cmpxchg_lock_m8_r8_triple_of_bytes p (regLow src) hl am hv hx hb c
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := cmpxchg_lock_m8_r8_rex_triple_of_bytes p _ hrex.rexPrefix (regLow src) am hv hx hb c
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

theorem cmpxchg_lock_m8_r8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s => SegLockedRmwPre p r base am 1 (r.prefixByte :: encodeCmpxchgLockM8R8 src am).length s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeCmpxchgLockM8R8 src am).length)) :
          Operand 8).read s) = c)
      (codeRange p (r.prefixByte :: encodeCmpxchgLockM8R8 src am))
      (Effect.post (cmpxchgMRSegEffect p (r.prefixByte :: encodeCmpxchgLockM8R8 src am).length 8 base
        (src.setWidth 5) am c)) := by
  unfold encodeCmpxchgLockM8R8 encodeCmpxchgM8R8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec src hs
    have := cmpxchg_lock_m8_r8_seg_triple_of_bytes p r base (regLow src) hl am hv hx hb c
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := cmpxchg_lock_m8_r8_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix (regLow src) am
      hv hx hb c
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 + 1 = 6 + am.tail.length by omega]

theorem cmpxchg_lock_m8_r8_norex_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => LockedRmw32Pre p am 1 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0x67 :: encodeCmpxchgLockM8R8NoRex src am))
      (Effect.post (cmpxchgM8R8NoRexA32Effect p (5 + am.tail.length) src am c)) :=
  cmpxchg_lock_m8_r8_norex_a32_triple_of_bytes p src am hv hx hb c

theorem cmpxchg_lock_m8_r8_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (c : Bool) :
    Triple (fun s => LockedRmw32Pre p am 1 (0x67 :: encodeCmpxchgLockM8R8 src am).length s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeCmpxchgLockM8R8 src am).length)) :
          Operand 8).read s) = c)
      (codeRange p (0x67 :: encodeCmpxchgLockM8R8 src am))
      (Effect.post
        (cmpxchgMRA32Effect p (0x67 :: encodeCmpxchgLockM8R8 src am).length 8 (src.setWidth 5) am c)) := by
  unfold encodeCmpxchgLockM8R8 encodeCmpxchgM8R8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec src hs
    have := cmpxchg_lock_m8_r8_a32_triple_of_bytes p (regLow src) hl am hv hx hb c
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := cmpxchg_lock_m8_r8_rex_a32_triple_of_bytes p _ hrex.rexPrefix (regLow src) am hv hx
      hb c
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 + 1 = 6 + am.tail.length by omega]

end X86Proofs
