import X86Proofs.Instructions.Cmpxchg16b.Generated.M128Lock.Step
import X86Proofs.Instructions.Cmpxchg16b.Generated.M128Lock.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Cmpxchg16b.Generated.M128.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem cmpxchg16b_lock_m128_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => LockedRmwPre p am 16 (5 + am.tail.length) s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding true ∧
      ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) : Operand 128).read s) = c)
      (codeRange p (0xF0 :: rex :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (cmpxchg16bM128Effect p (5 + am.tail.length) am c) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hcx, hc⟩
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
  have hstep := cmpxchg16b_lock_m128_step s h [0xF0, rex]
    (scanPrefix_lock_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; rfl) (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; rfl) (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; rfl) hcx am hv
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).withLock.toSeg)
    hcode.bytesAt hlow (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; exact hread)
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; exact hlk)
  simp only [scanContext_lock_cons, scanContext_rex _ _ hr] at hstep
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (withLock (rexContext s.DS rex.toBitVec)) (am.addrAt s (5 + am.tail.length)) =
    am.addrAt s (5 + am.tail.length) from rfl] at hstep
  cases c
  · have hne : ¬((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s) =
        (Operand.mem (am.addrAt s (5 + am.tail.length)) : Operand 128).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte, cmpxchg16bSpec, decide_false] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwRegPair h _ _ _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwRegPair_rip h _ _ _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwRegPair s _ _ _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwRegPair_mem (n := 128) s _ (by decide) (by decide) _ _ _
        _ _ _ _ _, ?_, ?_⟩
      · rw [Operand.read_afterStep_rmwRegPair_reg₁ _ _ _ _ _ _ _ _ _ _ (by decide), mergeGPR_64]
        rfl
      · rw [Operand.read_afterStep_rmwRegPair_reg₂ _ _ _ _ _ _ _ _ _ _ (by decide), mergeGPR_64]
        rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s) =
        (Operand.mem (am.addrAt s (5 + am.tail.length)) : Operand 128).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte, cmpxchg16bSpec, decide_true] at hstep
    have hsub : ∀ x ∈ [Component.mem (am.addrAt s (5 + am.tail.length)) (128 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt s (5 + am.tail.length)) (128 / 8), .reg 2, .reg 0, .flags,
          .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        (AgreesExcept.afterStep_rmw s _ _ _ _ _).mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 128) s _ (by decide) (by decide) _ _ _ _,
          (AgreesExcept.afterStep_rmw s _ _ _ _ _).read (by simp),
          (AgreesExcept.afterStep_rmw s _ _ _ _ _).read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg16b_lock_m128_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => LockedRmwPre p am 16 (5 + am.tail.length) s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding true ∧
      ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) : Operand 128).read s) = c)
      (codeRange p (0xF0 :: rex :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (Effect.post (cmpxchg16bM128Effect p (5 + am.tail.length) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchg16bM128Effect_components]; exact mem_components_rmwRegPair _ _ _ _) hpre.1.rmw.code
    (by simp; omega))
    (cmpxchg16b_lock_m128_effect_step p rex hrex am hv hx hb c)

theorem cmpxchg16b_lock_m128_triple [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s => LockedRmwPre p am 16 (encodeCmpxchg16bLockM128 am).length s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding true ∧
      ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (encodeCmpxchg16bLockM128 am).length)) : Operand 128).read s) = c)
      (codeRange p (encodeCmpxchg16bLockM128 am))
      (Effect.post (cmpxchg16bM128Effect p (encodeCmpxchg16bLockM128 am).length am c)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  have := cmpxchg16b_lock_m128_triple_of_bytes p _ hrex am hv hx hb c
  unfold encodeCmpxchg16bLockM128 encodeCmpxchg16bM128
  rwa [show (0xF0 :: am.rexByte true 0 :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail).length =
    5 + am.tail.length by simp; omega]

theorem cmpxchg16b_lock_m128_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => SegLockedRmwPre p r base am 16 (6 + am.tail.length) s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding true ∧
      ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) : Operand 128).read s) = c)
      (codeRange p (r.prefixByte :: 0xF0 :: rex :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (cmpxchg16bM128SegEffect p (6 + am.tail.length) base am c) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hcx, hc⟩
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
    rw [scanContext_seg_cons _ _ r [0xF0, rex] (noSegPrefix_cons noSegPrefix_f0 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)),
      scanContext_lock_cons,
      scanContext_rex _ _ hr]
  have hstep := cmpxchg16b_lock_m128_step s h [r.prefixByte, 0xF0, rex]
    (scanPrefix_seg_cons r (scanPrefix_lock_cons (by simpa using hr.scanPrefix))) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; exact hrex.rex_w s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) hcx am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withLock.withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
    (by rw [hsc, segAddr_withSeg]; exact hlk)
  simp only [hsc, segAddr_withSeg, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.reduceAdd] at hstep
  cases c
  · have hne : ¬((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s) =
        (Operand.mem (segBase (r.read s) + am.addrAt s (6 + am.tail.length)) : Operand 128).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte, cmpxchg16bSpec, decide_false] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwRegPair h _ _ _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwRegPair_rip h _ _ _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwRegPair s _ _ _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwRegPair_mem (n := 128) s _ (by decide) (by decide) _ _ _
        _ _ _ _ _, ?_, ?_⟩
      · rw [Operand.read_afterStep_rmwRegPair_reg₁ _ _ _ _ _ _ _ _ _ _ (by decide), mergeGPR_64]
        rfl
      · rw [Operand.read_afterStep_rmwRegPair_reg₂ _ _ _ _ _ _ _ _ _ _ (by decide), mergeGPR_64]
        rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s) =
        (Operand.mem (segBase (r.read s) + am.addrAt s (6 + am.tail.length)) : Operand 128).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte, cmpxchg16bSpec, decide_true] at hstep
    have hsub : ∀ x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (6 + am.tail.length)) (128 / 8), .flags, .rip],
        x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (6 + am.tail.length)) (128 / 8), .reg 2, .reg 0, .flags,
          .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        (AgreesExcept.afterStep_rmw s _ _ _ _ _).mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 128) s _ (by decide) (by decide) _ _ _ _,
          (AgreesExcept.afterStep_rmw s _ _ _ _ _).read (by simp),
          (AgreesExcept.afterStep_rmw s _ _ _ _ _).read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg16b_lock_m128_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => SegLockedRmwPre p r base am 16 (6 + am.tail.length) s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding true ∧
      ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) : Operand 128).read s) = c)
      (codeRange p (r.prefixByte :: 0xF0 :: rex :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (Effect.post (cmpxchg16bM128SegEffect p (6 + am.tail.length) base am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchg16bM128SegEffect_components]; exact mem_components_rmwRegPair _ _ _ _) hpre.1.rmw.store.code
    (by simp; omega))
    (cmpxchg16b_lock_m128_seg_effect_step p r base rex hrex am hv hx hb c)

theorem cmpxchg16b_lock_m128_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s => SegLockedRmwPre p r base am 16 (r.prefixByte :: encodeCmpxchg16bLockM128 am).length s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding true ∧
      ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeCmpxchg16bLockM128 am).length)) : Operand 128).read s) = c)
      (codeRange p (r.prefixByte :: encodeCmpxchg16bLockM128 am))
      (Effect.post (cmpxchg16bM128SegEffect p (r.prefixByte :: encodeCmpxchg16bLockM128 am).length base am c)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  have := cmpxchg16b_lock_m128_seg_triple_of_bytes p r base _ hrex am hv hx hb c
  unfold encodeCmpxchg16bLockM128 encodeCmpxchg16bM128
  rwa [show (r.prefixByte :: 0xF0 :: am.rexByte true 0 :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail).length =
    6 + am.tail.length by simp; omega]

theorem cmpxchg16b_lock_m128_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => LockedRmw32Pre p am 16 (6 + am.tail.length) s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding true ∧
      ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) : Operand 128).read s) = c)
      (codeRange p (0x67 :: 0xF0 :: rex :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (cmpxchg16bM128A32Effect p (6 + am.tail.length) am c) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hcx, hc⟩
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
  have hstep := cmpxchg16b_lock_m128_a32_step s h [0x67, 0xF0, rex]
    (scanPrefix_asz_cons (scanPrefix_lock_cons (by simpa using hr.scanPrefix))) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; exact hrex.rex_w s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) hcx am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withLock.toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
    (by rw [hsc]; exact hlk)
  simp only [hsc] at hstep
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (withAsz (withLock (rexContext s.DS rex.toBitVec))) (am.addrAt32 s (6 + am.tail.length)) =
    am.addrAt32 s (6 + am.tail.length) from rfl] at hstep
  cases c
  · have hne : ¬((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s) =
        (Operand.mem (am.addrAt32 s (6 + am.tail.length)) : Operand 128).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte, cmpxchg16bSpec, decide_false] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwRegPair h _ _ _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwRegPair_rip h _ _ _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwRegPair s _ _ _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwRegPair_mem (n := 128) s _ (by decide) (by decide) _ _ _
        _ _ _ _ _, ?_, ?_⟩
      · rw [Operand.read_afterStep_rmwRegPair_reg₁ _ _ _ _ _ _ _ _ _ _ (by decide), mergeGPR_64]
        rfl
      · rw [Operand.read_afterStep_rmwRegPair_reg₂ _ _ _ _ _ _ _ _ _ _ (by decide), mergeGPR_64]
        rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s) =
        (Operand.mem (am.addrAt32 s (6 + am.tail.length)) : Operand 128).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte, cmpxchg16bSpec, decide_true] at hstep
    have hsub : ∀ x ∈ [Component.mem (am.addrAt32 s (6 + am.tail.length)) (128 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt32 s (6 + am.tail.length)) (128 / 8), .reg 2, .reg 0, .flags,
          .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        (AgreesExcept.afterStep_rmw s _ _ _ _ _).mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 128) s _ (by decide) (by decide) _ _ _ _,
          (AgreesExcept.afterStep_rmw s _ _ _ _ _).read (by simp),
          (AgreesExcept.afterStep_rmw s _ _ _ _ _).read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg16b_lock_m128_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => LockedRmw32Pre p am 16 (6 + am.tail.length) s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding true ∧
      ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) : Operand 128).read s) = c)
      (codeRange p (0x67 :: 0xF0 :: rex :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (Effect.post (cmpxchg16bM128A32Effect p (6 + am.tail.length) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchg16bM128A32Effect_components]; exact mem_components_rmwRegPair _ _ _ _) hpre.1.rmw.code
    (by simp; omega))
    (cmpxchg16b_lock_m128_a32_effect_step p rex hrex am hv hx hb c)

theorem cmpxchg16b_lock_m128_a32_triple [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s => LockedRmw32Pre p am 16 (0x67 :: encodeCmpxchg16bLockM128 am).length s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding true ∧
      ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeCmpxchg16bLockM128 am).length)) : Operand 128).read s) = c)
      (codeRange p (0x67 :: encodeCmpxchg16bLockM128 am))
      (Effect.post (cmpxchg16bM128A32Effect p (0x67 :: encodeCmpxchg16bLockM128 am).length am c)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  have := cmpxchg16b_lock_m128_a32_triple_of_bytes p _ hrex am hv hx hb c
  unfold encodeCmpxchg16bLockM128 encodeCmpxchg16bM128
  rwa [show (0x67 :: 0xF0 :: am.rexByte true 0 :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail).length =
    6 + am.tail.length by simp; omega]

end X86Proofs
