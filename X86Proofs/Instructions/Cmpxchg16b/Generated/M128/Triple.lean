import X86Proofs.Instructions.Cmpxchg16b.Generated.M128.Step
import X86Proofs.Instructions.Cmpxchg16b.Generated.M128.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cmpxchg16bM128Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Bool) (s : RamState) :
    Effect :=
  let a := am.addr s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand 128).read s
  let rdx := (Operand.reg 2 : Operand 64).read s
  let rax := (Operand.reg 0 : Operand 64).read s
  let rep := (Operand.reg 1 : Operand 64).read s ++ (Operand.reg 3 : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand 128), if c then rep else x⟩,
      ⟨(Operand.reg 2 : Operand 64), if c then rdx else x.extractLsb' 64 64⟩,
      ⟨(Operand.reg 0 : Operand 64), if c then rax else x.setWidth 64⟩]
    flags := some (.ofStatusFlags { StatusFlags.ofRFLAGS s.RFLAGS with ZF := c }) }

@[simp] theorem cmpxchg16bM128Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (c : Bool) (s : RamState) : (cmpxchg16bM128Effect p len am c s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) (128 / 8), .reg 2, .reg 0, .flags, .rip] := rfl

def cmpxchg16bM128SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) (c : Bool)
    (s : RamState) : Effect :=
  let a := base + am.addr s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand 128).read s
  let rdx := (Operand.reg 2 : Operand 64).read s
  let rax := (Operand.reg 0 : Operand 64).read s
  let rep := (Operand.reg 1 : Operand 64).read s ++ (Operand.reg 3 : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand 128), if c then rep else x⟩,
      ⟨(Operand.reg 2 : Operand 64), if c then rdx else x.extractLsb' 64 64⟩,
      ⟨(Operand.reg 0 : Operand 64), if c then rax else x.setWidth 64⟩]
    flags := some (.ofStatusFlags { StatusFlags.ofRFLAGS s.RFLAGS with ZF := c }) }

@[simp] theorem cmpxchg16bM128SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (c : Bool) (s : RamState) :
    (cmpxchg16bM128SegEffect p len base am c s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) (128 / 8), .reg 2, .reg 0, .flags,
        .rip] := rfl

def cmpxchg16bM128A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Bool) (s : RamState) :
    Effect :=
  let a := am.addr32 s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand 128).read s
  let rdx := (Operand.reg 2 : Operand 64).read s
  let rax := (Operand.reg 0 : Operand 64).read s
  let rep := (Operand.reg 1 : Operand 64).read s ++ (Operand.reg 3 : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand 128), if c then rep else x⟩,
      ⟨(Operand.reg 2 : Operand 64), if c then rdx else x.extractLsb' 64 64⟩,
      ⟨(Operand.reg 0 : Operand 64), if c then rax else x.setWidth 64⟩]
    flags := some (.ofStatusFlags { StatusFlags.ofRFLAGS s.RFLAGS with ZF := c }) }

@[simp] theorem cmpxchg16bM128A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (c : Bool) (s : RamState) : (cmpxchg16bM128A32Effect p len am c s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) (128 / 8), .reg 2, .reg 0, .flags, .rip] := rfl

theorem cmpxchg16b_m128_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => RmwPre p am 16 (4 + am.tail.length) s ∧
      (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))).toNat % 16 = 0 ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding true ∧
      ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand 128).read s) = c)
      (codeRange p (rex :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (cmpxchg16bM128Effect p (4 + am.tail.length) am c) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hal, hcx, hc⟩
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cmpxchg16b_m128_step s h [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) hcx am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
    (by rw [scanContext_rex _ _ hr]; exact hal)
  simp only [scanContext_rex _ _ hr] at hstep
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (rexContext s.DS rex.toBitVec) (am.addrAt s (4 + am.tail.length)) =
    am.addrAt s (4 + am.tail.length) from rfl] at hstep
  cases c
  · have hne : ¬((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s) =
        (Operand.mem (am.addrAt s (4 + am.tail.length)) : Operand 128).read s :=
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
        (Operand.mem (am.addrAt s (4 + am.tail.length)) : Operand 128).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte, cmpxchg16bSpec, decide_true] at hstep
    have hsub : ∀ x ∈ [Component.mem (am.addrAt s (4 + am.tail.length)) (128 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt s (4 + am.tail.length)) (128 / 8), .reg 2, .reg 0, .flags,
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

theorem cmpxchg16b_m128_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => RmwPre p am 16 (4 + am.tail.length) s ∧
      (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))).toNat % 16 = 0 ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding true ∧
      ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand 128).read s) = c)
      (codeRange p (rex :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (Effect.post (cmpxchg16bM128Effect p (4 + am.tail.length) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchg16bM128Effect_components]; exact mem_components_rmwRegPair _ _ _ _) hpre.1.code
    (by simp; omega))
    (cmpxchg16b_m128_effect_step p rex hrex am hv hx hb c)

theorem cmpxchg16b_m128_triple [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s => RmwPre p am 16 (encodeCmpxchg16bM128 am).length s ∧
      (am.addr s (p + BitVec.ofNat 64 (encodeCmpxchg16bM128 am).length)).toNat % 16 = 0 ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding true ∧
      ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (encodeCmpxchg16bM128 am).length)) : Operand 128).read s) = c)
      (codeRange p (encodeCmpxchg16bM128 am))
      (Effect.post (cmpxchg16bM128Effect p (encodeCmpxchg16bM128 am).length am c)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  have := cmpxchg16b_m128_triple_of_bytes p _ hrex am hv hx hb c
  unfold encodeCmpxchg16bM128
  rwa [show (am.rexByte true 0 :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail).length =
    4 + am.tail.length by simp; omega]

theorem cmpxchg16b_m128_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 16 (5 + am.tail.length) s ∧
      (base + am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))).toNat % 16 = 0 ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding true ∧
      ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) : Operand 128).read s) = c)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (cmpxchg16bM128SegEffect p (5 + am.tail.length) base am c) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hal, hcx, hc⟩
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex] (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil),
      scanContext_rex _ _ hr]
  have hstep := cmpxchg16b_m128_step s h [r.prefixByte, rex]
    (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; exact hrex.rex_w s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) hcx am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
    (by rw [hsc, segAddr_withSeg]; exact hal)
  simp only [hsc, segAddr_withSeg, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.reduceAdd] at hstep
  cases c
  · have hne : ¬((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s) =
        (Operand.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) : Operand 128).read s :=
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
        (Operand.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) : Operand 128).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte, cmpxchg16bSpec, decide_true] at hstep
    have hsub : ∀ x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) (128 / 8), .flags, .rip],
        x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) (128 / 8), .reg 2, .reg 0, .flags,
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

theorem cmpxchg16b_m128_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 16 (5 + am.tail.length) s ∧
      (base + am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))).toNat % 16 = 0 ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding true ∧
      ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) : Operand 128).read s) = c)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (Effect.post (cmpxchg16bM128SegEffect p (5 + am.tail.length) base am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchg16bM128SegEffect_components]; exact mem_components_rmwRegPair _ _ _ _) hpre.1.store.code
    (by simp; omega))
    (cmpxchg16b_m128_seg_effect_step p r base rex hrex am hv hx hb c)

theorem cmpxchg16b_m128_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 16 (r.prefixByte :: encodeCmpxchg16bM128 am).length s ∧
      (base + am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeCmpxchg16bM128 am).length)).toNat % 16 = 0 ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding true ∧
      ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeCmpxchg16bM128 am).length)) : Operand 128).read s) = c)
      (codeRange p (r.prefixByte :: encodeCmpxchg16bM128 am))
      (Effect.post (cmpxchg16bM128SegEffect p (r.prefixByte :: encodeCmpxchg16bM128 am).length base am c)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  have := cmpxchg16b_m128_seg_triple_of_bytes p r base _ hrex am hv hx hb c
  unfold encodeCmpxchg16bM128
  rwa [show (r.prefixByte :: am.rexByte true 0 :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail).length =
    5 + am.tail.length by simp; omega]

theorem cmpxchg16b_m128_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => Rmw32Pre p am 16 (5 + am.tail.length) s ∧
      (am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))).toNat % 16 = 0 ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding true ∧
      ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) : Operand 128).read s) = c)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (cmpxchg16bM128A32Effect p (5 + am.tail.length) am c) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hal, hcx, hc⟩
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
  have hstep := cmpxchg16b_m128_a32_step s h [0x67, rex]
    (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; exact hrex.rex_w s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) hcx am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
    (by rw [hsc]; exact hal)
  simp only [hsc] at hstep
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (withAsz (rexContext s.DS rex.toBitVec)) (am.addrAt32 s (5 + am.tail.length)) =
    am.addrAt32 s (5 + am.tail.length) from rfl] at hstep
  cases c
  · have hne : ¬((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s) =
        (Operand.mem (am.addrAt32 s (5 + am.tail.length)) : Operand 128).read s :=
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
        (Operand.mem (am.addrAt32 s (5 + am.tail.length)) : Operand 128).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte, cmpxchg16bSpec, decide_true] at hstep
    have hsub : ∀ x ∈ [Component.mem (am.addrAt32 s (5 + am.tail.length)) (128 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt32 s (5 + am.tail.length)) (128 / 8), .reg 2, .reg 0, .flags,
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

theorem cmpxchg16b_m128_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 16 (5 + am.tail.length) s ∧
      (am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))).toNat % 16 = 0 ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding true ∧
      ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) : Operand 128).read s) = c)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (Effect.post (cmpxchg16bM128A32Effect p (5 + am.tail.length) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchg16bM128A32Effect_components]; exact mem_components_rmwRegPair _ _ _ _) hpre.1.code
    (by simp; omega))
    (cmpxchg16b_m128_a32_effect_step p rex hrex am hv hx hb c)

theorem cmpxchg16b_m128_a32_triple [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 16 (0x67 :: encodeCmpxchg16bM128 am).length s ∧
      (am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeCmpxchg16bM128 am).length)).toNat % 16 = 0 ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding true ∧
      ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeCmpxchg16bM128 am).length)) : Operand 128).read s) = c)
      (codeRange p (0x67 :: encodeCmpxchg16bM128 am))
      (Effect.post (cmpxchg16bM128A32Effect p (0x67 :: encodeCmpxchg16bM128 am).length am c)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  have := cmpxchg16b_m128_a32_triple_of_bytes p _ hrex am hv hx hb c
  unfold encodeCmpxchg16bM128
  rwa [show (0x67 :: am.rexByte true 0 :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail).length =
    5 + am.tail.length by simp; omega]

attribute [x86_compose] cmpxchg16bM128Effect cmpxchg16bM128SegEffect cmpxchg16bM128A32Effect

@[x86_local] theorem cmpxchg16bM128Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode}
    {c : Bool} :
    Effect.Local (cmpxchg16bM128Effect p len am c) := by
  effect_local [cmpxchg16bM128Effect]

@[x86_local] theorem cmpxchg16bM128SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {c : Bool} :
    Effect.Local (cmpxchg16bM128SegEffect p len base am c) := by
  effect_local [cmpxchg16bM128SegEffect]

@[x86_local] theorem cmpxchg16bM128A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode}
    {c : Bool} :
    Effect.Local (cmpxchg16bM128A32Effect p len am c) := by
  effect_local [cmpxchg16bM128A32Effect]

end X86Proofs
