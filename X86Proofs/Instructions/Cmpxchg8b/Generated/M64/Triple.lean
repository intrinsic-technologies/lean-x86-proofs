import X86Proofs.Instructions.Cmpxchg8b.Generated.M64.Step
import X86Proofs.Instructions.Cmpxchg8b.Generated.M64.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cmpxchg8bM64Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Bool) (s : RamState) :
    Effect :=
  let a := am.addr s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand 64).read s
  let rdx := (Operand.reg 2 : Operand 64).read s
  let rax := (Operand.reg 0 : Operand 64).read s
  let rep := concat32 ((Operand.reg 1 : Operand 64).read s) ((Operand.reg 3 : Operand 64).read s)
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand 64), if c then rep else x⟩,
      ⟨(Operand.reg 2 : Operand 64), if c then rdx else (x.extractLsb' 32 32).setWidth 64⟩,
      ⟨(Operand.reg 0 : Operand 64), if c then rax else (x.setWidth 32).setWidth 64⟩]
    flags := some (.ofStatusFlags { StatusFlags.ofRFLAGS s.RFLAGS with ZF := c }) }

@[simp] theorem cmpxchg8bM64Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (c : Bool) (s : RamState) : (cmpxchg8bM64Effect p len am c s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) (64 / 8), .reg 2, .reg 0, .flags, .rip] := rfl

def cmpxchg8bM64SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) (c : Bool)
    (s : RamState) : Effect :=
  let a := base + am.addr s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand 64).read s
  let rdx := (Operand.reg 2 : Operand 64).read s
  let rax := (Operand.reg 0 : Operand 64).read s
  let rep := concat32 ((Operand.reg 1 : Operand 64).read s) ((Operand.reg 3 : Operand 64).read s)
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand 64), if c then rep else x⟩,
      ⟨(Operand.reg 2 : Operand 64), if c then rdx else (x.extractLsb' 32 32).setWidth 64⟩,
      ⟨(Operand.reg 0 : Operand 64), if c then rax else (x.setWidth 32).setWidth 64⟩]
    flags := some (.ofStatusFlags { StatusFlags.ofRFLAGS s.RFLAGS with ZF := c }) }

@[simp] theorem cmpxchg8bM64SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (c : Bool) (s : RamState) :
    (cmpxchg8bM64SegEffect p len base am c s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) (64 / 8), .reg 2, .reg 0, .flags,
        .rip] := rfl

def cmpxchg8bM64A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Bool) (s : RamState) :
    Effect :=
  let a := am.addr32 s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand 64).read s
  let rdx := (Operand.reg 2 : Operand 64).read s
  let rax := (Operand.reg 0 : Operand 64).read s
  let rep := concat32 ((Operand.reg 1 : Operand 64).read s) ((Operand.reg 3 : Operand 64).read s)
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand 64), if c then rep else x⟩,
      ⟨(Operand.reg 2 : Operand 64), if c then rdx else (x.extractLsb' 32 32).setWidth 64⟩,
      ⟨(Operand.reg 0 : Operand 64), if c then rax else (x.setWidth 32).setWidth 64⟩]
    flags := some (.ofStatusFlags { StatusFlags.ofRFLAGS s.RFLAGS with ZF := c }) }

@[simp] theorem cmpxchg8bM64A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (c : Bool) (s : RamState) : (cmpxchg8bM64A32Effect p len am c s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) (64 / 8), .reg 2, .reg 0, .flags, .rip] := rfl

theorem cmpxchg8b_m64_effect_step [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => RmwPre p am 8 (3 + am.tail.length) s ∧
      (concat32 ((Operand.reg 2 : Operand 64).read s) ((Operand.reg 0 : Operand 64).read s) ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) :
          Operand 64).read s) = c)
      (codeRange p (0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (cmpxchg8bM64Effect p (3 + am.tail.length) am c) := by
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cmpxchg8b_m64_step s h []
    (by simp) (by simp)
    (by rfl) (by rfl)
    (by rfl) (by rfl) am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  simp only [List.length_nil, Nat.zero_add] at hstep
  rw [show segAddr (scanContext s.DS (PrefixSegments.ofState s) []) (am.addrAt s (3 + am.tail.length)) =
    am.addrAt s (3 + am.tail.length) from rfl] at hstep
  cases c
  · have hne : ¬concat32 ((Operand.reg 2 : Operand 64).read s)
        ((Operand.reg 0 : Operand 64).read s) =
        (Operand.mem (am.addrAt s (3 + am.tail.length)) : Operand 64).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte, cmpxchg8bSpec, decide_false] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwRegPair h _ _ _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwRegPair_rip h _ _ _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwRegPair s _ _ _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwRegPair_mem (n := 64) s _ (by decide) (by decide) _ _ _ _
        _ _ _ _, ?_, ?_⟩
      · rw [Operand.read_afterStep_rmwRegPair_reg₁ _ _ _ _ _ _ _ _ _ _ (by decide)]
        rfl
      · rw [Operand.read_afterStep_rmwRegPair_reg₂ _ _ _ _ _ _ _ _ _ _ (by decide)]
        rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : concat32 ((Operand.reg 2 : Operand 64).read s)
        ((Operand.reg 0 : Operand 64).read s) =
        (Operand.mem (am.addrAt s (3 + am.tail.length)) : Operand 64).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte, cmpxchg8bSpec, decide_true] at hstep
    have hsub : ∀ x ∈ [Component.mem (am.addrAt s (3 + am.tail.length)) (64 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt s (3 + am.tail.length)) (64 / 8), .reg 2, .reg 0, .flags,
          .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        (AgreesExcept.afterStep_rmw s _ _ _ _ _).mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _,
          (AgreesExcept.afterStep_rmw s _ _ _ _ _).read (by simp),
          (AgreesExcept.afterStep_rmw s _ _ _ _ _).read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg8b_m64_triple_of_bytes [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => RmwPre p am 8 (3 + am.tail.length) s ∧
      (concat32 ((Operand.reg 2 : Operand 64).read s) ((Operand.reg 0 : Operand 64).read s) ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) :
          Operand 64).read s) = c)
      (codeRange p (0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (Effect.post (cmpxchg8bM64Effect p (3 + am.tail.length) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchg8bM64Effect_components]; exact mem_components_rmwRegPair _ _ _ _) hpre.1.code
    (by simp; omega))
    (cmpxchg8b_m64_effect_step p am hv hx hb c)

theorem cmpxchg8b_m64_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => RmwPre p am 8 (4 + am.tail.length) s ∧
      (concat32 ((Operand.reg 2 : Operand 64).read s) ((Operand.reg 0 : Operand 64).read s) ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 64).read s) = c)
      (codeRange p (rex :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (cmpxchg8bM64Effect p (4 + am.tail.length) am c) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cmpxchg8b_m64_step s h [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (rexContext s.DS rex.toBitVec) (am.addrAt s (4 + am.tail.length)) =
    am.addrAt s (4 + am.tail.length) from rfl] at hstep
  cases c
  · have hne : ¬concat32 ((Operand.reg 2 : Operand 64).read s)
        ((Operand.reg 0 : Operand 64).read s) =
        (Operand.mem (am.addrAt s (4 + am.tail.length)) : Operand 64).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte, cmpxchg8bSpec, decide_false] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwRegPair h _ _ _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwRegPair_rip h _ _ _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwRegPair s _ _ _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwRegPair_mem (n := 64) s _ (by decide) (by decide) _ _ _ _
        _ _ _ _, ?_, ?_⟩
      · rw [Operand.read_afterStep_rmwRegPair_reg₁ _ _ _ _ _ _ _ _ _ _ (by decide)]
        rfl
      · rw [Operand.read_afterStep_rmwRegPair_reg₂ _ _ _ _ _ _ _ _ _ _ (by decide)]
        rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : concat32 ((Operand.reg 2 : Operand 64).read s)
        ((Operand.reg 0 : Operand 64).read s) =
        (Operand.mem (am.addrAt s (4 + am.tail.length)) : Operand 64).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte, cmpxchg8bSpec, decide_true] at hstep
    have hsub : ∀ x ∈ [Component.mem (am.addrAt s (4 + am.tail.length)) (64 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt s (4 + am.tail.length)) (64 / 8), .reg 2, .reg 0, .flags,
          .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        (AgreesExcept.afterStep_rmw s _ _ _ _ _).mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _,
          (AgreesExcept.afterStep_rmw s _ _ _ _ _).read (by simp),
          (AgreesExcept.afterStep_rmw s _ _ _ _ _).read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg8b_m64_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => RmwPre p am 8 (4 + am.tail.length) s ∧
      (concat32 ((Operand.reg 2 : Operand 64).read s) ((Operand.reg 0 : Operand 64).read s) ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 64).read s) = c)
      (codeRange p (rex :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (Effect.post (cmpxchg8bM64Effect p (4 + am.tail.length) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchg8bM64Effect_components]; exact mem_components_rmwRegPair _ _ _ _) hpre.1.code
    (by simp; omega))
    (cmpxchg8b_m64_rex_effect_step p rex hrex am hv hx hb c)

theorem cmpxchg8b_m64_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (c : Bool) :
    Triple (fun s => RmwPre p am 8 (encodeCmpxchg8bM64 am).length s ∧
      (concat32 ((Operand.reg 2 : Operand 64).read s) ((Operand.reg 0 : Operand 64).read s) ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (encodeCmpxchg8bM64 am).length)) :
          Operand 64).read s) = c)
      (codeRange p (encodeCmpxchg8bM64 am))
      (Effect.post (cmpxchg8bM64Effect p (encodeCmpxchg8bM64 am).length am c)) := by
  unfold encodeCmpxchg8bM64
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := cmpxchg8b_m64_triple_of_bytes p am hv hx hb c
    rwa [show (0x0F :: 0xC7 :: am.modrm 1 :: am.tail).length = 3 + am.tail.length by
      simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := cmpxchg8b_m64_rex_triple_of_bytes p _ hrex am hv hx hb c
    rwa [show (am.rexByte false 0 :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail).length =
      4 + am.tail.length by simp; omega]

theorem cmpxchg8b_m64_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 8 (4 + am.tail.length) s ∧
      (concat32 ((Operand.reg 2 : Operand 64).read s) ((Operand.reg 0 : Operand 64).read s) ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 64).read s) = c)
      (codeRange p (r.prefixByte :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (cmpxchg8bM64SegEffect p (4 + am.tail.length) base am c) := by
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [] noSegPrefix_nil]
  have hstep := cmpxchg8b_m64_step s h [r.prefixByte]
    (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.reduceAdd] at hstep
  cases c
  · have hne : ¬concat32 ((Operand.reg 2 : Operand 64).read s)
        ((Operand.reg 0 : Operand 64).read s) =
        (Operand.mem (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) : Operand 64).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte, cmpxchg8bSpec, decide_false] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwRegPair h _ _ _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwRegPair_rip h _ _ _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwRegPair s _ _ _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwRegPair_mem (n := 64) s _ (by decide) (by decide) _ _ _ _
        _ _ _ _, ?_, ?_⟩
      · rw [Operand.read_afterStep_rmwRegPair_reg₁ _ _ _ _ _ _ _ _ _ _ (by decide)]
        rfl
      · rw [Operand.read_afterStep_rmwRegPair_reg₂ _ _ _ _ _ _ _ _ _ _ (by decide)]
        rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : concat32 ((Operand.reg 2 : Operand 64).read s)
        ((Operand.reg 0 : Operand 64).read s) =
        (Operand.mem (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) : Operand 64).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte, cmpxchg8bSpec, decide_true] at hstep
    have hsub : ∀ x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) (64 / 8), .flags, .rip],
        x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) (64 / 8), .reg 2, .reg 0, .flags,
          .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        (AgreesExcept.afterStep_rmw s _ _ _ _ _).mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _,
          (AgreesExcept.afterStep_rmw s _ _ _ _ _).read (by simp),
          (AgreesExcept.afterStep_rmw s _ _ _ _ _).read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg8b_m64_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 8 (4 + am.tail.length) s ∧
      (concat32 ((Operand.reg 2 : Operand 64).read s) ((Operand.reg 0 : Operand 64).read s) ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 64).read s) = c)
      (codeRange p (r.prefixByte :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (Effect.post (cmpxchg8bM64SegEffect p (4 + am.tail.length) base am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchg8bM64SegEffect_components]; exact mem_components_rmwRegPair _ _ _ _) hpre.1.store.code
    (by simp; omega))
    (cmpxchg8b_m64_seg_effect_step p r base am hv hx hb c)

theorem cmpxchg8b_m64_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 8 (5 + am.tail.length) s ∧
      (concat32 ((Operand.reg 2 : Operand 64).read s) ((Operand.reg 0 : Operand 64).read s) ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 64).read s) = c)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (cmpxchg8bM64SegEffect p (5 + am.tail.length) base am c) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hc⟩
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
  have hstep := cmpxchg8b_m64_step s h [r.prefixByte, rex]
    (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; exact hrex.rex_w s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.reduceAdd] at hstep
  cases c
  · have hne : ¬concat32 ((Operand.reg 2 : Operand 64).read s)
        ((Operand.reg 0 : Operand 64).read s) =
        (Operand.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) : Operand 64).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte, cmpxchg8bSpec, decide_false] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwRegPair h _ _ _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwRegPair_rip h _ _ _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwRegPair s _ _ _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwRegPair_mem (n := 64) s _ (by decide) (by decide) _ _ _ _
        _ _ _ _, ?_, ?_⟩
      · rw [Operand.read_afterStep_rmwRegPair_reg₁ _ _ _ _ _ _ _ _ _ _ (by decide)]
        rfl
      · rw [Operand.read_afterStep_rmwRegPair_reg₂ _ _ _ _ _ _ _ _ _ _ (by decide)]
        rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : concat32 ((Operand.reg 2 : Operand 64).read s)
        ((Operand.reg 0 : Operand 64).read s) =
        (Operand.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) : Operand 64).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte, cmpxchg8bSpec, decide_true] at hstep
    have hsub : ∀ x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) (64 / 8), .flags, .rip],
        x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) (64 / 8), .reg 2, .reg 0, .flags,
          .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        (AgreesExcept.afterStep_rmw s _ _ _ _ _).mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _,
          (AgreesExcept.afterStep_rmw s _ _ _ _ _).read (by simp),
          (AgreesExcept.afterStep_rmw s _ _ _ _ _).read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg8b_m64_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 8 (5 + am.tail.length) s ∧
      (concat32 ((Operand.reg 2 : Operand 64).read s) ((Operand.reg 0 : Operand 64).read s) ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 64).read s) = c)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (Effect.post (cmpxchg8bM64SegEffect p (5 + am.tail.length) base am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchg8bM64SegEffect_components]; exact mem_components_rmwRegPair _ _ _ _) hpre.1.store.code
    (by simp; omega))
    (cmpxchg8b_m64_rex_seg_effect_step p r base rex hrex am hv hx hb c)

theorem cmpxchg8b_m64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 8 (r.prefixByte :: encodeCmpxchg8bM64 am).length s ∧
      (concat32 ((Operand.reg 2 : Operand 64).read s) ((Operand.reg 0 : Operand 64).read s) ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeCmpxchg8bM64 am).length)) :
          Operand 64).read s) = c)
      (codeRange p (r.prefixByte :: encodeCmpxchg8bM64 am))
      (Effect.post (cmpxchg8bM64SegEffect p (r.prefixByte :: encodeCmpxchg8bM64 am).length base am
        c)) := by
  unfold encodeCmpxchg8bM64
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := cmpxchg8b_m64_seg_triple_of_bytes p r base am hv hx hb c
    rwa [show (r.prefixByte :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := cmpxchg8b_m64_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb c
    rwa [show (r.prefixByte :: am.rexByte false 0 :: 0x0F :: 0xC7 :: am.modrm 1 ::
      am.tail).length = 5 + am.tail.length by simp; omega]

theorem cmpxchg8b_m64_a32_effect_step [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => Rmw32Pre p am 8 (4 + am.tail.length) s ∧
      (concat32 ((Operand.reg 2 : Operand 64).read s) ((Operand.reg 0 : Operand 64).read s) ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 64).read s) = c)
      (codeRange p (0x67 :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (cmpxchg8bM64A32Effect p (4 + am.tail.length) am c) := by
  intro s h hcode ⟨hpre, hc⟩
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
  have hstep := cmpxchg8b_m64_a32_step s h [0x67]
    (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])) (am.addrAt32 s (4 + am.tail.length)) =
    am.addrAt32 s (4 + am.tail.length) from rfl] at hstep
  cases c
  · have hne : ¬concat32 ((Operand.reg 2 : Operand 64).read s)
        ((Operand.reg 0 : Operand 64).read s) =
        (Operand.mem (am.addrAt32 s (4 + am.tail.length)) : Operand 64).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte, cmpxchg8bSpec, decide_false] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwRegPair h _ _ _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwRegPair_rip h _ _ _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwRegPair s _ _ _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwRegPair_mem (n := 64) s _ (by decide) (by decide) _ _ _ _
        _ _ _ _, ?_, ?_⟩
      · rw [Operand.read_afterStep_rmwRegPair_reg₁ _ _ _ _ _ _ _ _ _ _ (by decide)]
        rfl
      · rw [Operand.read_afterStep_rmwRegPair_reg₂ _ _ _ _ _ _ _ _ _ _ (by decide)]
        rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : concat32 ((Operand.reg 2 : Operand 64).read s)
        ((Operand.reg 0 : Operand 64).read s) =
        (Operand.mem (am.addrAt32 s (4 + am.tail.length)) : Operand 64).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte, cmpxchg8bSpec, decide_true] at hstep
    have hsub : ∀ x ∈ [Component.mem (am.addrAt32 s (4 + am.tail.length)) (64 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt32 s (4 + am.tail.length)) (64 / 8), .reg 2, .reg 0, .flags,
          .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        (AgreesExcept.afterStep_rmw s _ _ _ _ _).mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _,
          (AgreesExcept.afterStep_rmw s _ _ _ _ _).read (by simp),
          (AgreesExcept.afterStep_rmw s _ _ _ _ _).read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg8b_m64_a32_triple_of_bytes [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 8 (4 + am.tail.length) s ∧
      (concat32 ((Operand.reg 2 : Operand 64).read s) ((Operand.reg 0 : Operand 64).read s) ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 64).read s) = c)
      (codeRange p (0x67 :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (Effect.post (cmpxchg8bM64A32Effect p (4 + am.tail.length) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchg8bM64A32Effect_components]; exact mem_components_rmwRegPair _ _ _ _) hpre.1.code
    (by simp; omega))
    (cmpxchg8b_m64_a32_effect_step p am hv hx hb c)

theorem cmpxchg8b_m64_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => Rmw32Pre p am 8 (5 + am.tail.length) s ∧
      (concat32 ((Operand.reg 2 : Operand 64).read s) ((Operand.reg 0 : Operand 64).read s) ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 64).read s) = c)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (cmpxchg8bM64A32Effect p (5 + am.tail.length) am c) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hc⟩
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
  have hstep := cmpxchg8b_m64_a32_step s h [0x67, rex]
    (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; exact hrex.rex_w s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (withAsz (rexContext s.DS rex.toBitVec)) (am.addrAt32 s (5 + am.tail.length)) =
    am.addrAt32 s (5 + am.tail.length) from rfl] at hstep
  cases c
  · have hne : ¬concat32 ((Operand.reg 2 : Operand 64).read s)
        ((Operand.reg 0 : Operand 64).read s) =
        (Operand.mem (am.addrAt32 s (5 + am.tail.length)) : Operand 64).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte, cmpxchg8bSpec, decide_false] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwRegPair h _ _ _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwRegPair_rip h _ _ _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwRegPair s _ _ _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwRegPair_mem (n := 64) s _ (by decide) (by decide) _ _ _ _
        _ _ _ _, ?_, ?_⟩
      · rw [Operand.read_afterStep_rmwRegPair_reg₁ _ _ _ _ _ _ _ _ _ _ (by decide)]
        rfl
      · rw [Operand.read_afterStep_rmwRegPair_reg₂ _ _ _ _ _ _ _ _ _ _ (by decide)]
        rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : concat32 ((Operand.reg 2 : Operand 64).read s)
        ((Operand.reg 0 : Operand 64).read s) =
        (Operand.mem (am.addrAt32 s (5 + am.tail.length)) : Operand 64).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte, cmpxchg8bSpec, decide_true] at hstep
    have hsub : ∀ x ∈ [Component.mem (am.addrAt32 s (5 + am.tail.length)) (64 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt32 s (5 + am.tail.length)) (64 / 8), .reg 2, .reg 0, .flags,
          .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        (AgreesExcept.afterStep_rmw s _ _ _ _ _).mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _,
          (AgreesExcept.afterStep_rmw s _ _ _ _ _).read (by simp),
          (AgreesExcept.afterStep_rmw s _ _ _ _ _).read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg8b_m64_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 8 (5 + am.tail.length) s ∧
      (concat32 ((Operand.reg 2 : Operand 64).read s) ((Operand.reg 0 : Operand 64).read s) ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 64).read s) = c)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
      (Effect.post (cmpxchg8bM64A32Effect p (5 + am.tail.length) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchg8bM64A32Effect_components]; exact mem_components_rmwRegPair _ _ _ _) hpre.1.code
    (by simp; omega))
    (cmpxchg8b_m64_rex_a32_effect_step p rex hrex am hv hx hb c)

theorem cmpxchg8b_m64_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (c : Bool) :
    Triple (fun s => Rmw32Pre p am 8 (0x67 :: encodeCmpxchg8bM64 am).length s ∧
      (concat32 ((Operand.reg 2 : Operand 64).read s) ((Operand.reg 0 : Operand 64).read s) ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeCmpxchg8bM64 am).length)) :
          Operand 64).read s) = c)
      (codeRange p (0x67 :: encodeCmpxchg8bM64 am))
      (Effect.post (cmpxchg8bM64A32Effect p (0x67 :: encodeCmpxchg8bM64 am).length am c)) := by
  unfold encodeCmpxchg8bM64
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := cmpxchg8b_m64_a32_triple_of_bytes p am hv hx hb c
    rwa [show (0x67 :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := cmpxchg8b_m64_rex_a32_triple_of_bytes p _ hrex am hv hx hb c
    rwa [show (0x67 :: am.rexByte false 0 :: 0x0F :: 0xC7 :: am.modrm 1 ::
      am.tail).length = 5 + am.tail.length by simp; omega]

attribute [x86_compose] cmpxchg8bM64Effect cmpxchg8bM64SegEffect cmpxchg8bM64A32Effect

@[x86_local] theorem cmpxchg8bM64Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode}
    {c : Bool} :
    Effect.Local (cmpxchg8bM64Effect p len am c) := by
  effect_local [cmpxchg8bM64Effect, concat32]

@[x86_local] theorem cmpxchg8bM64SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {c : Bool} :
    Effect.Local (cmpxchg8bM64SegEffect p len base am c) := by
  effect_local [cmpxchg8bM64SegEffect, concat32]

@[x86_local] theorem cmpxchg8bM64A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode}
    {c : Bool} :
    Effect.Local (cmpxchg8bM64A32Effect p len am c) := by
  effect_local [cmpxchg8bM64A32Effect, concat32]

end X86Proofs
