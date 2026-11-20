import X86Proofs.Instructions.Cmpxchg.Generated.M8R8.Step
import X86Proofs.Instructions.Cmpxchg.Generated.M8R8.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Cmpxchg.Generated.MR.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cmpxchgM8R8NoRexEffect (p : BitVec 64) (len : Nat) (src : BitVec 3) (am : AddrMode) (c : Bool)
    (s : RamState) : Effect :=
  let a := am.addr s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand 8).read s
  let y := (Operand.byteReg src).read s
  let acc := (Operand.reg 0 : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand 8), if c then y else x⟩,
      ⟨(Operand.reg 0 : Operand 64), if c then (Operand.reg 0 : Operand 64).read s
        else mergeGPR 8 x ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (cmpSpec acc x)) }

@[simp] theorem cmpxchgM8R8NoRexEffect_components (p : BitVec 64) (len : Nat) (src : BitVec 3)
    (am : AddrMode) (c : Bool) (s : RamState) : (cmpxchgM8R8NoRexEffect p len src am c s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) (8 / 8), .reg 0, .flags, .rip] := rfl

def cmpxchgM8R8NoRexSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (src : BitVec 3) (am : AddrMode) (c : Bool)
    (s : RamState) : Effect :=
  let a := base + am.addr s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand 8).read s
  let y := (Operand.byteReg src).read s
  let acc := (Operand.reg 0 : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand 8), if c then y else x⟩,
      ⟨(Operand.reg 0 : Operand 64), if c then (Operand.reg 0 : Operand 64).read s
        else mergeGPR 8 x ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (cmpSpec acc x)) }

@[simp] theorem cmpxchgM8R8NoRexSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64) (src : BitVec 3)
    (am : AddrMode) (c : Bool) (s : RamState) : (cmpxchgM8R8NoRexSegEffect p len base src am c s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) (8 / 8), .reg 0, .flags, .rip] := rfl

def cmpxchgM8R8NoRexA32Effect (p : BitVec 64) (len : Nat) (src : BitVec 3) (am : AddrMode) (c : Bool)
    (s : RamState) : Effect :=
  let a := am.addr32 s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand 8).read s
  let y := (Operand.byteReg src).read s
  let acc := (Operand.reg 0 : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand 8), if c then y else x⟩,
      ⟨(Operand.reg 0 : Operand 64), if c then (Operand.reg 0 : Operand 64).read s
        else mergeGPR 8 x ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (cmpSpec acc x)) }

@[simp] theorem cmpxchgM8R8NoRexA32Effect_components (p : BitVec 64) (len : Nat) (src : BitVec 3)
    (am : AddrMode) (c : Bool) (s : RamState) : (cmpxchgM8R8NoRexA32Effect p len src am c s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) (8 / 8), .reg 0, .flags, .rip] := rfl

theorem cmpxchg_m8_r8_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => RmwPre p am 1 (3 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (cmpxchgMREffect p (3 + am.tail.length) 8
        (gprNumber 0 0 reg) am c) := by
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cmpxchg_m8_r8_step s h [] (by simp)
    (by simp)
    (by rfl) (by rfl)
    (by rfl) reg
    (.inr (by exact gprNumber_low4 reg hreg)) am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  simp only [List.length_nil, Nat.zero_add] at hstep
  rw [show segAddr (scanContext s.DS (PrefixSegments.ofState s) []) (am.addrAt s (3 + am.tail.length)) = am.addrAt s (3 + am.tail.length) from rfl]
    at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 8).read s =
        (Operand.mem (am.addrAt s (3 + am.tail.length)) : Operand 8).read s :=
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
        (Operand.mem (am.addrAt s (3 + am.tail.length)) : Operand 8).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (3 + am.tail.length) (n := 8)
      (am.addrAt s (3 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 0 reg) : Operand 8).read s,
        cmpSpec ((Operand.reg 0 : Operand 8).read s)
          ((Operand.mem (am.addrAt s (3 + am.tail.length)) : Operand 8).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (am.addrAt s (3 + am.tail.length)) (8 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt s (3 + am.tail.length)) (8 / 8), .reg 0, .flags, .rip] := by
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

theorem cmpxchg_m8_r8_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => RmwPre p am 1 (3 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMREffect p (3 + am.tail.length) 8
        (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMREffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.code
    (by simp; omega))
    (cmpxchg_m8_r8_effect_step p reg hreg am hv hx hb c)

theorem cmpxchg_m8_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => RmwPre p am 1 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (rex :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (cmpxchgMREffect p (4 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cmpxchg_m8_r8_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg
    (.inl (by rw [scanContext_rex _ _ hr]; rfl)) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (rexContext s.DS rex.toBitVec) (am.addrAt s (4 + am.tail.length)) = am.addrAt s (4 + am.tail.length) from rfl]
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
      (fun _ => ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 8).read s,
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

theorem cmpxchg_m8_r8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => RmwPre p am 1 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (rex :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMREffect p (4 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMREffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.code
    (by simp; omega))
    (cmpxchg_m8_r8_rex_effect_step p rex hr reg am hv hx hb c)

theorem cmpxchg_m8_r8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 1 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (r.prefixByte :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (cmpxchgMRSegEffect p (4 + am.tail.length) 8 base
        (gprNumber 0 0 reg) am c) := by
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
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := cmpxchg_m8_r8_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp))
    (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inr (by rw [hsc]; exact gprNumber_low4 reg hreg)) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 8).read s =
        (Operand.mem (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) : Operand 8).read s :=
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
        (Operand.mem (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) : Operand 8).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (4 + am.tail.length) (n := 8)
      (segBase (r.read s) + am.addrAt s (4 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 0 reg) : Operand 8).read s,
        cmpSpec ((Operand.reg 0 : Operand 8).read s)
          ((Operand.mem (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) : Operand 8).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) (8 / 8), .flags, .rip],
        x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) (8 / 8), .reg 0, .flags, .rip] := by
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

theorem cmpxchg_m8_r8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 1 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (r.prefixByte :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMRSegEffect p (4 + am.tail.length) 8 base
        (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMRSegEffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.store.code
    (by simp; omega))
    (cmpxchg_m8_r8_seg_effect_step p r base reg hreg am hv hx hb c)

theorem cmpxchg_m8_r8_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 1 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (cmpxchgMRSegEffect p (5 + am.tail.length) 8 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
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
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := cmpxchg_m8_r8_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix))
    (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inl (by rw [hsc]; rfl)) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
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
      (fun _ => ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 8).read s,
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

theorem cmpxchg_m8_r8_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 1 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMRSegEffect p (5 + am.tail.length) 8 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMRSegEffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.store.code
    (by simp; omega))
    (cmpxchg_m8_r8_rex_seg_effect_step p r base rex hr reg am hv hx hb c)

theorem cmpxchg_m8_r8_norex_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => RmwPre p am 1 (3 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (cmpxchgM8R8NoRexEffect p (3 + am.tail.length)
        reg am c) := by
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cmpxchg_m8_r8_gpr8_step s h [] (by simp)
    (by simp)
    (by rfl) (by rfl)
    (by rfl) reg am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  have hsrc : Operand.gpr8 (gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 reg)
      (byteRex (scanContext s.DS (PrefixSegments.ofState s) [])) = Operand.byteReg reg := rfl
  rw [hsrc] at hstep
  simp only [List.length_nil, Nat.zero_add] at hstep
  rw [show segAddr (scanContext s.DS (PrefixSegments.ofState s) []) (am.addrAt s (3 + am.tail.length)) = am.addrAt s (3 + am.tail.length) from rfl]
    at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 8).read s =
        (Operand.mem (am.addrAt s (3 + am.tail.length)) : Operand 8).read s :=
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
        (Operand.mem (am.addrAt s (3 + am.tail.length)) : Operand 8).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (3 + am.tail.length) (n := 8)
      (am.addrAt s (3 + am.tail.length))
      (fun _ => ((Operand.byteReg reg).read s,
        cmpSpec ((Operand.reg 0 : Operand 8).read s)
          ((Operand.mem (am.addrAt s (3 + am.tail.length)) : Operand 8).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (am.addrAt s (3 + am.tail.length)) (8 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt s (3 + am.tail.length)) (8 / 8), .reg 0, .flags, .rip] := by
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

theorem cmpxchg_m8_r8_norex_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => RmwPre p am 1 (3 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgM8R8NoRexEffect p (3 + am.tail.length)
        reg am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgM8R8NoRexEffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.code
    (by simp; omega))
    (cmpxchg_m8_r8_norex_effect_step p reg am hv hx hb c)

theorem cmpxchg_m8_r8_norex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 1 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (r.prefixByte :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (cmpxchgM8R8NoRexSegEffect p (4 + am.tail.length) base
        reg am c) := by
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
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := cmpxchg_m8_r8_gpr8_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp))
    (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : Operand.gpr8 (gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r3 reg)
      (byteRex (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)))) = Operand.byteReg reg := rfl
  rw [hsrc] at hstep
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 8).read s =
        (Operand.mem (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) : Operand 8).read s :=
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
        (Operand.mem (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) : Operand 8).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (4 + am.tail.length) (n := 8)
      (segBase (r.read s) + am.addrAt s (4 + am.tail.length))
      (fun _ => ((Operand.byteReg reg).read s,
        cmpSpec ((Operand.reg 0 : Operand 8).read s)
          ((Operand.mem (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) : Operand 8).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) (8 / 8), .flags, .rip],
        x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) (8 / 8), .reg 0, .flags, .rip] := by
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

theorem cmpxchg_m8_r8_norex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 1 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (r.prefixByte :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgM8R8NoRexSegEffect p (4 + am.tail.length) base
        reg am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgM8R8NoRexSegEffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.store.code
    (by simp; omega))
    (cmpxchg_m8_r8_norex_seg_effect_step p r base reg am hv hx hb c)

theorem cmpxchg_m8_r8_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => Rmw32Pre p am 1 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0x67 :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (cmpxchgMRA32Effect p (4 + am.tail.length) 8
        (gprNumber 0 0 reg) am c) := by
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
  have hstep := cmpxchg_m8_r8_a32_step s h [0x67] (scanPrefix_asz_cons (by simp))
    (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inr (by rw [hsc]; exact gprNumber_low4 reg hreg)) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])) (am.addrAt32 s (4 + am.tail.length)) = am.addrAt32 s (4 + am.tail.length) from rfl]
    at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 8).read s =
        (Operand.mem (am.addrAt32 s (4 + am.tail.length)) : Operand 8).read s :=
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
        (Operand.mem (am.addrAt32 s (4 + am.tail.length)) : Operand 8).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (4 + am.tail.length) (n := 8)
      (am.addrAt32 s (4 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 0 reg) : Operand 8).read s,
        cmpSpec ((Operand.reg 0 : Operand 8).read s)
          ((Operand.mem (am.addrAt32 s (4 + am.tail.length)) : Operand 8).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (am.addrAt32 s (4 + am.tail.length)) (8 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt32 s (4 + am.tail.length)) (8 / 8), .reg 0, .flags, .rip] := by
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

theorem cmpxchg_m8_r8_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 1 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0x67 :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMRA32Effect p (4 + am.tail.length) 8
        (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMRA32Effect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.code
    (by simp; omega))
    (cmpxchg_m8_r8_a32_effect_step p reg hreg am hv hx hb c)

theorem cmpxchg_m8_r8_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => Rmw32Pre p am 1 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (cmpxchgMRA32Effect p (5 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
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
  have hstep := cmpxchg_m8_r8_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix))
    (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inl (by rw [hsc]; rfl)) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (rexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (rexContext s.DS rex.toBitVec)).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (withAsz (rexContext s.DS rex.toBitVec)) (am.addrAt32 s (5 + am.tail.length)) = am.addrAt32 s (5 + am.tail.length) from rfl]
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
      (fun _ => ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 8).read s,
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

theorem cmpxchg_m8_r8_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 1 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMRA32Effect p (5 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMRA32Effect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.code
    (by simp; omega))
    (cmpxchg_m8_r8_rex_a32_effect_step p rex hr reg am hv hx hb c)

theorem cmpxchg_m8_r8_norex_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => Rmw32Pre p am 1 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0x67 :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (cmpxchgM8R8NoRexA32Effect p (4 + am.tail.length)
        reg am c) := by
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
  have hstep := cmpxchg_m8_r8_gpr8_a32_step s h [0x67] (scanPrefix_asz_cons (by simp))
    (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hsrc : Operand.gpr8 (gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r3 reg)
      (byteRex (withAsz (scanContext s.DS (PrefixSegments.ofState s) []))) = Operand.byteReg reg := rfl
  rw [hsrc] at hstep
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])) (am.addrAt32 s (4 + am.tail.length)) = am.addrAt32 s (4 + am.tail.length) from rfl]
    at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 8).read s =
        (Operand.mem (am.addrAt32 s (4 + am.tail.length)) : Operand 8).read s :=
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
        (Operand.mem (am.addrAt32 s (4 + am.tail.length)) : Operand 8).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (4 + am.tail.length) (n := 8)
      (am.addrAt32 s (4 + am.tail.length))
      (fun _ => ((Operand.byteReg reg).read s,
        cmpSpec ((Operand.reg 0 : Operand 8).read s)
          ((Operand.mem (am.addrAt32 s (4 + am.tail.length)) : Operand 8).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (am.addrAt32 s (4 + am.tail.length)) (8 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt32 s (4 + am.tail.length)) (8 / 8), .reg 0, .flags, .rip] := by
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

theorem cmpxchg_m8_r8_norex_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 1 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0x67 :: 0x0F :: 0xB0 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgM8R8NoRexA32Effect p (4 + am.tail.length)
        reg am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgM8R8NoRexA32Effect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.code
    (by simp; omega))
    (cmpxchg_m8_r8_norex_a32_effect_step p reg am hv hx hb c)

theorem cmpxchg_m8_r8_norex_triple [Bindings] (p : BitVec 64) (src : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => RmwPre p am 1 (3 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (encodeCmpxchgM8R8NoRex src am))
      (Effect.post (cmpxchgM8R8NoRexEffect p (3 + am.tail.length) src am c)) :=
  cmpxchg_m8_r8_norex_triple_of_bytes p src am hv hx hb c

theorem cmpxchg_m8_r8_norex_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 1 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (r.prefixByte :: encodeCmpxchgM8R8NoRex src am))
      (Effect.post (cmpxchgM8R8NoRexSegEffect p (4 + am.tail.length) base src am c)) :=
  cmpxchg_m8_r8_norex_seg_triple_of_bytes p r base src am hv hx hb c

theorem cmpxchg_m8_r8_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (c : Bool) :
    Triple (fun s => RmwPre p am 1 (encodeCmpxchgM8R8 src am).length s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (encodeCmpxchgM8R8 src am).length)) :
          Operand 8).read s) = c)
      (codeRange p (encodeCmpxchgM8R8 src am))
      (Effect.post
        (cmpxchgMREffect p (encodeCmpxchgM8R8 src am).length 8 (src.setWidth 5) am c)) := by
  unfold encodeCmpxchgM8R8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec src hs
    have := cmpxchg_m8_r8_triple_of_bytes p (regLow src) hl am hv hx hb c
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := cmpxchg_m8_r8_rex_triple_of_bytes p _ hrex.rexPrefix (regLow src) am hv hx hb c
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem cmpxchg_m8_r8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 1 (r.prefixByte :: encodeCmpxchgM8R8 src am).length s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeCmpxchgM8R8 src am).length)) :
          Operand 8).read s) = c)
      (codeRange p (r.prefixByte :: encodeCmpxchgM8R8 src am))
      (Effect.post (cmpxchgMRSegEffect p (r.prefixByte :: encodeCmpxchgM8R8 src am).length 8 base
        (src.setWidth 5) am c)) := by
  unfold encodeCmpxchgM8R8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec src hs
    have := cmpxchg_m8_r8_seg_triple_of_bytes p r base (regLow src) hl am hv hx hb c
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := cmpxchg_m8_r8_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix (regLow src) am
      hv hx hb c
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

theorem cmpxchg_m8_r8_norex_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 1 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 8).read s) = c)
      (codeRange p (0x67 :: encodeCmpxchgM8R8NoRex src am))
      (Effect.post (cmpxchgM8R8NoRexA32Effect p (4 + am.tail.length) src am c)) :=
  cmpxchg_m8_r8_norex_a32_triple_of_bytes p src am hv hx hb c

theorem cmpxchg_m8_r8_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 1 (0x67 :: encodeCmpxchgM8R8 src am).length s ∧
      ((Operand.reg 0 : Operand 8).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeCmpxchgM8R8 src am).length)) :
          Operand 8).read s) = c)
      (codeRange p (0x67 :: encodeCmpxchgM8R8 src am))
      (Effect.post
        (cmpxchgMRA32Effect p (0x67 :: encodeCmpxchgM8R8 src am).length 8 (src.setWidth 5) am c)) := by
  unfold encodeCmpxchgM8R8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec src hs
    have := cmpxchg_m8_r8_a32_triple_of_bytes p (regLow src) hl am hv hx hb c
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := cmpxchg_m8_r8_rex_a32_triple_of_bytes p _ hrex.rexPrefix (regLow src) am hv hx
      hb c
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

attribute [x86_compose] cmpxchgM8R8NoRexEffect cmpxchgM8R8NoRexSegEffect

@[x86_local] theorem cmpxchgM8R8NoRexEffect_local {p : BitVec 64} {len : Nat} {src : BitVec 3}
    {am : AddrMode} {c : Bool} :
    Effect.Local (cmpxchgM8R8NoRexEffect p len src am c) := by
  effect_local [cmpxchgM8R8NoRexEffect]

@[x86_local] theorem cmpxchgM8R8NoRexSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 3} {am : AddrMode} {c : Bool} :
    Effect.Local (cmpxchgM8R8NoRexSegEffect p len base src am c) := by
  effect_local [cmpxchgM8R8NoRexSegEffect]

attribute [x86_compose] cmpxchgM8R8NoRexA32Effect

@[x86_local] theorem cmpxchgM8R8NoRexA32Effect_local {p : BitVec 64} {len : Nat} {src : BitVec 3}
    {am : AddrMode} {c : Bool} :
    Effect.Local (cmpxchgM8R8NoRexA32Effect p len src am c) := by
  effect_local [cmpxchgM8R8NoRexA32Effect]

end X86Proofs
