import X86Proofs.Instructions.Cmpxchg.Generated.MR.Step
import X86Proofs.Instructions.Cmpxchg.Generated.MR.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cmpxchgMREffect (p : BitVec 64) (len n : Nat) (src : BitVec 5) (am : AddrMode) (c : Bool)
    (s : RamState) : Effect :=
  let a := am.addr s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand n).read s
  let y := (Operand.reg src : Operand n).read s
  let acc := (Operand.reg 0 : Operand n).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand n), if c then y else x⟩,
      ⟨(Operand.reg 0 : Operand 64), if c then (Operand.reg 0 : Operand 64).read s
        else mergeGPR n x ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (cmpSpec acc x)) }

@[simp] theorem cmpxchgMREffect_components (p : BitVec 64) (len n : Nat) (src : BitVec 5)
    (am : AddrMode) (c : Bool) (s : RamState) : (cmpxchgMREffect p len n src am c s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) (n / 8), .reg 0, .flags, .rip] := rfl

def cmpxchgMRSegEffect (p : BitVec 64) (len n : Nat) (base : BitVec 64) (src : BitVec 5) (am : AddrMode) (c : Bool)
    (s : RamState) : Effect :=
  let a := base + am.addr s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand n).read s
  let y := (Operand.reg src : Operand n).read s
  let acc := (Operand.reg 0 : Operand n).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand n), if c then y else x⟩,
      ⟨(Operand.reg 0 : Operand 64), if c then (Operand.reg 0 : Operand 64).read s
        else mergeGPR n x ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (cmpSpec acc x)) }

@[simp] theorem cmpxchgMRSegEffect_components (p : BitVec 64) (len n : Nat) (base : BitVec 64)
    (src : BitVec 5) (am : AddrMode) (c : Bool) (s : RamState) :
    (cmpxchgMRSegEffect p len n base src am c s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) (n / 8),
        .reg 0, .flags, .rip] := rfl

def cmpxchgMRA32Effect (p : BitVec 64) (len n : Nat) (src : BitVec 5) (am : AddrMode) (c : Bool)
    (s : RamState) : Effect :=
  let a := am.addr32 s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand n).read s
  let y := (Operand.reg src : Operand n).read s
  let acc := (Operand.reg 0 : Operand n).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand n), if c then y else x⟩,
      ⟨(Operand.reg 0 : Operand 64), if c then (Operand.reg 0 : Operand 64).read s
        else mergeGPR n x ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (cmpSpec acc x)) }

@[simp] theorem cmpxchgMRA32Effect_components (p : BitVec 64) (len n : Nat) (src : BitVec 5)
    (am : AddrMode) (c : Bool) (s : RamState) : (cmpxchgMRA32Effect p len n src am c s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) (n / 8), .reg 0, .flags,
        .rip] := rfl

theorem cmpxchg_m64_r64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => RmwPre p am 8 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 64).read s) = c)
      (codeRange p (rex :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (cmpxchgMREffect p (4 + am.tail.length) 64
        (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
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
  have hstep := cmpxchg_m_r_step s h [rex] (by simpa using hr.scanPrefix)
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
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (rexContext s.DS rex.toBitVec) (am.addrAt s (4 + am.tail.length)) = am.addrAt s (4 + am.tail.length) from rfl]
    at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 64).read s =
        (Operand.mem (am.addrAt s (4 + am.tail.length)) : Operand 64).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 64) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 64).read s =
        (Operand.mem (am.addrAt s (4 + am.tail.length)) : Operand 64).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (4 + am.tail.length) (n := 64)
      (am.addrAt s (4 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 64).read s,
        cmpSpec ((Operand.reg 0 : Operand 64).read s)
          ((Operand.mem (am.addrAt s (4 + am.tail.length)) : Operand 64).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (am.addrAt s (4 + am.tail.length)) (64 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt s (4 + am.tail.length)) (64 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_m64_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => RmwPre p am 8 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 64).read s) = c)
      (codeRange p (rex :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMREffect p (4 + am.tail.length) 64
        (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMREffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.code
    (by simp; omega))
    (cmpxchg_m64_r64_effect_step p rex hrex reg am hv hx hb c)

theorem cmpxchg_m32_r32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => RmwPre p am 4 (3 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 32).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) :
          Operand 32).read s) = c)
      (codeRange p (0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (cmpxchgMREffect p (3 + am.tail.length) 32
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
  have hstep := cmpxchg_m_r_step s h [] (by simp)
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
  simp only [List.length_nil, Nat.zero_add] at hstep
  rw [show segAddr (scanContext s.DS (PrefixSegments.ofState s) []) (am.addrAt s (3 + am.tail.length)) = am.addrAt s (3 + am.tail.length) from rfl]
    at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 32).read s =
        (Operand.mem (am.addrAt s (3 + am.tail.length)) : Operand 32).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 32) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 32).read s =
        (Operand.mem (am.addrAt s (3 + am.tail.length)) : Operand 32).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (3 + am.tail.length) (n := 32)
      (am.addrAt s (3 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 0 reg) : Operand 32).read s,
        cmpSpec ((Operand.reg 0 : Operand 32).read s)
          ((Operand.mem (am.addrAt s (3 + am.tail.length)) : Operand 32).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (am.addrAt s (3 + am.tail.length)) (32 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt s (3 + am.tail.length)) (32 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_m32_r32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => RmwPre p am 4 (3 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 32).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) :
          Operand 32).read s) = c)
      (codeRange p (0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMREffect p (3 + am.tail.length) 32
        (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMREffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.code
    (by simp; omega))
    (cmpxchg_m32_r32_effect_step p reg am hv hx hb c)

theorem cmpxchg_m32_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => RmwPre p am 4 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 32).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 32).read s) = c)
      (codeRange p (rex :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (cmpxchgMREffect p (4 + am.tail.length) 32
        (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
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
  have hstep := cmpxchg_m_r_step s h [rex] (by simpa using hr.scanPrefix)
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
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (rexContext s.DS rex.toBitVec) (am.addrAt s (4 + am.tail.length)) = am.addrAt s (4 + am.tail.length) from rfl]
    at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 32).read s =
        (Operand.mem (am.addrAt s (4 + am.tail.length)) : Operand 32).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 32) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 32).read s =
        (Operand.mem (am.addrAt s (4 + am.tail.length)) : Operand 32).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (4 + am.tail.length) (n := 32)
      (am.addrAt s (4 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 32).read s,
        cmpSpec ((Operand.reg 0 : Operand 32).read s)
          ((Operand.mem (am.addrAt s (4 + am.tail.length)) : Operand 32).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (am.addrAt s (4 + am.tail.length)) (32 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt s (4 + am.tail.length)) (32 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_m32_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => RmwPre p am 4 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 32).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 32).read s) = c)
      (codeRange p (rex :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMREffect p (4 + am.tail.length) 32
        (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMREffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.code
    (by simp; omega))
    (cmpxchg_m32_r32_rex_effect_step p rex hrex reg am hv hx hb c)

theorem cmpxchg_m16_r16_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => RmwPre p am 2 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 16).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 16).read s) = c)
      (codeRange p (0x66 :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (cmpxchgMREffect p (4 + am.tail.length) 16
        (gprNumber 0 0 reg) am c) := by
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cmpxchg_m16_r16_step s h [0x66] (by simpa using scanPrefix_66)
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
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (am.addrAt s (4 + am.tail.length)) = am.addrAt s (4 + am.tail.length) from rfl]
    at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 16).read s =
        (Operand.mem (am.addrAt s (4 + am.tail.length)) : Operand 16).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 16) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 16).read s =
        (Operand.mem (am.addrAt s (4 + am.tail.length)) : Operand 16).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (4 + am.tail.length) (n := 16)
      (am.addrAt s (4 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 0 reg) : Operand 16).read s,
        cmpSpec ((Operand.reg 0 : Operand 16).read s)
          ((Operand.mem (am.addrAt s (4 + am.tail.length)) : Operand 16).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (am.addrAt s (4 + am.tail.length)) (16 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt s (4 + am.tail.length)) (16 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_m16_r16_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => RmwPre p am 2 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 16).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 16).read s) = c)
      (codeRange p (0x66 :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMREffect p (4 + am.tail.length) 16
        (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMREffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.code
    (by simp; omega))
    (cmpxchg_m16_r16_effect_step p reg am hv hx hb c)

theorem cmpxchg_m16_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => RmwPre p am 2 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 16).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 16).read s) = c)
      (codeRange p (0x66 :: rex :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (cmpxchgMREffect p (5 + am.tail.length) 16
        (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cmpxchg_m16_r16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix])
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
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (oszRexContext s.DS rex.toBitVec) (am.addrAt s (5 + am.tail.length)) = am.addrAt s (5 + am.tail.length) from rfl]
    at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 16).read s =
        (Operand.mem (am.addrAt s (5 + am.tail.length)) : Operand 16).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 16) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 16).read s =
        (Operand.mem (am.addrAt s (5 + am.tail.length)) : Operand 16).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (5 + am.tail.length) (n := 16)
      (am.addrAt s (5 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 16).read s,
        cmpSpec ((Operand.reg 0 : Operand 16).read s)
          ((Operand.mem (am.addrAt s (5 + am.tail.length)) : Operand 16).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (5 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (am.addrAt s (5 + am.tail.length)) (16 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt s (5 + am.tail.length)) (16 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_m16_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => RmwPre p am 2 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 16).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 16).read s) = c)
      (codeRange p (0x66 :: rex :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMREffect p (5 + am.tail.length) 16
        (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMREffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.code
    (by simp; omega))
    (cmpxchg_m16_r16_rex_effect_step p rex hrex reg am hv hx hb c)

theorem cmpxchg_m64_r64_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 8 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 64).read s) = c)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (cmpxchgMRSegEffect p (5 + am.tail.length) 64 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
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
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := cmpxchg_m_r_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix))
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
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 64).read s =
        (Operand.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) : Operand 64).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 64) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 64).read s =
        (Operand.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) : Operand 64).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (5 + am.tail.length) (n := 64)
      (segBase (r.read s) + am.addrAt s (5 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 64).read s,
        cmpSpec ((Operand.reg 0 : Operand 64).read s)
          ((Operand.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) : Operand 64).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (5 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) (64 / 8), .flags, .rip],
        x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) (64 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_m64_r64_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 8 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 64).read s) = c)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMRSegEffect p (5 + am.tail.length) 64 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMRSegEffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.store.code
    (by simp; omega))
    (cmpxchg_m64_r64_seg_effect_step p r base rex hrex reg am hv hx hb c)

theorem cmpxchg_m32_r32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 4 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 32).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 32).read s) = c)
      (codeRange p (r.prefixByte :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (cmpxchgMRSegEffect p (4 + am.tail.length) 32 base
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
  have hstep := cmpxchg_m_r_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp))
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
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 32).read s =
        (Operand.mem (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) : Operand 32).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 32) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 32).read s =
        (Operand.mem (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) : Operand 32).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (4 + am.tail.length) (n := 32)
      (segBase (r.read s) + am.addrAt s (4 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 0 reg) : Operand 32).read s,
        cmpSpec ((Operand.reg 0 : Operand 32).read s)
          ((Operand.mem (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) : Operand 32).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) (32 / 8), .flags, .rip],
        x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) (32 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_m32_r32_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 4 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 32).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 32).read s) = c)
      (codeRange p (r.prefixByte :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMRSegEffect p (4 + am.tail.length) 32 base
        (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMRSegEffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.store.code
    (by simp; omega))
    (cmpxchg_m32_r32_seg_effect_step p r base reg am hv hx hb c)

theorem cmpxchg_m32_r32_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 4 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 32).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 32).read s) = c)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (cmpxchgMRSegEffect p (5 + am.tail.length) 32 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
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
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := cmpxchg_m_r_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix))
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
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 32).read s =
        (Operand.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) : Operand 32).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 32) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 32).read s =
        (Operand.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) : Operand 32).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (5 + am.tail.length) (n := 32)
      (segBase (r.read s) + am.addrAt s (5 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 32).read s,
        cmpSpec ((Operand.reg 0 : Operand 32).read s)
          ((Operand.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) : Operand 32).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (5 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) (32 / 8), .flags, .rip],
        x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) (32 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_m32_r32_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 4 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 32).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 32).read s) = c)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMRSegEffect p (5 + am.tail.length) 32 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMRSegEffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.store.code
    (by simp; omega))
    (cmpxchg_m32_r32_rex_seg_effect_step p r base rex hrex reg am hv hx hb c)

theorem cmpxchg_m16_r16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 2 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 16).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 16).read s) = c)
      (codeRange p (r.prefixByte :: 0x66 :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (cmpxchgMRSegEffect p (5 + am.tail.length) 16 base
        (gprNumber 0 0 reg) am c) := by
  intro s h hcode ⟨hpre, hc⟩
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
  have hstep := cmpxchg_m16_r16_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66))
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
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 16).read s =
        (Operand.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) : Operand 16).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 16) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 16).read s =
        (Operand.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) : Operand 16).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (5 + am.tail.length) (n := 16)
      (segBase (r.read s) + am.addrAt s (5 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 0 reg) : Operand 16).read s,
        cmpSpec ((Operand.reg 0 : Operand 16).read s)
          ((Operand.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) : Operand 16).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (5 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) (16 / 8), .flags, .rip],
        x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) (16 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_m16_r16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 2 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 16).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 16).read s) = c)
      (codeRange p (r.prefixByte :: 0x66 :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMRSegEffect p (5 + am.tail.length) 16 base
        (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMRSegEffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.store.code
    (by simp; omega))
    (cmpxchg_m16_r16_seg_effect_step p r base reg am hv hx hb c)

theorem cmpxchg_m16_r16_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 2 (6 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 16).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) :
          Operand 16).read s) = c)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (cmpxchgMRSegEffect p (6 + am.tail.length) 16 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hc⟩
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
  have hstep := cmpxchg_m16_r16_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix]))
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
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 16).read s =
        (Operand.mem (segBase (r.read s) + am.addrAt s (6 + am.tail.length)) : Operand 16).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 16) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 16).read s =
        (Operand.mem (segBase (r.read s) + am.addrAt s (6 + am.tail.length)) : Operand 16).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (6 + am.tail.length) (n := 16)
      (segBase (r.read s) + am.addrAt s (6 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 16).read s,
        cmpSpec ((Operand.reg 0 : Operand 16).read s)
          ((Operand.mem (segBase (r.read s) + am.addrAt s (6 + am.tail.length)) : Operand 16).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (6 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (6 + am.tail.length)) (16 / 8), .flags, .rip],
        x ∈ [Component.mem (segBase (r.read s) + am.addrAt s (6 + am.tail.length)) (16 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_m16_r16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 2 (6 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 16).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) :
          Operand 16).read s) = c)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMRSegEffect p (6 + am.tail.length) 16 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMRSegEffect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.store.code
    (by simp; omega))
    (cmpxchg_m16_r16_rex_seg_effect_step p r base rex hrex reg am hv hx hb c)

theorem cmpxchg_m64_r64_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => Rmw32Pre p am 8 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 64).read s) = c)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (cmpxchgMRA32Effect p (5 + am.tail.length) 64
        (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
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
  have hstep := cmpxchg_m_r_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix))
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
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (withAsz (rexContext s.DS rex.toBitVec)) (am.addrAt32 s (5 + am.tail.length)) = am.addrAt32 s (5 + am.tail.length) from rfl]
    at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 64).read s =
        (Operand.mem (am.addrAt32 s (5 + am.tail.length)) : Operand 64).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 64) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 64).read s =
        (Operand.mem (am.addrAt32 s (5 + am.tail.length)) : Operand 64).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (5 + am.tail.length) (n := 64)
      (am.addrAt32 s (5 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 64).read s,
        cmpSpec ((Operand.reg 0 : Operand 64).read s)
          ((Operand.mem (am.addrAt32 s (5 + am.tail.length)) : Operand 64).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (5 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (am.addrAt32 s (5 + am.tail.length)) (64 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt32 s (5 + am.tail.length)) (64 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_m64_r64_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 8 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 64).read s) = c)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMRA32Effect p (5 + am.tail.length) 64
        (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMRA32Effect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.code
    (by simp; omega))
    (cmpxchg_m64_r64_a32_effect_step p rex hrex reg am hv hx hb c)

theorem cmpxchg_m32_r32_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => Rmw32Pre p am 4 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 32).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 32).read s) = c)
      (codeRange p (0x67 :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (cmpxchgMRA32Effect p (4 + am.tail.length) 32
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
  have hstep := cmpxchg_m_r_a32_step s h [0x67] (scanPrefix_asz_cons (by simp))
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
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])) (am.addrAt32 s (4 + am.tail.length)) = am.addrAt32 s (4 + am.tail.length) from rfl]
    at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 32).read s =
        (Operand.mem (am.addrAt32 s (4 + am.tail.length)) : Operand 32).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 32) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 32).read s =
        (Operand.mem (am.addrAt32 s (4 + am.tail.length)) : Operand 32).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (4 + am.tail.length) (n := 32)
      (am.addrAt32 s (4 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 0 reg) : Operand 32).read s,
        cmpSpec ((Operand.reg 0 : Operand 32).read s)
          ((Operand.mem (am.addrAt32 s (4 + am.tail.length)) : Operand 32).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (am.addrAt32 s (4 + am.tail.length)) (32 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt32 s (4 + am.tail.length)) (32 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_m32_r32_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 4 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 32).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 32).read s) = c)
      (codeRange p (0x67 :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMRA32Effect p (4 + am.tail.length) 32
        (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMRA32Effect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.code
    (by simp; omega))
    (cmpxchg_m32_r32_a32_effect_step p reg am hv hx hb c)

theorem cmpxchg_m32_r32_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => Rmw32Pre p am 4 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 32).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 32).read s) = c)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (cmpxchgMRA32Effect p (5 + am.tail.length) 32
        (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
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
  have hstep := cmpxchg_m_r_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix))
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
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (withAsz (rexContext s.DS rex.toBitVec)) (am.addrAt32 s (5 + am.tail.length)) = am.addrAt32 s (5 + am.tail.length) from rfl]
    at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 32).read s =
        (Operand.mem (am.addrAt32 s (5 + am.tail.length)) : Operand 32).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 32) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 32).read s =
        (Operand.mem (am.addrAt32 s (5 + am.tail.length)) : Operand 32).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (5 + am.tail.length) (n := 32)
      (am.addrAt32 s (5 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 32).read s,
        cmpSpec ((Operand.reg 0 : Operand 32).read s)
          ((Operand.mem (am.addrAt32 s (5 + am.tail.length)) : Operand 32).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (5 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (am.addrAt32 s (5 + am.tail.length)) (32 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt32 s (5 + am.tail.length)) (32 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_m32_r32_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 4 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 32).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 32).read s) = c)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMRA32Effect p (5 + am.tail.length) 32
        (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMRA32Effect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.code
    (by simp; omega))
    (cmpxchg_m32_r32_rex_a32_effect_step p rex hrex reg am hv hx hb c)

theorem cmpxchg_m16_r16_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s => Rmw32Pre p am 2 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 16).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 16).read s) = c)
      (codeRange p (0x67 :: 0x66 :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (cmpxchgMRA32Effect p (5 + am.tail.length) 16
        (gprNumber 0 0 reg) am c) := by
  intro s h hcode ⟨hpre, hc⟩
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
  have hstep := cmpxchg_m16_r16_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66))
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
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66])) (am.addrAt32 s (5 + am.tail.length)) = am.addrAt32 s (5 + am.tail.length) from rfl]
    at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 16).read s =
        (Operand.mem (am.addrAt32 s (5 + am.tail.length)) : Operand 16).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 16) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 16).read s =
        (Operand.mem (am.addrAt32 s (5 + am.tail.length)) : Operand 16).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (5 + am.tail.length) (n := 16)
      (am.addrAt32 s (5 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 0 reg) : Operand 16).read s,
        cmpSpec ((Operand.reg 0 : Operand 16).read s)
          ((Operand.mem (am.addrAt32 s (5 + am.tail.length)) : Operand 16).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (5 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (am.addrAt32 s (5 + am.tail.length)) (16 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt32 s (5 + am.tail.length)) (16 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_m16_r16_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 2 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 16).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 16).read s) = c)
      (codeRange p (0x67 :: 0x66 :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMRA32Effect p (5 + am.tail.length) 16
        (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMRA32Effect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.code
    (by simp; omega))
    (cmpxchg_m16_r16_a32_effect_step p reg am hv hx hb c)

theorem cmpxchg_m16_r16_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s => Rmw32Pre p am 2 (6 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 16).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) :
          Operand 16).read s) = c)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (cmpxchgMRA32Effect p (6 + am.tail.length) 16
        (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hc⟩
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
  have hstep := cmpxchg_m16_r16_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix]))
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
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
  rw [show segAddr (withAsz (oszRexContext s.DS rex.toBitVec)) (am.addrAt32 s (6 + am.tail.length)) = am.addrAt32 s (6 + am.tail.length) from rfl]
    at hstep
  cases c
  · have hne : ¬(Operand.reg 0 : Operand 16).read s =
        (Operand.mem (am.addrAt32 s (6 + am.tail.length)) : Operand 16).read s :=
      fun h' => (beq_eq_false_iff_ne.mp hc) h'
    simp only [eq_false hne, ↓reduceIte] at hstep
    refine ⟨_, hstep, ReadyToStep.afterStep_rmwReg h _ _ _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmwReg_rip h _ _ _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        AgreesExcept.afterStep_rmwReg s _ _ _ _ _ _ _⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      refine ⟨Operand.read_afterStep_rmwReg_mem (n := 16) s _ (by decide) (by decide) _ _ _ _ _ _,
        ?_⟩
      rw [Operand.read_afterStep_rmwReg_reg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · exact StatusFlagsOutcome.allows_ofStatusFlags _
  · have heq : (Operand.reg 0 : Operand 16).read s =
        (Operand.mem (am.addrAt32 s (6 + am.tail.length)) : Operand 16).read s :=
      beq_iff_eq.mp hc
    simp only [eq_true heq, ↓reduceIte] at hstep
    have hag := AgreesExcept.afterStep_rmw s (6 + am.tail.length) (n := 16)
      (am.addrAt32 s (6 + am.tail.length))
      (fun _ => ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 16).read s,
        cmpSpec ((Operand.reg 0 : Operand 16).read s)
          ((Operand.mem (am.addrAt32 s (6 + am.tail.length)) : Operand 16).read s))) 0
      (BitVec.add s.RIP (BitVec.ofNat 64 (6 + am.tail.length)))
    have hsub : ∀ x ∈ [Component.mem (am.addrAt32 s (6 + am.tail.length)) (16 / 8), .flags, .rip],
        x ∈ [Component.mem (am.addrAt32 s (6 + am.tail.length)) (16 / 8), .reg 0, .flags, .rip] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
      ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
        hag.mono hsub⟩⟩
    · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
      exact ⟨Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _,
        hag.read (by simp)⟩
    · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpxchg_m16_r16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 2 (6 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 16).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) :
          Operand 16).read s) = c)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: 0xB1 :: am.modrm reg :: am.tail))
      (Effect.post (cmpxchgMRA32Effect p (6 + am.tail.length) 16
        (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [cmpxchgMRA32Effect_components]; exact mem_components_rmwReg _ _ _)
    hpre.1.code
    (by simp; omega))
    (cmpxchg_m16_r16_rex_a32_effect_step p rex hrex reg am hv hx hb c)

theorem cmpxchg_m64_r64_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (c : Bool) :
    Triple (fun s => RmwPre p am 8 (4 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) :
          Operand 64).read s) = c)
      (codeRange p (encodeCmpxchgM64R64 src am))
      (Effect.post (cmpxchgMREffect p (4 + am.tail.length) 64 (src.setWidth 5) am c)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := cmpxchg_m64_r64_triple_of_bytes p _ hrex (regLow src) am hv hx hb c
  rwa [hr, gprNumber_reg] at this

theorem cmpxchg_m32_r32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (c : Bool) :
    Triple (fun s => RmwPre p am 4 (encodeCmpxchgM32R32 src am).length s ∧
      ((Operand.reg 0 : Operand 32).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (encodeCmpxchgM32R32 src am).length)) :
          Operand 32).read s) = c)
      (codeRange p (encodeCmpxchgM32R32 src am))
      (Effect.post
        (cmpxchgMREffect p (encodeCmpxchgM32R32 src am).length 32 (src.setWidth 5) am c)) := by
  unfold encodeCmpxchgM32R32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := cmpxchg_m32_r32_triple_of_bytes p (regLow src) am hv hx hb c
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := cmpxchg_m32_r32_rex_triple_of_bytes p _ hrex (regLow src) am hv hx hb c
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem cmpxchg_m16_r16_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (c : Bool) :
    Triple (fun s => RmwPre p am 2 (encodeCmpxchgM16R16 src am).length s ∧
      ((Operand.reg 0 : Operand 16).read s ==
        (Operand.mem (am.addr s (p + BitVec.ofNat 64 (encodeCmpxchgM16R16 src am).length)) :
          Operand 16).read s) = c)
      (codeRange p (encodeCmpxchgM16R16 src am))
      (Effect.post
        (cmpxchgMREffect p (encodeCmpxchgM16R16 src am).length 16 (src.setWidth 5) am c)) := by
  unfold encodeCmpxchgM16R16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := cmpxchg_m16_r16_triple_of_bytes p (regLow src) am hv hx hb c
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := cmpxchg_m16_r16_rex_triple_of_bytes p _ hrex (regLow src) am hv hx hb c
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

theorem cmpxchg_m64_r64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 8 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 64).read s) = c)
      (codeRange p (r.prefixByte :: encodeCmpxchgM64R64 src am))
      (Effect.post (cmpxchgMRSegEffect p (5 + am.tail.length) 64 base (src.setWidth 5) am c)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := cmpxchg_m64_r64_seg_triple_of_bytes p r base _ hrex (regLow src) am hv hx hb c
  rwa [hr, gprNumber_reg] at this

theorem cmpxchg_m32_r32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 4 (r.prefixByte :: encodeCmpxchgM32R32 src am).length s ∧
      ((Operand.reg 0 : Operand 32).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeCmpxchgM32R32 src am).length)) :
          Operand 32).read s) = c)
      (codeRange p (r.prefixByte :: encodeCmpxchgM32R32 src am))
      (Effect.post (cmpxchgMRSegEffect p (r.prefixByte :: encodeCmpxchgM32R32 src am).length 32 base
        (src.setWidth 5) am c)) := by
  unfold encodeCmpxchgM32R32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := cmpxchg_m32_r32_seg_triple_of_bytes p r base (regLow src) am hv hx hb c
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := cmpxchg_m32_r32_rex_seg_triple_of_bytes p r base _ hrex (regLow src) am
      hv hx hb c
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

theorem cmpxchg_m16_r16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s => SegRmwPre p r base am 2 (r.prefixByte :: encodeCmpxchgM16R16 src am).length s ∧
      ((Operand.reg 0 : Operand 16).read s ==
        (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeCmpxchgM16R16 src am).length)) :
          Operand 16).read s) = c)
      (codeRange p (r.prefixByte :: encodeCmpxchgM16R16 src am))
      (Effect.post (cmpxchgMRSegEffect p (r.prefixByte :: encodeCmpxchgM16R16 src am).length 16 base
        (src.setWidth 5) am c)) := by
  unfold encodeCmpxchgM16R16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := cmpxchg_m16_r16_seg_triple_of_bytes p r base (regLow src) am hv hx hb c
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := cmpxchg_m16_r16_rex_seg_triple_of_bytes p r base _ hrex (regLow src) am
      hv hx hb c
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 + 1 = 6 + am.tail.length by omega]

theorem cmpxchg_m64_r64_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 8 (5 + am.tail.length) s ∧
      ((Operand.reg 0 : Operand 64).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) :
          Operand 64).read s) = c)
      (codeRange p (0x67 :: encodeCmpxchgM64R64 src am))
      (Effect.post (cmpxchgMRA32Effect p (5 + am.tail.length) 64 (src.setWidth 5) am c)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := cmpxchg_m64_r64_a32_triple_of_bytes p _ hrex (regLow src) am hv hx hb c
  rwa [hr, gprNumber_reg] at this

theorem cmpxchg_m32_r32_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 4 (0x67 :: encodeCmpxchgM32R32 src am).length s ∧
      ((Operand.reg 0 : Operand 32).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeCmpxchgM32R32 src am).length)) :
          Operand 32).read s) = c)
      (codeRange p (0x67 :: encodeCmpxchgM32R32 src am))
      (Effect.post
        (cmpxchgMRA32Effect p (0x67 :: encodeCmpxchgM32R32 src am).length 32 (src.setWidth 5) am c)) := by
  unfold encodeCmpxchgM32R32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := cmpxchg_m32_r32_a32_triple_of_bytes p (regLow src) am hv hx hb c
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := cmpxchg_m32_r32_rex_a32_triple_of_bytes p _ hrex (regLow src) am hv hx
      hb c
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

theorem cmpxchg_m16_r16_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (c : Bool) :
    Triple (fun s => Rmw32Pre p am 2 (0x67 :: encodeCmpxchgM16R16 src am).length s ∧
      ((Operand.reg 0 : Operand 16).read s ==
        (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeCmpxchgM16R16 src am).length)) :
          Operand 16).read s) = c)
      (codeRange p (0x67 :: encodeCmpxchgM16R16 src am))
      (Effect.post
        (cmpxchgMRA32Effect p (0x67 :: encodeCmpxchgM16R16 src am).length 16 (src.setWidth 5) am c)) := by
  unfold encodeCmpxchgM16R16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := cmpxchg_m16_r16_a32_triple_of_bytes p (regLow src) am hv hx hb c
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := cmpxchg_m16_r16_rex_a32_triple_of_bytes p _ hrex (regLow src) am hv hx
      hb c
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 + 1 = 6 + am.tail.length by omega]

attribute [x86_compose] cmpxchgMREffect

theorem cmpxchgMREffect_local {p : BitVec 64} {len n : Nat} {src : BitVec 5} {am : AddrMode}
    {c : Bool}
    (hn : n % 8 = 0) :
    Effect.Local (cmpxchgMREffect p len n src am c) := by
  effect_local [cmpxchgMREffect, hn]

@[x86_local] theorem cmpxchgMREffect_local64 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} {c : Bool} :
    Effect.Local (cmpxchgMREffect p len 64 src am c) :=
  cmpxchgMREffect_local (by decide)

@[x86_local] theorem cmpxchgMREffect_local32 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} {c : Bool} :
    Effect.Local (cmpxchgMREffect p len 32 src am c) :=
  cmpxchgMREffect_local (by decide)

@[x86_local] theorem cmpxchgMREffect_local16 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} {c : Bool} :
    Effect.Local (cmpxchgMREffect p len 16 src am c) :=
  cmpxchgMREffect_local (by decide)

@[x86_local] theorem cmpxchgMREffect_local8 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} {c : Bool} :
    Effect.Local (cmpxchgMREffect p len 8 src am c) :=
  cmpxchgMREffect_local (by decide)

attribute [x86_compose] cmpxchgMRSegEffect

theorem cmpxchgMRSegEffect_local {p : BitVec 64} {len n : Nat} {base : BitVec 64} {src : BitVec 5}
    {am : AddrMode} {c : Bool} (hn : n % 8 = 0) :
    Effect.Local (cmpxchgMRSegEffect p len n base src am c) := by
  effect_local [cmpxchgMRSegEffect, hn]

@[x86_local] theorem cmpxchgMRSegEffect_local64 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 5} {am : AddrMode} {c : Bool} :
    Effect.Local (cmpxchgMRSegEffect p len 64 base src am c) :=
  cmpxchgMRSegEffect_local (by decide)

@[x86_local] theorem cmpxchgMRSegEffect_local32 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 5} {am : AddrMode} {c : Bool} :
    Effect.Local (cmpxchgMRSegEffect p len 32 base src am c) :=
  cmpxchgMRSegEffect_local (by decide)

@[x86_local] theorem cmpxchgMRSegEffect_local16 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 5} {am : AddrMode} {c : Bool} :
    Effect.Local (cmpxchgMRSegEffect p len 16 base src am c) :=
  cmpxchgMRSegEffect_local (by decide)

@[x86_local] theorem cmpxchgMRSegEffect_local8 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 5} {am : AddrMode} {c : Bool} :
    Effect.Local (cmpxchgMRSegEffect p len 8 base src am c) :=
  cmpxchgMRSegEffect_local (by decide)

attribute [x86_compose] cmpxchgMRA32Effect

theorem cmpxchgMRA32Effect_local {p : BitVec 64} {len n : Nat} {src : BitVec 5}
    {am : AddrMode} {c : Bool} (hn : n % 8 = 0) :
    Effect.Local (cmpxchgMRA32Effect p len n src am c) := by
  effect_local [cmpxchgMRA32Effect, hn]

@[x86_local] theorem cmpxchgMRA32Effect_local64 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} {c : Bool} :
    Effect.Local (cmpxchgMRA32Effect p len 64 src am c) :=
  cmpxchgMRA32Effect_local (by decide)

@[x86_local] theorem cmpxchgMRA32Effect_local32 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} {c : Bool} :
    Effect.Local (cmpxchgMRA32Effect p len 32 src am c) :=
  cmpxchgMRA32Effect_local (by decide)

@[x86_local] theorem cmpxchgMRA32Effect_local16 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} {c : Bool} :
    Effect.Local (cmpxchgMRA32Effect p len 16 src am c) :=
  cmpxchgMRA32Effect_local (by decide)

@[x86_local] theorem cmpxchgMRA32Effect_local8 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} {c : Bool} :
    Effect.Local (cmpxchgMRA32Effect p len 8 src am c) :=
  cmpxchgMRA32Effect_local (by decide)

end X86Proofs
