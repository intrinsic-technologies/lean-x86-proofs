import X86Proofs.Instructions.Xchg.Generated.MR.Step
import X86Proofs.Instructions.Xchg.Generated.MR.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def xchgMREffect (p : BitVec 64) (len n : Nat) (src : BitVec 5) (am : AddrMode) (s : RamState) :
    Effect :=
  let a := am.addr s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand n).read s
  let y := (Operand.reg src : Operand n).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand n), y⟩,
      ⟨(Operand.reg src : Operand 64), mergeGPR n x ((Operand.reg src : Operand 64).read s)⟩] }

@[simp] theorem xchgMREffect_components (p : BitVec 64) (len n : Nat) (src : BitVec 5)
    (am : AddrMode) (s : RamState) : (xchgMREffect p len n src am s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) (n / 8), .reg src, .rip] := rfl

def xchgMRSegEffect (p : BitVec 64) (len n : Nat) (base : BitVec 64) (src : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := base + am.addr s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand n).read s
  let y := (Operand.reg src : Operand n).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand n), y⟩,
      ⟨(Operand.reg src : Operand 64), mergeGPR n x ((Operand.reg src : Operand 64).read s)⟩] }

@[simp] theorem xchgMRSegEffect_components (p : BitVec 64) (len n : Nat) (base : BitVec 64)
    (src : BitVec 5) (am : AddrMode) (s : RamState) :
    (xchgMRSegEffect p len n base src am s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) (n / 8), .reg src, .rip] := rfl

def xchgMRA32Effect (p : BitVec 64) (len n : Nat) (src : BitVec 5) (am : AddrMode) (s : RamState) :
    Effect :=
  let a := am.addr32 s (p + BitVec.ofNat 64 len)
  let x := (Operand.mem a : Operand n).read s
  let y := (Operand.reg src : Operand n).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand n), y⟩,
      ⟨(Operand.reg src : Operand 64), mergeGPR n x ((Operand.reg src : Operand 64).read s)⟩] }

@[simp] theorem xchgMRA32Effect_components (p : BitVec 64) (len n : Nat) (src : BitVec 5)
    (am : AddrMode) (s : RamState) : (xchgMRA32Effect p len n src am s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) (n / 8), .reg src, .rip] := rfl

theorem xchg_m64_r64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LockedRmwPre p am 8 (3 + am.tail.length))
      (codeRange p (rex :: 0x87 :: am.modrm reg :: am.tail))
      (xchgMREffect p (3 + am.tail.length) 64
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
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
  have hstep := xchg_m_r_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
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
  refine ⟨Operand.read_afterStep_rmwRegResult_mem (n := 64) s _ (by decide) (by decide) _ _ _ _ _,
    ?_⟩
  rw [Operand.read_afterStep_rmwRegResult_reg]
  rfl

theorem xchg_m64_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LockedRmwPre p am 8 (3 + am.tail.length))
      (codeRange p (rex :: 0x87 :: am.modrm reg :: am.tail))
      (Effect.post (xchgMREffect p (3 + am.tail.length) 64
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgMREffect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.code (by simp; omega))
    (xchg_m64_r64_effect_step p rex hrex reg am hv hx hb)

theorem xchg_m32_r32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LockedRmwPre p am 4 (2 + am.tail.length))
      (codeRange p (0x87 :: am.modrm reg :: am.tail))
      (xchgMREffect p (2 + am.tail.length) 32
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
  have hstep := xchg_m_r_step s h [] (by simp)
    (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) reg am hv
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
  refine ⟨Operand.read_afterStep_rmwRegResult_mem (n := 32) s _ (by decide) (by decide) _ _ _ _ _,
    ?_⟩
  rw [Operand.read_afterStep_rmwRegResult_reg]
  rfl

theorem xchg_m32_r32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LockedRmwPre p am 4 (2 + am.tail.length))
      (codeRange p (0x87 :: am.modrm reg :: am.tail))
      (Effect.post (xchgMREffect p (2 + am.tail.length) 32
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgMREffect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.code (by simp; omega))
    (xchg_m32_r32_effect_step p reg am hv hx hb)

theorem xchg_m32_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LockedRmwPre p am 4 (3 + am.tail.length))
      (codeRange p (rex :: 0x87 :: am.modrm reg :: am.tail))
      (xchgMREffect p (3 + am.tail.length) 32
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
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
  have hstep := xchg_m_r_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
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
  refine ⟨Operand.read_afterStep_rmwRegResult_mem (n := 32) s _ (by decide) (by decide) _ _ _ _ _,
    ?_⟩
  rw [Operand.read_afterStep_rmwRegResult_reg]
  rfl

theorem xchg_m32_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LockedRmwPre p am 4 (3 + am.tail.length))
      (codeRange p (rex :: 0x87 :: am.modrm reg :: am.tail))
      (Effect.post (xchgMREffect p (3 + am.tail.length) 32
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgMREffect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.code (by simp; omega))
    (xchg_m32_r32_rex_effect_step p rex hrex reg am hv hx hb)

theorem xchg_m16_r16_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LockedRmwPre p am 2 (3 + am.tail.length))
      (codeRange p (0x66 :: 0x87 :: am.modrm reg :: am.tail))
      (xchgMREffect p (3 + am.tail.length) 16
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
  have hstep := xchg_m16_r16_step s h [0x66] (by simpa using scanPrefix_66)
    (by simp)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) reg am hv
    (by exact (AddrContext.osz _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
    (by exact hlk)
  dsimp only at hstep
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwRegResult h _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwRegResult_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_rmwRegResult s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  refine ⟨Operand.read_afterStep_rmwRegResult_mem (n := 16) s _ (by decide) (by decide) _ _ _ _ _,
    ?_⟩
  rw [Operand.read_afterStep_rmwRegResult_reg]
  rfl

theorem xchg_m16_r16_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LockedRmwPre p am 2 (3 + am.tail.length))
      (codeRange p (0x66 :: 0x87 :: am.modrm reg :: am.tail))
      (Effect.post (xchgMREffect p (3 + am.tail.length) 16
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgMREffect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.code (by simp; omega))
    (xchg_m16_r16_effect_step p reg am hv hx hb)

theorem xchg_m16_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LockedRmwPre p am 2 (4 + am.tail.length))
      (codeRange p (0x66 :: rex :: 0x87 :: am.modrm reg :: am.tail))
      (xchgMREffect p (4 + am.tail.length) 16
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
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
  have hstep := xchg_m16_r16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix])
    (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_66_rex _ _ hr]; exact (AddrContext.oszRex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_66_rex _ _ hr]; exact hread)
    (by rw [scanContext_66_rex _ _ hr]; exact hlk)
  simp only [scanContext_66_rex _ _ hr] at hstep
  have hsrc : gprNumber (oszRexContext s.DS rex.toBitVec).rex_r4
      (oszRexContext s.DS rex.toBitVec).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwRegResult h _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwRegResult_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_rmwRegResult s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  refine ⟨Operand.read_afterStep_rmwRegResult_mem (n := 16) s _ (by decide) (by decide) _ _ _ _ _,
    ?_⟩
  rw [Operand.read_afterStep_rmwRegResult_reg]
  rfl

theorem xchg_m16_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LockedRmwPre p am 2 (4 + am.tail.length))
      (codeRange p (0x66 :: rex :: 0x87 :: am.modrm reg :: am.tail))
      (Effect.post (xchgMREffect p (4 + am.tail.length) 16
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgMREffect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.code (by simp; omega))
    (xchg_m16_r16_rex_effect_step p rex hrex reg am hv hx hb)

theorem xchg_m64_r64_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegLockedRmwPre p r base am 8 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0x87 :: am.modrm reg :: am.tail))
      (xchgMRSegEffect p (4 + am.tail.length) 64 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
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
  have hstep := xchg_m_r_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix))
    (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
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
  refine ⟨Operand.read_afterStep_rmwRegResult_mem (n := 64) s _ (by decide) (by decide) _ _ _ _ _,
    ?_⟩
  rw [Operand.read_afterStep_rmwRegResult_reg]
  rfl

theorem xchg_m64_r64_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegLockedRmwPre p r base am 8 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0x87 :: am.modrm reg :: am.tail))
      (Effect.post (xchgMRSegEffect p (4 + am.tail.length) 64 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgMRSegEffect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.store.code (by simp; omega))
    (xchg_m64_r64_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem xchg_m32_r32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SegLockedRmwPre p r base am 4 (3 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x87 :: am.modrm reg :: am.tail))
      (xchgMRSegEffect p (3 + am.tail.length) 32 base
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
  have hstep := xchg_m_r_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp))
    (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
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
  refine ⟨Operand.read_afterStep_rmwRegResult_mem (n := 32) s _ (by decide) (by decide) _ _ _ _ _,
    ?_⟩
  rw [Operand.read_afterStep_rmwRegResult_reg]
  rfl

theorem xchg_m32_r32_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegLockedRmwPre p r base am 4 (3 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x87 :: am.modrm reg :: am.tail))
      (Effect.post (xchgMRSegEffect p (3 + am.tail.length) 32 base
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgMRSegEffect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.store.code (by simp; omega))
    (xchg_m32_r32_seg_effect_step p r base reg am hv hx hb)

theorem xchg_m32_r32_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegLockedRmwPre p r base am 4 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0x87 :: am.modrm reg :: am.tail))
      (xchgMRSegEffect p (4 + am.tail.length) 32 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
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
  have hstep := xchg_m_r_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix))
    (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
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
  refine ⟨Operand.read_afterStep_rmwRegResult_mem (n := 32) s _ (by decide) (by decide) _ _ _ _ _,
    ?_⟩
  rw [Operand.read_afterStep_rmwRegResult_reg]
  rfl

theorem xchg_m32_r32_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegLockedRmwPre p r base am 4 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0x87 :: am.modrm reg :: am.tail))
      (Effect.post (xchgMRSegEffect p (4 + am.tail.length) 32 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgMRSegEffect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.store.code (by simp; omega))
    (xchg_m32_r32_rex_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem xchg_m16_r16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SegLockedRmwPre p r base am 2 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: 0x87 :: am.modrm reg :: am.tail))
      (xchgMRSegEffect p (4 + am.tail.length) 16 base
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
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66]
      (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := xchg_m16_r16_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66))
    (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
    (by rw [hsc, segAddr_withSeg]; exact hlk)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwRegResult h _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwRegResult_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_rmwRegResult s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  refine ⟨Operand.read_afterStep_rmwRegResult_mem (n := 16) s _ (by decide) (by decide) _ _ _ _ _,
    ?_⟩
  rw [Operand.read_afterStep_rmwRegResult_reg]
  rfl

theorem xchg_m16_r16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegLockedRmwPre p r base am 2 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: 0x87 :: am.modrm reg :: am.tail))
      (Effect.post (xchgMRSegEffect p (4 + am.tail.length) 16 base
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgMRSegEffect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.store.code (by simp; omega))
    (xchg_m16_r16_seg_effect_step p r base reg am hv hx hb)

theorem xchg_m16_r16_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegLockedRmwPre p r base am 2 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x87 :: am.modrm reg :: am.tail))
      (xchgMRSegEffect p (5 + am.tail.length) 16 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
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
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66, rex] =
      withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66, rex]
      (noSegPrefix_cons noSegPrefix_66 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_66_rex _ _ hr]
  have hstep := xchg_m16_r16_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix]))
    (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
    (by rw [hsc, segAddr_withSeg]; exact hlk)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwRegResult h _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwRegResult_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_rmwRegResult s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  refine ⟨Operand.read_afterStep_rmwRegResult_mem (n := 16) s _ (by decide) (by decide) _ _ _ _ _,
    ?_⟩
  rw [Operand.read_afterStep_rmwRegResult_reg]
  rfl

theorem xchg_m16_r16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegLockedRmwPre p r base am 2 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x87 :: am.modrm reg :: am.tail))
      (Effect.post (xchgMRSegEffect p (5 + am.tail.length) 16 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgMRSegEffect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.store.code (by simp; omega))
    (xchg_m16_r16_rex_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem xchg_m64_r64_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LockedRmw32Pre p am 8 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0x87 :: am.modrm reg :: am.tail))
      (xchgMRA32Effect p (4 + am.tail.length) 64
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
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
  have hstep := xchg_m_r_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix))
    (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
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
  refine ⟨Operand.read_afterStep_rmwRegResult_mem (n := 64) s _ (by decide) (by decide) _ _ _ _ _,
    ?_⟩
  rw [Operand.read_afterStep_rmwRegResult_reg]
  rfl

theorem xchg_m64_r64_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LockedRmw32Pre p am 8 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0x87 :: am.modrm reg :: am.tail))
      (Effect.post (xchgMRA32Effect p (4 + am.tail.length) 64
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgMRA32Effect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.code (by simp; omega))
    (xchg_m64_r64_a32_effect_step p rex hrex reg am hv hx hb)

theorem xchg_m32_r32_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LockedRmw32Pre p am 4 (3 + am.tail.length))
      (codeRange p (0x67 :: 0x87 :: am.modrm reg :: am.tail))
      (xchgMRA32Effect p (3 + am.tail.length) 32
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
  have hstep := xchg_m_r_a32_step s h [0x67] (scanPrefix_asz_cons (by simp))
    (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
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
  refine ⟨Operand.read_afterStep_rmwRegResult_mem (n := 32) s _ (by decide) (by decide) _ _ _ _ _,
    ?_⟩
  rw [Operand.read_afterStep_rmwRegResult_reg]
  rfl

theorem xchg_m32_r32_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LockedRmw32Pre p am 4 (3 + am.tail.length))
      (codeRange p (0x67 :: 0x87 :: am.modrm reg :: am.tail))
      (Effect.post (xchgMRA32Effect p (3 + am.tail.length) 32
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgMRA32Effect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.code (by simp; omega))
    (xchg_m32_r32_a32_effect_step p reg am hv hx hb)

theorem xchg_m32_r32_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LockedRmw32Pre p am 4 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0x87 :: am.modrm reg :: am.tail))
      (xchgMRA32Effect p (4 + am.tail.length) 32
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
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
  have hstep := xchg_m_r_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix))
    (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
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
  refine ⟨Operand.read_afterStep_rmwRegResult_mem (n := 32) s _ (by decide) (by decide) _ _ _ _ _,
    ?_⟩
  rw [Operand.read_afterStep_rmwRegResult_reg]
  rfl

theorem xchg_m32_r32_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LockedRmw32Pre p am 4 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0x87 :: am.modrm reg :: am.tail))
      (Effect.post (xchgMRA32Effect p (4 + am.tail.length) 32
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgMRA32Effect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.code (by simp; omega))
    (xchg_m32_r32_rex_a32_effect_step p rex hrex reg am hv hx hb)

theorem xchg_m16_r16_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LockedRmw32Pre p am 2 (4 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: 0x87 :: am.modrm reg :: am.tail))
      (xchgMRA32Effect p (4 + am.tail.length) 16
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
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66]) := by
    rw [scanContext_asz_cons]
  have hstep := xchg_m16_r16_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66))
    (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
    (by rw [hsc]; exact hlk)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66])).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwRegResult h _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwRegResult_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_rmwRegResult s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  refine ⟨Operand.read_afterStep_rmwRegResult_mem (n := 16) s _ (by decide) (by decide) _ _ _ _ _,
    ?_⟩
  rw [Operand.read_afterStep_rmwRegResult_reg]
  rfl

theorem xchg_m16_r16_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LockedRmw32Pre p am 2 (4 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: 0x87 :: am.modrm reg :: am.tail))
      (Effect.post (xchgMRA32Effect p (4 + am.tail.length) 16
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgMRA32Effect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.code (by simp; omega))
    (xchg_m16_r16_a32_effect_step p reg am hv hx hb)

theorem xchg_m16_r16_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LockedRmw32Pre p am 2 (5 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: rex :: 0x87 :: am.modrm reg :: am.tail))
      (xchgMRA32Effect p (5 + am.tail.length) 16
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
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
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, rex] =
      withAsz (oszRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_66_rex _ _ hr]
  have hstep := xchg_m16_r16_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix]))
    (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
    (by rw [hsc]; exact hlk)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (oszRexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (oszRexContext s.DS rex.toBitVec)).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwRegResult h _ _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmwRegResult_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_rmwRegResult s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  refine ⟨Operand.read_afterStep_rmwRegResult_mem (n := 16) s _ (by decide) (by decide) _ _ _ _ _,
    ?_⟩
  rw [Operand.read_afterStep_rmwRegResult_reg]
  rfl

theorem xchg_m16_r16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LockedRmw32Pre p am 2 (5 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: rex :: 0x87 :: am.modrm reg :: am.tail))
      (Effect.post (xchgMRA32Effect p (5 + am.tail.length) 16
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xchgMRA32Effect_components]; exact mem_components_rmwRegResult _ _ _)
    hpre.rmw.code (by simp; omega))
    (xchg_m16_r16_rex_a32_effect_step p rex hrex reg am hv hx hb)

theorem xchg_m64_r64_triple [Bindings] (p : BitVec 64) (src : BitVec 4)
    (am : AddrMode) (hv : am.Valid) :
    Triple (LockedRmwPre p am 8 (3 + am.tail.length))
      (codeRange p (encodeXchgM64R64 src am))
      (Effect.post (xchgMREffect p (3 + am.tail.length) 64 (src.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := xchg_m64_r64_triple_of_bytes p _ hrex (regLow src) am hv hx hb
  rwa [hr, gprNumber_reg] at this

theorem xchg_m32_r32_triple [Bindings] (p : BitVec 64) (src : BitVec 4)
    (am : AddrMode) (hv : am.Valid) :
    Triple (LockedRmwPre p am 4 (encodeXchgM32R32 src am).length)
      (codeRange p (encodeXchgM32R32 src am))
      (Effect.post (xchgMREffect p (encodeXchgM32R32 src am).length 32 (src.setWidth 5) am)) := by
  unfold encodeXchgM32R32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := xchg_m32_r32_triple_of_bytes p (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 = 2 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := xchg_m32_r32_rex_triple_of_bytes p _ hrex (regLow src) am hv
      hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]

theorem xchg_m16_r16_triple [Bindings] (p : BitVec 64) (src : BitVec 4)
    (am : AddrMode) (hv : am.Valid) :
    Triple (LockedRmwPre p am 2 (encodeXchgM16R16 src am).length)
      (codeRange p (encodeXchgM16R16 src am))
      (Effect.post (xchgMREffect p (encodeXchgM16R16 src am).length 16 (src.setWidth 5) am)) := by
  unfold encodeXchgM16R16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := xchg_m16_r16_triple_of_bytes p (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := xchg_m16_r16_rex_triple_of_bytes p _ hrex (regLow src) am hv
      hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem xchg_m64_r64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) (src : BitVec 4)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegLockedRmwPre p r base am 8 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: encodeXchgM64R64 src am))
      (Effect.post (xchgMRSegEffect p (4 + am.tail.length) 64 base (src.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := xchg_m64_r64_seg_triple_of_bytes p r base _ hrex (regLow src) am hv hx hb
  rwa [hr, gprNumber_reg] at this

theorem xchg_m32_r32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) (src : BitVec 4)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegLockedRmwPre p r base am 4 (r.prefixByte :: encodeXchgM32R32 src am).length)
      (codeRange p (r.prefixByte :: encodeXchgM32R32 src am))
      (Effect.post (xchgMRSegEffect p (r.prefixByte :: encodeXchgM32R32 src am).length 32 base (src.setWidth 5) am)) := by
  unfold encodeXchgM32R32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := xchg_m32_r32_seg_triple_of_bytes p r base (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := xchg_m32_r32_rex_seg_triple_of_bytes p r base _ hrex (regLow src) am hv
      hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem xchg_m16_r16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) (src : BitVec 4)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegLockedRmwPre p r base am 2 (r.prefixByte :: encodeXchgM16R16 src am).length)
      (codeRange p (r.prefixByte :: encodeXchgM16R16 src am))
      (Effect.post (xchgMRSegEffect p (r.prefixByte :: encodeXchgM16R16 src am).length 16 base (src.setWidth 5) am)) := by
  unfold encodeXchgM16R16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := xchg_m16_r16_seg_triple_of_bytes p r base (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := xchg_m16_r16_rex_seg_triple_of_bytes p r base _ hrex (regLow src) am hv
      hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

theorem xchg_m64_r64_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4)
    (am : AddrMode) (hv : am.Valid) :
    Triple (LockedRmw32Pre p am 8 (4 + am.tail.length))
      (codeRange p (0x67 :: encodeXchgM64R64 src am))
      (Effect.post (xchgMRA32Effect p (4 + am.tail.length) 64 (src.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := xchg_m64_r64_a32_triple_of_bytes p _ hrex (regLow src) am hv hx hb
  rwa [hr, gprNumber_reg] at this

theorem xchg_m32_r32_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4)
    (am : AddrMode) (hv : am.Valid) :
    Triple (LockedRmw32Pre p am 4 (0x67 :: encodeXchgM32R32 src am).length)
      (codeRange p (0x67 :: encodeXchgM32R32 src am))
      (Effect.post (xchgMRA32Effect p (0x67 :: encodeXchgM32R32 src am).length 32 (src.setWidth 5) am)) := by
  unfold encodeXchgM32R32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := xchg_m32_r32_a32_triple_of_bytes p (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := xchg_m32_r32_rex_a32_triple_of_bytes p _ hrex (regLow src) am hv
      hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem xchg_m16_r16_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4)
    (am : AddrMode) (hv : am.Valid) :
    Triple (LockedRmw32Pre p am 2 (0x67 :: encodeXchgM16R16 src am).length)
      (codeRange p (0x67 :: encodeXchgM16R16 src am))
      (Effect.post (xchgMRA32Effect p (0x67 :: encodeXchgM16R16 src am).length 16 (src.setWidth 5) am)) := by
  unfold encodeXchgM16R16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := xchg_m16_r16_a32_triple_of_bytes p (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := xchg_m16_r16_rex_a32_triple_of_bytes p _ hrex (regLow src) am hv
      hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

attribute [x86_compose] xchgMREffect xchgMRSegEffect xchgMRA32Effect

theorem xchgMREffect_local {p : BitVec 64} {len n : Nat} {src : BitVec 5} {am : AddrMode}
    (hn : n % 8 = 0) :
    Effect.Local (xchgMREffect p len n src am) := by
  effect_local [xchgMREffect, hn]

@[x86_local] theorem xchgMREffect_local64 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} : Effect.Local (xchgMREffect p len 64 src am) :=
  xchgMREffect_local (by decide)

@[x86_local] theorem xchgMREffect_local32 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} : Effect.Local (xchgMREffect p len 32 src am) :=
  xchgMREffect_local (by decide)

@[x86_local] theorem xchgMREffect_local16 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} : Effect.Local (xchgMREffect p len 16 src am) :=
  xchgMREffect_local (by decide)

@[x86_local] theorem xchgMREffect_local8 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} : Effect.Local (xchgMREffect p len 8 src am) :=
  xchgMREffect_local (by decide)

theorem xchgMRSegEffect_local {p : BitVec 64} {len n : Nat} {base : BitVec 64} {src : BitVec 5} {am : AddrMode}
    (hn : n % 8 = 0) :
    Effect.Local (xchgMRSegEffect p len n base src am) := by
  effect_local [xchgMRSegEffect, hn]

@[x86_local] theorem xchgMRSegEffect_local64 {p : BitVec 64} {len : Nat} {base : BitVec 64} {src : BitVec 5}
    {am : AddrMode} : Effect.Local (xchgMRSegEffect p len 64 base src am) :=
  xchgMRSegEffect_local (by decide)

@[x86_local] theorem xchgMRSegEffect_local32 {p : BitVec 64} {len : Nat} {base : BitVec 64} {src : BitVec 5}
    {am : AddrMode} : Effect.Local (xchgMRSegEffect p len 32 base src am) :=
  xchgMRSegEffect_local (by decide)

@[x86_local] theorem xchgMRSegEffect_local16 {p : BitVec 64} {len : Nat} {base : BitVec 64} {src : BitVec 5}
    {am : AddrMode} : Effect.Local (xchgMRSegEffect p len 16 base src am) :=
  xchgMRSegEffect_local (by decide)

@[x86_local] theorem xchgMRSegEffect_local8 {p : BitVec 64} {len : Nat} {base : BitVec 64} {src : BitVec 5}
    {am : AddrMode} : Effect.Local (xchgMRSegEffect p len 8 base src am) :=
  xchgMRSegEffect_local (by decide)

theorem xchgMRA32Effect_local {p : BitVec 64} {len n : Nat} {src : BitVec 5} {am : AddrMode}
    (hn : n % 8 = 0) :
    Effect.Local (xchgMRA32Effect p len n src am) := by
  effect_local [xchgMRA32Effect, hn]

@[x86_local] theorem xchgMRA32Effect_local64 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} : Effect.Local (xchgMRA32Effect p len 64 src am) :=
  xchgMRA32Effect_local (by decide)

@[x86_local] theorem xchgMRA32Effect_local32 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} : Effect.Local (xchgMRA32Effect p len 32 src am) :=
  xchgMRA32Effect_local (by decide)

@[x86_local] theorem xchgMRA32Effect_local16 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} : Effect.Local (xchgMRA32Effect p len 16 src am) :=
  xchgMRA32Effect_local (by decide)

@[x86_local] theorem xchgMRA32Effect_local8 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} : Effect.Local (xchgMRA32Effect p len 8 src am) :=
  xchgMRA32Effect_local (by decide)

end X86Proofs
