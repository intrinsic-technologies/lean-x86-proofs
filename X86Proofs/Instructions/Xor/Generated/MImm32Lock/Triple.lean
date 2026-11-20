import X86Proofs.Instructions.Xor.Generated.MImm32Lock.Step
import X86Proofs.Instructions.Xor.Generated.MImm32Lock.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Xor.Generated.MImm32.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem xor_lock_m64_imm32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (LockedRmwPre p am 8 (8 + am.tail.length))
      (codeRange p (0xF0 :: rex :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)))
      (xorMImm32Effect p (8 + am.tail.length) 64 am imm) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  have hlk := lockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (8 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := xor_lock_m_imm32_step s h [0xF0, rex] (scanPrefix_lock_cons (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; rfl) (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; exact ((AddrContext.rex _ _ am hx hb).withLock).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; exact hread)
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; exact hlk)
  simp only [scanContext_lock_cons, scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_lock_m64_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    Triple (LockedRmwPre p am 8 (8 + am.tail.length))
      (codeRange p (0xF0 :: rex :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (xorMImm32Effect p (8 + am.tail.length) 64 am imm)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorMImm32Effect_components]; exact mem_components_rmw _ _) hpre.rmw.code (by simp; omega))
    (xor_lock_m64_imm32_effect_step p rex hrex am hv hx hb imm)

theorem xor_lock_m32_imm32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) :
    StepEffect (LockedRmwPre p am 4 (7 + am.tail.length))
      (codeRange p (0xF0 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)))
      (xorMImm32Effect p (7 + am.tail.length) 32 am imm) := by
  intro s h hcode hpre
  have hlk := lockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := xor_lock_m_imm32_step s h [0xF0] (scanPrefix_lock_cons (by simp)) (by simp) 32 (.inr rfl)
    (by rw [scanContext_lock_cons]; exact rfl)
    (by rw [scanContext_lock_cons]; rfl) (by rw [scanContext_lock_cons]; rfl)
    (by rw [scanContext_lock_cons]; rfl) am hv
    (by rw [scanContext_lock_cons]; exact ((AddrContext.legacy _ am hx hb).withLock).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_lock_cons]; exact hread)
    (by rw [scanContext_lock_cons]; exact hlk)
  simp only [scanContext_lock_cons] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_lock_m32_imm32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) :
    Triple (LockedRmwPre p am 4 (7 + am.tail.length))
      (codeRange p (0xF0 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (xorMImm32Effect p (7 + am.tail.length) 32 am imm)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorMImm32Effect_components]; exact mem_components_rmw _ _) hpre.rmw.code (by simp; omega))
    (xor_lock_m32_imm32_effect_step p am hv hx hb imm)

theorem xor_lock_m32_imm32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (LockedRmwPre p am 4 (8 + am.tail.length))
      (codeRange p (0xF0 :: rex :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)))
      (xorMImm32Effect p (8 + am.tail.length) 32 am imm) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  have hlk := lockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (8 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := xor_lock_m_imm32_step s h [0xF0, rex] (scanPrefix_lock_cons (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; rfl) (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; exact ((AddrContext.rex _ _ am hx hb).withLock).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; exact hread)
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; exact hlk)
  simp only [scanContext_lock_cons, scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_lock_m32_imm32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    Triple (LockedRmwPre p am 4 (8 + am.tail.length))
      (codeRange p (0xF0 :: rex :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (xorMImm32Effect p (8 + am.tail.length) 32 am imm)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorMImm32Effect_components]; exact mem_components_rmw _ _) hpre.rmw.code (by simp; omega))
    (xor_lock_m32_imm32_rex_effect_step p rex hrex am hv hx hb imm)

theorem xor_lock_m16_imm16_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) :
    StepEffect (LockedRmwPre p am 2 (6 + am.tail.length))
      (codeRange p (0xF0 :: 0x66 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 16 imm)))
      (xorM16Imm16Effect p (6 + am.tail.length) am imm) := by
  intro s h hcode hpre
  have hlk := lockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := xor_lock_m16_imm16_step s h [0xF0, 0x66] (scanPrefix_lock_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [scanContext_lock_cons]; exact rfl)
    (by rw [scanContext_lock_cons]; rfl) (by rw [scanContext_lock_cons]; rfl)
    (by rw [scanContext_lock_cons]; rfl) am hv
    (by rw [scanContext_lock_cons]; exact ((AddrContext.osz _ am hx hb).withLock).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_lock_cons]; exact hread)
    (by rw [scanContext_lock_cons]; exact hlk)
  simp only [scanContext_lock_cons] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_lock_m16_imm16_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) :
    Triple (LockedRmwPre p am 2 (6 + am.tail.length))
      (codeRange p (0xF0 :: 0x66 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 16 imm)))
      (Effect.post (xorM16Imm16Effect p (6 + am.tail.length) am imm)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorM16Imm16Effect_components]; exact mem_components_rmw _ _) hpre.rmw.code (by simp; omega))
    (xor_lock_m16_imm16_effect_step p am hv hx hb imm)

theorem xor_lock_m16_imm16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 16) :
    StepEffect (LockedRmwPre p am 2 (7 + am.tail.length))
      (codeRange p (0xF0 :: 0x66 :: rex :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 16 imm)))
      (xorM16Imm16Effect p (7 + am.tail.length) am imm) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  have hlk := lockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := xor_lock_m16_imm16_step s h [0xF0, 0x66, rex] (scanPrefix_lock_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [scanContext_lock_cons, scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_lock_cons, scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_lock_cons, scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_lock_cons, scanContext_66_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_lock_cons, scanContext_66_rex _ _ hr]; exact ((AddrContext.oszRex _ _ am hx hb).withLock).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_lock_cons, scanContext_66_rex _ _ hr]; exact hread)
    (by rw [scanContext_lock_cons, scanContext_66_rex _ _ hr]; exact hlk)
  simp only [scanContext_lock_cons, scanContext_66_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_lock_m16_imm16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 16) :
    Triple (LockedRmwPre p am 2 (7 + am.tail.length))
      (codeRange p (0xF0 :: 0x66 :: rex :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 16 imm)))
      (Effect.post (xorM16Imm16Effect p (7 + am.tail.length) am imm)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorM16Imm16Effect_components]; exact mem_components_rmw _ _) hpre.rmw.code (by simp; omega))
    (xor_lock_m16_imm16_rex_effect_step p rex hrex am hv hx hb imm)

theorem xor_lock_m64_imm32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (SegLockedRmwPre p r base am 8 (9 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF0 :: rex :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)))
      (xorMImm32SegEffect p (9 + am.tail.length) 64 base am imm) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  have hlk := segLockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (9 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF0, rex] =
      withSeg (withLock (rexContext s.DS rex.toBitVec)) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF0, rex]
      (noSegPrefix_cons noSegPrefix_f0 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_lock_cons, scanContext_rex _ _ hr]
  have hstep := xor_lock_m_imm32_step s h [r.prefixByte, 0xF0, rex] (scanPrefix_seg_cons r (scanPrefix_lock_cons (by simpa using hr.scanPrefix))) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact ((AddrContext.rex _ _ am hx hb).withLock).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
    (by rw [hsc, segAddr_withSeg]; exact hlk)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_lock_m64_imm32_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    Triple (SegLockedRmwPre p r base am 8 (9 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF0 :: rex :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (xorMImm32SegEffect p (9 + am.tail.length) 64 base am imm)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorMImm32SegEffect_components]; exact mem_components_rmw _ _) hpre.rmw.store.code (by simp; omega))
    (xor_lock_m64_imm32_seg_effect_step p r base rex hrex am hv hx hb imm)

theorem xor_lock_m32_imm32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) :
    StepEffect (SegLockedRmwPre p r base am 4 (8 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF0 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)))
      (xorMImm32SegEffect p (8 + am.tail.length) 32 base am imm) := by
  intro s h hcode hpre
  have hlk := segLockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (8 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF0] =
      withSeg (withLock (scanContext s.DS (PrefixSegments.ofState s) [])) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF0]
      (noSegPrefix_cons noSegPrefix_f0 noSegPrefix_nil), scanContext_lock_cons]
  have hstep := xor_lock_m_imm32_step s h [r.prefixByte, 0xF0] (scanPrefix_seg_cons r (scanPrefix_lock_cons (by simp))) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact ((AddrContext.legacy _ am hx hb).withLock).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
    (by rw [hsc, segAddr_withSeg]; exact hlk)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_lock_m32_imm32_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) :
    Triple (SegLockedRmwPre p r base am 4 (8 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF0 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (xorMImm32SegEffect p (8 + am.tail.length) 32 base am imm)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorMImm32SegEffect_components]; exact mem_components_rmw _ _) hpre.rmw.store.code (by simp; omega))
    (xor_lock_m32_imm32_seg_effect_step p r base am hv hx hb imm)

theorem xor_lock_m32_imm32_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (SegLockedRmwPre p r base am 4 (9 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF0 :: rex :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)))
      (xorMImm32SegEffect p (9 + am.tail.length) 32 base am imm) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  have hlk := segLockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (9 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF0, rex] =
      withSeg (withLock (rexContext s.DS rex.toBitVec)) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF0, rex]
      (noSegPrefix_cons noSegPrefix_f0 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_lock_cons, scanContext_rex _ _ hr]
  have hstep := xor_lock_m_imm32_step s h [r.prefixByte, 0xF0, rex] (scanPrefix_seg_cons r (scanPrefix_lock_cons (by simpa using hr.scanPrefix))) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact ((AddrContext.rex _ _ am hx hb).withLock).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
    (by rw [hsc, segAddr_withSeg]; exact hlk)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_lock_m32_imm32_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    Triple (SegLockedRmwPre p r base am 4 (9 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF0 :: rex :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (xorMImm32SegEffect p (9 + am.tail.length) 32 base am imm)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorMImm32SegEffect_components]; exact mem_components_rmw _ _) hpre.rmw.store.code (by simp; omega))
    (xor_lock_m32_imm32_rex_seg_effect_step p r base rex hrex am hv hx hb imm)

theorem xor_lock_m16_imm16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) :
    StepEffect (SegLockedRmwPre p r base am 2 (7 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF0 :: 0x66 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 16 imm)))
      (xorM16Imm16SegEffect p (7 + am.tail.length) base am imm) := by
  intro s h hcode hpre
  have hlk := segLockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF0, 0x66] =
      withSeg (withLock (scanContext s.DS (PrefixSegments.ofState s) [0x66])) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF0, 0x66]
      (noSegPrefix_cons noSegPrefix_f0 (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)), scanContext_lock_cons]
  have hstep := xor_lock_m16_imm16_step s h [r.prefixByte, 0xF0, 0x66] (scanPrefix_seg_cons r (scanPrefix_lock_cons (by simpa using scanPrefix_66))) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact ((AddrContext.osz _ am hx hb).withLock).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
    (by rw [hsc, segAddr_withSeg]; exact hlk)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_lock_m16_imm16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) :
    Triple (SegLockedRmwPre p r base am 2 (7 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF0 :: 0x66 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 16 imm)))
      (Effect.post (xorM16Imm16SegEffect p (7 + am.tail.length) base am imm)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorM16Imm16SegEffect_components]; exact mem_components_rmw _ _) hpre.rmw.store.code (by simp; omega))
    (xor_lock_m16_imm16_seg_effect_step p r base am hv hx hb imm)

theorem xor_lock_m16_imm16_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 16) :
    StepEffect (SegLockedRmwPre p r base am 2 (8 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF0 :: 0x66 :: rex :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 16 imm)))
      (xorM16Imm16SegEffect p (8 + am.tail.length) base am imm) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  have hlk := segLockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (8 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF0, 0x66, rex] =
      withSeg (withLock (oszRexContext s.DS rex.toBitVec)) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF0, 0x66, rex]
      (noSegPrefix_cons noSegPrefix_f0 (noSegPrefix_cons noSegPrefix_66 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil))), scanContext_lock_cons, scanContext_66_rex _ _ hr]
  have hstep := xor_lock_m16_imm16_step s h [r.prefixByte, 0xF0, 0x66, rex] (scanPrefix_seg_cons r (scanPrefix_lock_cons (by simp [scanPrefix_66, hr.scanPrefix]))) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact ((AddrContext.oszRex _ _ am hx hb).withLock).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
    (by rw [hsc, segAddr_withSeg]; exact hlk)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_lock_m16_imm16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 16) :
    Triple (SegLockedRmwPre p r base am 2 (8 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF0 :: 0x66 :: rex :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 16 imm)))
      (Effect.post (xorM16Imm16SegEffect p (8 + am.tail.length) base am imm)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorM16Imm16SegEffect_components]; exact mem_components_rmw _ _) hpre.rmw.store.code (by simp; omega))
    (xor_lock_m16_imm16_rex_seg_effect_step p r base rex hrex am hv hx hb imm)

theorem xor_lock_m64_imm32_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (LockedRmw32Pre p am 8 (9 + am.tail.length))
      (codeRange p (0x67 :: 0xF0 :: rex :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)))
      (xorMImm32A32Effect p (9 + am.tail.length) 64 am imm) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  have hlk := lockedRmw32_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (9 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0xF0, rex] =
      withAsz (withLock (rexContext s.DS rex.toBitVec)) := by
    rw [scanContext_asz_cons, scanContext_lock_cons, scanContext_rex _ _ hr]
  have hstep := xor_lock_m_imm32_a32_step s h [0x67, 0xF0, rex] (scanPrefix_asz_cons (scanPrefix_lock_cons (by simpa using hr.scanPrefix))) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact ((AddrContext.rex _ _ am hx hb).withLock).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
    (by rw [hsc]; exact hlk)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_lock_m64_imm32_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    Triple (LockedRmw32Pre p am 8 (9 + am.tail.length))
      (codeRange p (0x67 :: 0xF0 :: rex :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (xorMImm32A32Effect p (9 + am.tail.length) 64 am imm)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorMImm32A32Effect_components]; exact mem_components_rmw _ _) hpre.rmw.code (by simp; omega))
    (xor_lock_m64_imm32_a32_effect_step p rex hrex am hv hx hb imm)

theorem xor_lock_m32_imm32_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) :
    StepEffect (LockedRmw32Pre p am 4 (8 + am.tail.length))
      (codeRange p (0x67 :: 0xF0 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)))
      (xorMImm32A32Effect p (8 + am.tail.length) 32 am imm) := by
  intro s h hcode hpre
  have hlk := lockedRmw32_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (8 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0xF0] =
      withAsz (withLock (scanContext s.DS (PrefixSegments.ofState s) [])) := by
    rw [scanContext_asz_cons, scanContext_lock_cons]
  have hstep := xor_lock_m_imm32_a32_step s h [0x67, 0xF0] (scanPrefix_asz_cons (scanPrefix_lock_cons (by simp))) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact ((AddrContext.legacy _ am hx hb).withLock).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
    (by rw [hsc]; exact hlk)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_lock_m32_imm32_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) :
    Triple (LockedRmw32Pre p am 4 (8 + am.tail.length))
      (codeRange p (0x67 :: 0xF0 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (xorMImm32A32Effect p (8 + am.tail.length) 32 am imm)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorMImm32A32Effect_components]; exact mem_components_rmw _ _) hpre.rmw.code (by simp; omega))
    (xor_lock_m32_imm32_a32_effect_step p am hv hx hb imm)

theorem xor_lock_m32_imm32_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (LockedRmw32Pre p am 4 (9 + am.tail.length))
      (codeRange p (0x67 :: 0xF0 :: rex :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)))
      (xorMImm32A32Effect p (9 + am.tail.length) 32 am imm) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  have hlk := lockedRmw32_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (9 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0xF0, rex] =
      withAsz (withLock (rexContext s.DS rex.toBitVec)) := by
    rw [scanContext_asz_cons, scanContext_lock_cons, scanContext_rex _ _ hr]
  have hstep := xor_lock_m_imm32_a32_step s h [0x67, 0xF0, rex] (scanPrefix_asz_cons (scanPrefix_lock_cons (by simpa using hr.scanPrefix))) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact ((AddrContext.rex _ _ am hx hb).withLock).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
    (by rw [hsc]; exact hlk)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_lock_m32_imm32_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    Triple (LockedRmw32Pre p am 4 (9 + am.tail.length))
      (codeRange p (0x67 :: 0xF0 :: rex :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (xorMImm32A32Effect p (9 + am.tail.length) 32 am imm)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorMImm32A32Effect_components]; exact mem_components_rmw _ _) hpre.rmw.code (by simp; omega))
    (xor_lock_m32_imm32_rex_a32_effect_step p rex hrex am hv hx hb imm)

theorem xor_lock_m16_imm16_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) :
    StepEffect (LockedRmw32Pre p am 2 (7 + am.tail.length))
      (codeRange p (0x67 :: 0xF0 :: 0x66 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 16 imm)))
      (xorM16Imm16A32Effect p (7 + am.tail.length) am imm) := by
  intro s h hcode hpre
  have hlk := lockedRmw32_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0xF0, 0x66] =
      withAsz (withLock (scanContext s.DS (PrefixSegments.ofState s) [0x66])) := by
    rw [scanContext_asz_cons, scanContext_lock_cons]
  have hstep := xor_lock_m16_imm16_a32_step s h [0x67, 0xF0, 0x66] (scanPrefix_asz_cons (scanPrefix_lock_cons (by simpa using scanPrefix_66))) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact ((AddrContext.osz _ am hx hb).withLock).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
    (by rw [hsc]; exact hlk)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_lock_m16_imm16_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) :
    Triple (LockedRmw32Pre p am 2 (7 + am.tail.length))
      (codeRange p (0x67 :: 0xF0 :: 0x66 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 16 imm)))
      (Effect.post (xorM16Imm16A32Effect p (7 + am.tail.length) am imm)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorM16Imm16A32Effect_components]; exact mem_components_rmw _ _) hpre.rmw.code (by simp; omega))
    (xor_lock_m16_imm16_a32_effect_step p am hv hx hb imm)

theorem xor_lock_m16_imm16_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 16) :
    StepEffect (LockedRmw32Pre p am 2 (8 + am.tail.length))
      (codeRange p (0x67 :: 0xF0 :: 0x66 :: rex :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 16 imm)))
      (xorM16Imm16A32Effect p (8 + am.tail.length) am imm) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  have hlk := lockedRmw32_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (8 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0xF0, 0x66, rex] =
      withAsz (withLock (oszRexContext s.DS rex.toBitVec)) := by
    rw [scanContext_asz_cons, scanContext_lock_cons, scanContext_66_rex _ _ hr]
  have hstep := xor_lock_m16_imm16_a32_step s h [0x67, 0xF0, 0x66, rex] (scanPrefix_asz_cons (scanPrefix_lock_cons (by simp [scanPrefix_66, hr.scanPrefix]))) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact ((AddrContext.oszRex _ _ am hx hb).withLock).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
    (by rw [hsc]; exact hlk)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_lock_m16_imm16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 16) :
    Triple (LockedRmw32Pre p am 2 (8 + am.tail.length))
      (codeRange p (0x67 :: 0xF0 :: 0x66 :: rex :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 16 imm)))
      (Effect.post (xorM16Imm16A32Effect p (8 + am.tail.length) am imm)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorM16Imm16A32Effect_components]; exact mem_components_rmw _ _) hpre.rmw.code (by simp; omega))
    (xor_lock_m16_imm16_rex_a32_effect_step p rex hrex am hv hx hb imm)

theorem xor_lock_m64_imm32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 32) :
    Triple (LockedRmwPre p am 8 (8 + am.tail.length))
      (codeRange p (encodeXorLockM64Imm32 am imm))
      (Effect.post (xorMImm32Effect p (8 + am.tail.length) 64 am imm)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact xor_lock_m64_imm32_triple_of_bytes p _ hrex am hv hx hb imm

theorem xor_lock_m32_imm32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 32) :
    Triple (LockedRmwPre p am 4 (encodeXorLockM32Imm32 am imm).length)
      (codeRange p (encodeXorLockM32Imm32 am imm))
      (Effect.post (xorMImm32Effect p (encodeXorLockM32Imm32 am imm).length 32 am imm)) := by
  unfold encodeXorLockM32Imm32 encodeXorM32Imm32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := xor_lock_m32_imm32_triple_of_bytes p am hv hx hb imm
    rwa [show (0xF0 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)).length =
      7 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := xor_lock_m32_imm32_rex_triple_of_bytes p _ hrex am hv hx hb imm
    rwa [show (0xF0 :: am.rexByte false 0 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)).length =
      8 + am.tail.length by simp; omega]

theorem xor_lock_m16_imm16_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 16) :
    Triple (LockedRmwPre p am 2 (encodeXorLockM16Imm16 am imm).length)
      (codeRange p (encodeXorLockM16Imm16 am imm))
      (Effect.post (xorM16Imm16Effect p (encodeXorLockM16Imm16 am imm).length am imm)) := by
  unfold encodeXorLockM16Imm16 encodeXorM16Imm16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := xor_lock_m16_imm16_triple_of_bytes p am hv hx hb imm
    rwa [show (0xF0 :: 0x66 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 16 imm)).length =
      6 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := xor_lock_m16_imm16_rex_triple_of_bytes p _ hrex am hv hx hb imm
    rwa [show (0xF0 :: 0x66 :: am.rexByte false 0 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 16 imm)).length =
      7 + am.tail.length by simp; omega]

theorem xor_lock_m64_imm32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (imm : BitVec 32) :
    Triple (SegLockedRmwPre p r base am 8 (9 + am.tail.length))
      (codeRange p (r.prefixByte :: encodeXorLockM64Imm32 am imm))
      (Effect.post (xorMImm32SegEffect p (9 + am.tail.length) 64 base am
        imm)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact xor_lock_m64_imm32_seg_triple_of_bytes p r base _ hrex am hv hx hb imm

theorem xor_lock_m32_imm32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (imm : BitVec 32) :
    Triple (SegLockedRmwPre p r base am 4 (r.prefixByte :: encodeXorLockM32Imm32 am imm).length)
      (codeRange p (r.prefixByte :: encodeXorLockM32Imm32 am imm))
      (Effect.post (xorMImm32SegEffect p (r.prefixByte :: encodeXorLockM32Imm32 am imm).length 32 base am
        imm)) := by
  unfold encodeXorLockM32Imm32 encodeXorM32Imm32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := xor_lock_m32_imm32_seg_triple_of_bytes p r base am hv hx hb imm
    rwa [show (r.prefixByte :: 0xF0 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)).length =
      8 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := xor_lock_m32_imm32_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb imm
    rwa [show (r.prefixByte :: 0xF0 :: am.rexByte false 0 :: 0x81 :: am.modrm 6 ::
      (am.tail ++ immBytes 32 imm)).length = 9 + am.tail.length by simp; omega]

theorem xor_lock_m16_imm16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (imm : BitVec 16) :
    Triple (SegLockedRmwPre p r base am 2 (r.prefixByte :: encodeXorLockM16Imm16 am imm).length)
      (codeRange p (r.prefixByte :: encodeXorLockM16Imm16 am imm))
      (Effect.post (xorM16Imm16SegEffect p (r.prefixByte :: encodeXorLockM16Imm16 am imm).length base am
        imm)) := by
  unfold encodeXorLockM16Imm16 encodeXorM16Imm16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := xor_lock_m16_imm16_seg_triple_of_bytes p r base am hv hx hb imm
    rwa [show (r.prefixByte :: 0xF0 :: 0x66 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 16 imm)).length =
      7 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := xor_lock_m16_imm16_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb imm
    rwa [show (r.prefixByte :: 0xF0 :: 0x66 :: am.rexByte false 0 :: 0x81 :: am.modrm 6 ::
      (am.tail ++ immBytes 16 imm)).length = 8 + am.tail.length by simp; omega]

theorem xor_lock_m64_imm32_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 32) :
    Triple (LockedRmw32Pre p am 8 (9 + am.tail.length))
      (codeRange p (0x67 :: encodeXorLockM64Imm32 am imm))
      (Effect.post (xorMImm32A32Effect p (9 + am.tail.length) 64 am imm)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact xor_lock_m64_imm32_a32_triple_of_bytes p _ hrex am hv hx hb imm

theorem xor_lock_m32_imm32_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 32) :
    Triple (LockedRmw32Pre p am 4 (0x67 :: encodeXorLockM32Imm32 am imm).length)
      (codeRange p (0x67 :: encodeXorLockM32Imm32 am imm))
      (Effect.post (xorMImm32A32Effect p (0x67 :: encodeXorLockM32Imm32 am imm).length 32 am imm)) := by
  unfold encodeXorLockM32Imm32 encodeXorM32Imm32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := xor_lock_m32_imm32_a32_triple_of_bytes p am hv hx hb imm
    rwa [show (0x67 :: 0xF0 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)).length =
      8 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := xor_lock_m32_imm32_rex_a32_triple_of_bytes p _ hrex am hv hx hb imm
    rwa [show (0x67 :: 0xF0 :: am.rexByte false 0 :: 0x81 :: am.modrm 6 ::
      (am.tail ++ immBytes 32 imm)).length = 9 + am.tail.length by simp; omega]

theorem xor_lock_m16_imm16_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 16) :
    Triple (LockedRmw32Pre p am 2 (0x67 :: encodeXorLockM16Imm16 am imm).length)
      (codeRange p (0x67 :: encodeXorLockM16Imm16 am imm))
      (Effect.post (xorM16Imm16A32Effect p (0x67 :: encodeXorLockM16Imm16 am imm).length am imm)) := by
  unfold encodeXorLockM16Imm16 encodeXorM16Imm16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := xor_lock_m16_imm16_a32_triple_of_bytes p am hv hx hb imm
    rwa [show (0x67 :: 0xF0 :: 0x66 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 16 imm)).length =
      7 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := xor_lock_m16_imm16_rex_a32_triple_of_bytes p _ hrex am hv hx hb imm
    rwa [show (0x67 :: 0xF0 :: 0x66 :: am.rexByte false 0 :: 0x81 :: am.modrm 6 ::
      (am.tail ++ immBytes 16 imm)).length = 8 + am.tail.length by simp; omega]

end X86Proofs
