import X86Proofs.Instructions.Xor.Generated.M8Imm8Lock.Step
import X86Proofs.Instructions.Xor.Generated.M8Imm8Lock.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem xor_lock_m8_imm8_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : UInt8) :
    StepEffect (LockedRmwPre p am 1 (4 + am.tail.length))
      (codeRange p (0xF0 :: 0x80 :: am.modrm 6 :: (am.tail ++ [imm])))
      (xorM8Imm8Effect p (4 + am.tail.length) am imm.toBitVec) := by
  intro s h hcode hpre
  have hlk := lockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append] at this
    omega
  have hstep := xor_lock_m8_imm8_step s h [0xF0] (scanPrefix_lock_cons (by simp)) (by simp)
    (by rw [scanContext_lock_cons]; rfl) (by rw [scanContext_lock_cons]; rfl)
    (by rw [scanContext_lock_cons]; rfl) am hv
    (by rw [scanContext_lock_cons]; exact ((AddrContext.legacy _ am hx hb).withLock).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_lock_cons]; exact hread)
    (by rw [scanContext_lock_cons]; exact hlk)
  simp only [scanContext_lock_cons, BitVec.signExtend_eq] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_lock_m8_imm8_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : UInt8) :
    Triple (LockedRmwPre p am 1 (4 + am.tail.length))
      (codeRange p (0xF0 :: 0x80 :: am.modrm 6 :: (am.tail ++ [imm])))
      (Effect.post (xorM8Imm8Effect p (4 + am.tail.length) am imm.toBitVec)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorM8Imm8Effect_components]; exact mem_components_rmw _ _) hpre.rmw.code (by simp; omega))
    (xor_lock_m8_imm8_effect_step p am hv hx hb imm)

theorem xor_lock_m8_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : UInt8) :
    StepEffect (LockedRmwPre p am 1 (5 + am.tail.length))
      (codeRange p (0xF0 :: rex :: 0x80 :: am.modrm 6 :: (am.tail ++ [imm])))
      (xorM8Imm8Effect p (5 + am.tail.length) am imm.toBitVec) := by
  intro s h hcode hpre
  have hlk := lockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append] at this
    omega
  have hstep := xor_lock_m8_imm8_step s h [0xF0, rex] (scanPrefix_lock_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; rfl) (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; exact ((AddrContext.rex _ _ am hx hb).withLock).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; exact hread)
    (by rw [scanContext_lock_cons, scanContext_rex _ _ hr]; exact hlk)
  simp only [scanContext_lock_cons, scanContext_rex _ _ hr, BitVec.signExtend_eq] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_lock_m8_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : UInt8) :
    Triple (LockedRmwPre p am 1 (5 + am.tail.length))
      (codeRange p (0xF0 :: rex :: 0x80 :: am.modrm 6 :: (am.tail ++ [imm])))
      (Effect.post (xorM8Imm8Effect p (5 + am.tail.length) am imm.toBitVec)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorM8Imm8Effect_components]; exact mem_components_rmw _ _) hpre.rmw.code (by simp; omega))
    (xor_lock_m8_imm8_rex_effect_step p rex hr am hv hx hb imm)

theorem xor_lock_m8_imm8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : UInt8) :
    StepEffect (SegLockedRmwPre p r base am 1 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF0 :: 0x80 :: am.modrm 6 :: (am.tail ++ [imm])))
      (xorM8Imm8SegEffect p (5 + am.tail.length) base am imm.toBitVec) := by
  intro s h hcode hpre
  have hlk := segLockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF0] =
      withSeg (withLock (scanContext s.DS (PrefixSegments.ofState s) [])) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF0]
      (noSegPrefix_cons noSegPrefix_f0 noSegPrefix_nil), scanContext_lock_cons]
  have hstep := xor_lock_m8_imm8_step s h [r.prefixByte, 0xF0] (scanPrefix_seg_cons r (scanPrefix_lock_cons (by simp))) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact ((AddrContext.legacy _ am hx hb).withLock).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
    (by rw [hsc, segAddr_withSeg]; exact hlk)
  simp only [hsc, segAddr_withSeg, BitVec.signExtend_eq] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_lock_m8_imm8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : UInt8) :
    Triple (SegLockedRmwPre p r base am 1 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF0 :: 0x80 :: am.modrm 6 :: (am.tail ++ [imm])))
      (Effect.post (xorM8Imm8SegEffect p (5 + am.tail.length) base am imm.toBitVec)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorM8Imm8SegEffect_components]; exact mem_components_rmw _ _) hpre.rmw.store.code (by simp; omega))
    (xor_lock_m8_imm8_seg_effect_step p r base am hv hx hb imm)

theorem xor_lock_m8_imm8_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : UInt8) :
    StepEffect (SegLockedRmwPre p r base am 1 (6 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF0 :: rex :: 0x80 :: am.modrm 6 :: (am.tail ++ [imm])))
      (xorM8Imm8SegEffect p (6 + am.tail.length) base am imm.toBitVec) := by
  intro s h hcode hpre
  have hlk := segLockedRmw_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF0, rex] =
      withSeg (withLock (rexContext s.DS rex.toBitVec)) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF0, rex]
      (noSegPrefix_cons noSegPrefix_f0 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_lock_cons, scanContext_rex _ _ hr]
  have hstep := xor_lock_m8_imm8_step s h [r.prefixByte, 0xF0, rex] (scanPrefix_seg_cons r (scanPrefix_lock_cons (by simpa using hr.scanPrefix))) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact ((AddrContext.rex _ _ am hx hb).withLock).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
    (by rw [hsc, segAddr_withSeg]; exact hlk)
  simp only [hsc, segAddr_withSeg, BitVec.signExtend_eq] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_lock_m8_imm8_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : UInt8) :
    Triple (SegLockedRmwPre p r base am 1 (6 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF0 :: rex :: 0x80 :: am.modrm 6 :: (am.tail ++ [imm])))
      (Effect.post (xorM8Imm8SegEffect p (6 + am.tail.length) base am imm.toBitVec)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorM8Imm8SegEffect_components]; exact mem_components_rmw _ _) hpre.rmw.store.code (by simp; omega))
    (xor_lock_m8_imm8_rex_seg_effect_step p r base rex hr am hv hx hb imm)

theorem xor_lock_m8_imm8_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : UInt8) :
    StepEffect (LockedRmw32Pre p am 1 (5 + am.tail.length))
      (codeRange p (0x67 :: 0xF0 :: 0x80 :: am.modrm 6 :: (am.tail ++ [imm])))
      (xorM8Imm8A32Effect p (5 + am.tail.length) am imm.toBitVec) := by
  intro s h hcode hpre
  have hlk := lockedRmw32_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0xF0] =
      withAsz (withLock (scanContext s.DS (PrefixSegments.ofState s) [])) := by
    rw [scanContext_asz_cons, scanContext_lock_cons]
  have hstep := xor_lock_m8_imm8_a32_step s h [0x67, 0xF0] (scanPrefix_asz_cons (scanPrefix_lock_cons (by simp))) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact ((AddrContext.legacy _ am hx hb).withLock).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
    (by rw [hsc]; exact hlk)
  simp only [hsc, BitVec.signExtend_eq] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_lock_m8_imm8_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : UInt8) :
    Triple (LockedRmw32Pre p am 1 (5 + am.tail.length))
      (codeRange p (0x67 :: 0xF0 :: 0x80 :: am.modrm 6 :: (am.tail ++ [imm])))
      (Effect.post (xorM8Imm8A32Effect p (5 + am.tail.length) am imm.toBitVec)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorM8Imm8A32Effect_components]; exact mem_components_rmw _ _) hpre.rmw.code (by simp; omega))
    (xor_lock_m8_imm8_a32_effect_step p am hv hx hb imm)

theorem xor_lock_m8_imm8_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : UInt8) :
    StepEffect (LockedRmw32Pre p am 1 (6 + am.tail.length))
      (codeRange p (0x67 :: 0xF0 :: rex :: 0x80 :: am.modrm 6 :: (am.tail ++ [imm])))
      (xorM8Imm8A32Effect p (6 + am.tail.length) am imm.toBitVec) := by
  intro s h hcode hpre
  have hlk := lockedRmw32_lock hpre
  replace hpre := hpre.rmw
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0xF0, rex] =
      withAsz (withLock (rexContext s.DS rex.toBitVec)) := by
    rw [scanContext_asz_cons, scanContext_lock_cons, scanContext_rex _ _ hr]
  have hstep := xor_lock_m8_imm8_a32_step s h [0x67, 0xF0, rex] (scanPrefix_asz_cons (scanPrefix_lock_cons (by simpa using hr.scanPrefix))) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact ((AddrContext.rex _ _ am hx hb).withLock).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
    (by rw [hsc]; exact hlk)
  simp only [hsc, BitVec.signExtend_eq] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_lock_m8_imm8_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : UInt8) :
    Triple (LockedRmw32Pre p am 1 (6 + am.tail.length))
      (codeRange p (0x67 :: 0xF0 :: rex :: 0x80 :: am.modrm 6 :: (am.tail ++ [imm])))
      (Effect.post (xorM8Imm8A32Effect p (6 + am.tail.length) am imm.toBitVec)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorM8Imm8A32Effect_components]; exact mem_components_rmw _ _) hpre.rmw.code (by simp; omega))
    (xor_lock_m8_imm8_rex_a32_effect_step p rex hr am hv hx hb imm)

theorem xor_lock_m8_imm8_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (LockedRmwPre p am 1 (4 + am.tail.length))
      (codeRange p (encodeXorLockM8Imm8 am imm))
      (Effect.post (xorM8Imm8Effect p (4 + am.tail.length) am imm)) :=
  xor_lock_m8_imm8_triple_of_bytes p am hv hx hb (UInt8.ofBitVec imm)

theorem xor_lock_m8_imm8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (SegLockedRmwPre p r base am 1 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: encodeXorLockM8Imm8 am imm))
      (Effect.post (xorM8Imm8SegEffect p (5 + am.tail.length) base am imm)) :=
  xor_lock_m8_imm8_seg_triple_of_bytes p r base am hv hx hb (UInt8.ofBitVec imm)

theorem xor_lock_m8_imm8_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (LockedRmw32Pre p am 1 (5 + am.tail.length))
      (codeRange p (0x67 :: encodeXorLockM8Imm8 am imm))
      (Effect.post (xorM8Imm8A32Effect p (5 + am.tail.length) am imm)) :=
  xor_lock_m8_imm8_a32_triple_of_bytes p am hv hx hb (UInt8.ofBitVec imm)

end X86Proofs
