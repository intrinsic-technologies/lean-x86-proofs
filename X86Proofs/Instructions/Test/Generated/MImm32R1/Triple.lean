import X86Proofs.Instructions.Test.Generated.MImm32R1.Step
import X86Proofs.Instructions.Test.Generated.MImm32R1.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Test.Generated.MImm32.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem test_r1_m64_imm32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (7 + am.tail.length))) 8)
      (codeRange p (rex :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 32 imm)))
      (testMImm32Effect p (7 + am.tail.length) 64 am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := test_r1_m_imm32_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_m64_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (7 + am.tail.length))) 8)
      (codeRange p (rex :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (testMImm32Effect p (7 + am.tail.length) 64 am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testMImm32Effect_components]; simp [Component.Covers]) _)
    (test_r1_m64_imm32_effect_step p rex hrex am hv hx hb imm)

theorem test_r1_m32_imm32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 4)
      (codeRange p (0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 32 imm)))
      (testMImm32Effect p (6 + am.tail.length) 32 am imm) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := test_r1_m_imm32_step s h [] (by simp) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_m32_imm32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 4)
      (codeRange p (0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (testMImm32Effect p (6 + am.tail.length) 32 am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testMImm32Effect_components]; simp [Component.Covers]) _)
    (test_r1_m32_imm32_effect_step p am hv hx hb imm)

theorem test_r1_m32_imm32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (7 + am.tail.length))) 4)
      (codeRange p (rex :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 32 imm)))
      (testMImm32Effect p (7 + am.tail.length) 32 am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := test_r1_m_imm32_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_m32_imm32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (7 + am.tail.length))) 4)
      (codeRange p (rex :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (testMImm32Effect p (7 + am.tail.length) 32 am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testMImm32Effect_components]; simp [Component.Covers]) _)
    (test_r1_m32_imm32_rex_effect_step p rex hrex am hv hx hb imm)

theorem test_r1_m16_imm16_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (0x66 :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 16 imm)))
      (testM16Imm16Effect p (5 + am.tail.length) am imm) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := test_r1_m16_imm16_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.osz _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_m16_imm16_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (0x66 :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 16 imm)))
      (Effect.post (testM16Imm16Effect p (5 + am.tail.length) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testM16Imm16Effect_components]; simp [Component.Covers]) _)
    (test_r1_m16_imm16_effect_step p am hv hx hb imm)

theorem test_r1_m16_imm16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 16) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2)
      (codeRange p (0x66 :: rex :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 16 imm)))
      (testM16Imm16Effect p (6 + am.tail.length) am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := test_r1_m16_imm16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_66_rex _ _ hr]; exact (AddrContext.oszRex _ _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_66_rex _ _ hr]; exact hread)
  simp only [scanContext_66_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_m16_imm16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 16) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2)
      (codeRange p (0x66 :: rex :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 16 imm)))
      (Effect.post (testM16Imm16Effect p (6 + am.tail.length) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testM16Imm16Effect_components]; simp [Component.Covers]) _)
    (test_r1_m16_imm16_rex_effect_step p rex hrex am hv hx hb imm)

theorem test_r1_m64_imm32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (8 + am.tail.length))) 8)
      (codeRange p (r.prefixByte :: rex :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 32 imm)))
      (testMImm32SegEffect p (8 + am.tail.length) 64 base am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (8 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := test_r1_m_imm32_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_m64_imm32_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (8 + am.tail.length))) 8)
      (codeRange p (r.prefixByte :: rex :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (testMImm32SegEffect p (8 + am.tail.length) 64 base am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testMImm32SegEffect_components]; simp [Component.Covers]) _)
    (test_r1_m64_imm32_seg_effect_step p r base rex hrex am hv hx hb imm)

theorem test_r1_m32_imm32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (7 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 32 imm)))
      (testMImm32SegEffect p (7 + am.tail.length) 32 base am imm) := by
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := test_r1_m_imm32_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_m32_imm32_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (7 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (testMImm32SegEffect p (7 + am.tail.length) 32 base am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testMImm32SegEffect_components]; simp [Component.Covers]) _)
    (test_r1_m32_imm32_seg_effect_step p r base am hv hx hb imm)

theorem test_r1_m32_imm32_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (8 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: rex :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 32 imm)))
      (testMImm32SegEffect p (8 + am.tail.length) 32 base am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (8 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := test_r1_m_imm32_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_m32_imm32_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (8 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: rex :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (testMImm32SegEffect p (8 + am.tail.length) 32 base am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testMImm32SegEffect_components]; simp [Component.Covers]) _)
    (test_r1_m32_imm32_rex_seg_effect_step p r base rex hrex am hv hx hb imm)

theorem test_r1_m16_imm16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 16 imm)))
      (testM16Imm16SegEffect p (6 + am.tail.length) base am imm) := by
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66]
      (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := test_r1_m16_imm16_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_m16_imm16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 16 imm)))
      (Effect.post (testM16Imm16SegEffect p (6 + am.tail.length) base am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testM16Imm16SegEffect_components]; simp [Component.Covers]) _)
    (test_r1_m16_imm16_seg_effect_step p r base am hv hx hb imm)

theorem test_r1_m16_imm16_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 16) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (7 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 16 imm)))
      (testM16Imm16SegEffect p (7 + am.tail.length) base am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66, rex] =
      withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66, rex]
      (noSegPrefix_cons noSegPrefix_66 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_66_rex _ _ hr]
  have hstep := test_r1_m16_imm16_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_m16_imm16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 16) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (7 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 16 imm)))
      (Effect.post (testM16Imm16SegEffect p (7 + am.tail.length) base am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testM16Imm16SegEffect_components]; simp [Component.Covers]) _)
    (test_r1_m16_imm16_rex_seg_effect_step p r base rex hrex am hv hx hb imm)

theorem test_r1_m64_imm32_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (8 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 32 imm)))
      (testMImm32A32Effect p (8 + am.tail.length) 64 am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (8 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := test_r1_m_imm32_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_m64_imm32_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (8 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (testMImm32A32Effect p (8 + am.tail.length) 64 am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testMImm32A32Effect_components]; simp [Component.Covers]) _)
    (test_r1_m64_imm32_a32_effect_step p rex hrex am hv hx hb imm)

theorem test_r1_m32_imm32_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (7 + am.tail.length))) 4)
      (codeRange p (0x67 :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 32 imm)))
      (testMImm32A32Effect p (7 + am.tail.length) 32 am imm) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := test_r1_m_imm32_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_m32_imm32_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (7 + am.tail.length))) 4)
      (codeRange p (0x67 :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (testMImm32A32Effect p (7 + am.tail.length) 32 am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testMImm32A32Effect_components]; simp [Component.Covers]) _)
    (test_r1_m32_imm32_a32_effect_step p am hv hx hb imm)

theorem test_r1_m32_imm32_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (8 + am.tail.length))) 4)
      (codeRange p (0x67 :: rex :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 32 imm)))
      (testMImm32A32Effect p (8 + am.tail.length) 32 am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (8 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := test_r1_m_imm32_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_m32_imm32_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (8 + am.tail.length))) 4)
      (codeRange p (0x67 :: rex :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (testMImm32A32Effect p (8 + am.tail.length) 32 am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testMImm32A32Effect_components]; simp [Component.Covers]) _)
    (test_r1_m32_imm32_rex_a32_effect_step p rex hrex am hv hx hb imm)

theorem test_r1_m16_imm16_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 16 imm)))
      (testM16Imm16A32Effect p (6 + am.tail.length) am imm) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66]) := by
    rw [scanContext_asz_cons]
  have hstep := test_r1_m16_imm16_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_m16_imm16_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 16 imm)))
      (Effect.post (testM16Imm16A32Effect p (6 + am.tail.length) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testM16Imm16A32Effect_components]; simp [Component.Covers]) _)
    (test_r1_m16_imm16_a32_effect_step p am hv hx hb imm)

theorem test_r1_m16_imm16_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 16) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (7 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: rex :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 16 imm)))
      (testM16Imm16A32Effect p (7 + am.tail.length) am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, rex] =
      withAsz (oszRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_66_rex _ _ hr]
  have hstep := test_r1_m16_imm16_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_r1_m16_imm16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 16) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (7 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: rex :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 16 imm)))
      (Effect.post (testM16Imm16A32Effect p (7 + am.tail.length) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testM16Imm16A32Effect_components]; simp [Component.Covers]) _)
    (test_r1_m16_imm16_rex_a32_effect_step p rex hrex am hv hx hb imm)

theorem test_r1_m64_imm32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 32) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (7 + am.tail.length))) 8)
      (codeRange p (encodeTestR1M64Imm32 am imm))
      (Effect.post (testMImm32Effect p (7 + am.tail.length) 64 am imm)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact test_r1_m64_imm32_triple_of_bytes p _ hrex am hv hx hb imm

theorem test_r1_m32_imm32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 32) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (encodeTestR1M32Imm32 am imm).length)) 4)
      (codeRange p (encodeTestR1M32Imm32 am imm))
      (Effect.post (testMImm32Effect p (encodeTestR1M32Imm32 am imm).length 32 am imm)) := by
  unfold encodeTestR1M32Imm32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := test_r1_m32_imm32_triple_of_bytes p am hv hx hb imm
    rwa [show (0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 32 imm)).length =
      6 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := test_r1_m32_imm32_rex_triple_of_bytes p _ hrex am hv hx hb imm
    rwa [show (am.rexByte false 0 :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 32 imm)).length =
      7 + am.tail.length by simp; omega]

theorem test_r1_m16_imm16_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 16) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (encodeTestR1M16Imm16 am imm).length)) 2)
      (codeRange p (encodeTestR1M16Imm16 am imm))
      (Effect.post (testM16Imm16Effect p (encodeTestR1M16Imm16 am imm).length am imm)) := by
  unfold encodeTestR1M16Imm16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := test_r1_m16_imm16_triple_of_bytes p am hv hx hb imm
    rwa [show (0x66 :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 16 imm)).length =
      5 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := test_r1_m16_imm16_rex_triple_of_bytes p _ hrex am hv hx hb imm
    rwa [show (0x66 :: am.rexByte false 0 :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 16 imm)).length =
      6 + am.tail.length by simp; omega]

theorem test_r1_m64_imm32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (imm : BitVec 32) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (8 + am.tail.length))) 8)
      (codeRange p (r.prefixByte :: encodeTestR1M64Imm32 am imm))
      (Effect.post (testMImm32SegEffect p (8 + am.tail.length) 64 base am
        imm)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact test_r1_m64_imm32_seg_triple_of_bytes p r base _ hrex am hv hx hb imm

theorem test_r1_m32_imm32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (imm : BitVec 32) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeTestR1M32Imm32 am imm).length)) 4)
      (codeRange p (r.prefixByte :: encodeTestR1M32Imm32 am imm))
      (Effect.post (testMImm32SegEffect p (r.prefixByte :: encodeTestR1M32Imm32 am imm).length 32 base am
        imm)) := by
  unfold encodeTestR1M32Imm32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := test_r1_m32_imm32_seg_triple_of_bytes p r base am hv hx hb imm
    rwa [show (r.prefixByte :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 32 imm)).length =
      7 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := test_r1_m32_imm32_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb imm
    rwa [show (r.prefixByte :: am.rexByte false 0 :: 0xF7 :: am.modrm 1 ::
      (am.tail ++ immBytes 32 imm)).length = 8 + am.tail.length by simp; omega]

theorem test_r1_m16_imm16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (imm : BitVec 16) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeTestR1M16Imm16 am imm).length)) 2)
      (codeRange p (r.prefixByte :: encodeTestR1M16Imm16 am imm))
      (Effect.post (testM16Imm16SegEffect p (r.prefixByte :: encodeTestR1M16Imm16 am imm).length base am
        imm)) := by
  unfold encodeTestR1M16Imm16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := test_r1_m16_imm16_seg_triple_of_bytes p r base am hv hx hb imm
    rwa [show (r.prefixByte :: 0x66 :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 16 imm)).length =
      6 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := test_r1_m16_imm16_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb imm
    rwa [show (r.prefixByte :: 0x66 :: am.rexByte false 0 :: 0xF7 :: am.modrm 1 ::
      (am.tail ++ immBytes 16 imm)).length = 7 + am.tail.length by simp; omega]

theorem test_r1_m64_imm32_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 32) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (8 + am.tail.length))) 8)
      (codeRange p (0x67 :: encodeTestR1M64Imm32 am imm))
      (Effect.post (testMImm32A32Effect p (8 + am.tail.length) 64 am imm)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact test_r1_m64_imm32_a32_triple_of_bytes p _ hrex am hv hx hb imm

theorem test_r1_m32_imm32_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 32) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeTestR1M32Imm32 am imm).length)) 4)
      (codeRange p (0x67 :: encodeTestR1M32Imm32 am imm))
      (Effect.post (testMImm32A32Effect p (0x67 :: encodeTestR1M32Imm32 am imm).length 32 am imm)) := by
  unfold encodeTestR1M32Imm32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := test_r1_m32_imm32_a32_triple_of_bytes p am hv hx hb imm
    rwa [show (0x67 :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 32 imm)).length =
      7 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := test_r1_m32_imm32_rex_a32_triple_of_bytes p _ hrex am hv hx hb imm
    rwa [show (0x67 :: am.rexByte false 0 :: 0xF7 :: am.modrm 1 ::
      (am.tail ++ immBytes 32 imm)).length = 8 + am.tail.length by simp; omega]

theorem test_r1_m16_imm16_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 16) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeTestR1M16Imm16 am imm).length)) 2)
      (codeRange p (0x67 :: encodeTestR1M16Imm16 am imm))
      (Effect.post (testM16Imm16A32Effect p (0x67 :: encodeTestR1M16Imm16 am imm).length am imm)) := by
  unfold encodeTestR1M16Imm16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := test_r1_m16_imm16_a32_triple_of_bytes p am hv hx hb imm
    rwa [show (0x67 :: 0x66 :: 0xF7 :: am.modrm 1 :: (am.tail ++ immBytes 16 imm)).length =
      6 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := test_r1_m16_imm16_rex_a32_triple_of_bytes p _ hrex am hv hx hb imm
    rwa [show (0x67 :: 0x66 :: am.rexByte false 0 :: 0xF7 :: am.modrm 1 ::
      (am.tail ++ immBytes 16 imm)).length = 7 + am.tail.length by simp; omega]

end X86Proofs
