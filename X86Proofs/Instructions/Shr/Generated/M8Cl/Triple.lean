import X86Proofs.Instructions.Shr.Generated.M8Cl.Step
import X86Proofs.Instructions.Shr.Generated.M8Cl.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Shr.Generated.MCl.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem shr_m8_cl_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (RmwPre p am 1 (2 + am.tail.length))
      (codeRange p (0xD2 :: am.modrm 5 :: am.tail))
      (shrMClEffect p (2 + am.tail.length) 8 am) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := shr_m8_cl_step s h [] (by simp) (by simp)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · apply shrFlags_allows

theorem shr_m8_cl_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (RmwPre p am 1 (2 + am.tail.length))
      (codeRange p (0xD2 :: am.modrm 5 :: am.tail))
      (Effect.post (shrMClEffect p (2 + am.tail.length) 8 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shrMClEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (shr_m8_cl_effect_step p am hv hx hb)

theorem shr_m8_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 1 (3 + am.tail.length))
      (codeRange p (rex :: 0xD2 :: am.modrm 5 :: am.tail))
      (shrMClEffect p (3 + am.tail.length) 8 am) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := shr_m8_cl_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · apply shrFlags_allows

theorem shr_m8_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 1 (3 + am.tail.length))
      (codeRange p (rex :: 0xD2 :: am.modrm 5 :: am.tail))
      (Effect.post (shrMClEffect p (3 + am.tail.length) 8 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shrMClEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (shr_m8_cl_rex_effect_step p rex hr am hv hx hb)

theorem shr_m8_cl_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (SegRmwPre p r base am 1 (3 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xD2 :: am.modrm 5 :: am.tail))
      (shrMClSegEffect p (3 + am.tail.length) 8 base am) := by
  intro s h hcode hpre
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
  have hstep := shr_m8_cl_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · apply shrFlags_allows

theorem shr_m8_cl_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (SegRmwPre p r base am 1 (3 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xD2 :: am.modrm 5 :: am.tail))
      (Effect.post (shrMClSegEffect p (3 + am.tail.length) 8 base am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shrMClSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (shr_m8_cl_seg_effect_step p r base am hv hx hb)

theorem shr_m8_cl_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegRmwPre p r base am 1 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xD2 :: am.modrm 5 :: am.tail))
      (shrMClSegEffect p (4 + am.tail.length) 8 base am) := by
  intro s h hcode hpre
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
  have hstep := shr_m8_cl_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · apply shrFlags_allows

theorem shr_m8_cl_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegRmwPre p r base am 1 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xD2 :: am.modrm 5 :: am.tail))
      (Effect.post (shrMClSegEffect p (4 + am.tail.length) 8 base am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shrMClSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (shr_m8_cl_rex_seg_effect_step p r base rex hr am hv hx hb)

theorem shr_m8_cl_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (Rmw32Pre p am 1 (3 + am.tail.length))
      (codeRange p (0x67 :: 0xD2 :: am.modrm 5 :: am.tail))
      (shrMClA32Effect p (3 + am.tail.length) 8 am) := by
  intro s h hcode hpre
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
  have hstep := shr_m8_cl_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · apply shrFlags_allows

theorem shr_m8_cl_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (Rmw32Pre p am 1 (3 + am.tail.length))
      (codeRange p (0x67 :: 0xD2 :: am.modrm 5 :: am.tail))
      (Effect.post (shrMClA32Effect p (3 + am.tail.length) 8 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shrMClA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (shr_m8_cl_a32_effect_step p am hv hx hb)

theorem shr_m8_cl_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Rmw32Pre p am 1 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xD2 :: am.modrm 5 :: am.tail))
      (shrMClA32Effect p (4 + am.tail.length) 8 am) := by
  intro s h hcode hpre
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
  have hstep := shr_m8_cl_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · apply shrFlags_allows

theorem shr_m8_cl_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (Rmw32Pre p am 1 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xD2 :: am.modrm 5 :: am.tail))
      (Effect.post (shrMClA32Effect p (4 + am.tail.length) 8 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shrMClA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (shr_m8_cl_rex_a32_effect_step p rex hr am hv hx hb)

theorem shr_m8_cl_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (RmwPre p am 1 (encodeShrM8Cl am).length)
      (codeRange p (encodeShrM8Cl am))
      (Effect.post (shrMClEffect p (encodeShrM8Cl am).length 8 am)) := by
  unfold encodeShrM8Cl
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := shr_m8_cl_triple_of_bytes p am hv hx hb
    rwa [show (0xD2 :: am.modrm 5 :: am.tail).length =
      2 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := shr_m8_cl_rex_triple_of_bytes p _ hrex.rexPrefix am hv hx hb
    rwa [show (am.rexByte false 0 ::
      0xD2 :: am.modrm 5 :: am.tail).length =
      3 + am.tail.length by simp; omega]

theorem shr_m8_cl_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegRmwPre p r base am 1 (r.prefixByte :: encodeShrM8Cl am).length)
      (codeRange p (r.prefixByte :: encodeShrM8Cl am))
      (Effect.post (shrMClSegEffect p (r.prefixByte :: encodeShrM8Cl am).length 8 base am)) := by
  unfold encodeShrM8Cl
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := shr_m8_cl_seg_triple_of_bytes p r base am hv hx hb
    rwa [show (r.prefixByte :: 0xD2 :: am.modrm 5 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := shr_m8_cl_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix am hv hx hb
    rwa [show (r.prefixByte :: am.rexByte false 0 ::
      0xD2 :: am.modrm 5 :: am.tail).length =
      4 + am.tail.length by simp; omega]

theorem shr_m8_cl_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (Rmw32Pre p am 1 (0x67 :: encodeShrM8Cl am).length)
      (codeRange p (0x67 :: encodeShrM8Cl am))
      (Effect.post (shrMClA32Effect p (0x67 :: encodeShrM8Cl am).length 8 am)) := by
  unfold encodeShrM8Cl
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := shr_m8_cl_a32_triple_of_bytes p am hv hx hb
    rwa [show (0x67 :: 0xD2 :: am.modrm 5 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := shr_m8_cl_rex_a32_triple_of_bytes p _ hrex.rexPrefix am hv hx hb
    rwa [show (0x67 :: am.rexByte false 0 ::
      0xD2 :: am.modrm 5 :: am.tail).length =
      4 + am.tail.length by simp; omega]

end X86Proofs
