import X86Proofs.Instructions.Rcr.Generated.M8Cl.Step
import X86Proofs.Instructions.Rcr.Generated.M8Cl.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Rcr.Generated.MCl.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem rcr_m8_cl_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (cf : Bool) :
    StepEffect (fun s => RmwPre p am 1 (2 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0xD2 :: am.modrm 3 :: am.tail))
      (rcrMClEffect p (2 + am.tail.length) 8 am cf) := by
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := rcr_m8_cl_step s h [] (by simp) (by simp)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · apply rcrFlags_allows

theorem rcr_m8_cl_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (cf : Bool) :
    Triple (fun s => RmwPre p am 1 (2 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0xD2 :: am.modrm 3 :: am.tail))
      (Effect.post (rcrMClEffect p (2 + am.tail.length) 8 am cf)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rcrMClEffect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (rcr_m8_cl_effect_step p am hv hx hb cf)

theorem rcr_m8_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    StepEffect (fun s => RmwPre p am 1 (3 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (rex :: 0xD2 :: am.modrm 3 :: am.tail))
      (rcrMClEffect p (3 + am.tail.length) 8 am cf) := by
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := rcr_m8_cl_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · apply rcrFlags_allows

theorem rcr_m8_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    Triple (fun s => RmwPre p am 1 (3 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (rex :: 0xD2 :: am.modrm 3 :: am.tail))
      (Effect.post (rcrMClEffect p (3 + am.tail.length) 8 am cf)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rcrMClEffect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (rcr_m8_cl_rex_effect_step p rex hr am hv hx hb cf)

theorem rcr_m8_cl_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (cf : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 1 (3 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (r.prefixByte :: 0xD2 :: am.modrm 3 :: am.tail))
      (rcrMClSegEffect p (3 + am.tail.length) 8 base am cf) := by
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  subst hc
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := rcr_m8_cl_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · apply rcrFlags_allows

theorem rcr_m8_cl_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (cf : Bool) :
    Triple (fun s => SegRmwPre p r base am 1 (3 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (r.prefixByte :: 0xD2 :: am.modrm 3 :: am.tail))
      (Effect.post (rcrMClSegEffect p (3 + am.tail.length) 8 base am cf)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rcrMClSegEffect_components]; exact mem_components_rmw _ _) hpre.1.store.code (by simp; omega))
    (rcr_m8_cl_seg_effect_step p r base am hv hx hb cf)

theorem rcr_m8_cl_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 1 (4 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (r.prefixByte :: rex :: 0xD2 :: am.modrm 3 :: am.tail))
      (rcrMClSegEffect p (4 + am.tail.length) 8 base am cf) := by
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  subst hc
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := rcr_m8_cl_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · apply rcrFlags_allows

theorem rcr_m8_cl_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    Triple (fun s => SegRmwPre p r base am 1 (4 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (r.prefixByte :: rex :: 0xD2 :: am.modrm 3 :: am.tail))
      (Effect.post (rcrMClSegEffect p (4 + am.tail.length) 8 base am cf)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rcrMClSegEffect_components]; exact mem_components_rmw _ _) hpre.1.store.code (by simp; omega))
    (rcr_m8_cl_rex_seg_effect_step p r base rex hr am hv hx hb cf)

theorem rcr_m8_cl_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (cf : Bool) :
    StepEffect (fun s => Rmw32Pre p am 1 (3 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0x67 :: 0xD2 :: am.modrm 3 :: am.tail))
      (rcrMClA32Effect p (3 + am.tail.length) 8 am cf) := by
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := rcr_m8_cl_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · apply rcrFlags_allows

theorem rcr_m8_cl_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (cf : Bool) :
    Triple (fun s => Rmw32Pre p am 1 (3 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0x67 :: 0xD2 :: am.modrm 3 :: am.tail))
      (Effect.post (rcrMClA32Effect p (3 + am.tail.length) 8 am cf)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rcrMClA32Effect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (rcr_m8_cl_a32_effect_step p am hv hx hb cf)

theorem rcr_m8_cl_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    StepEffect (fun s => Rmw32Pre p am 1 (4 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0x67 :: rex :: 0xD2 :: am.modrm 3 :: am.tail))
      (rcrMClA32Effect p (4 + am.tail.length) 8 am cf) := by
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := rcr_m8_cl_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · apply rcrFlags_allows

theorem rcr_m8_cl_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    Triple (fun s => Rmw32Pre p am 1 (4 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0x67 :: rex :: 0xD2 :: am.modrm 3 :: am.tail))
      (Effect.post (rcrMClA32Effect p (4 + am.tail.length) 8 am cf)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rcrMClA32Effect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (rcr_m8_cl_rex_a32_effect_step p rex hr am hv hx hb cf)

theorem rcr_m8_cl_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (cf : Bool) :
    Triple (fun s => RmwPre p am 1 (encodeRcrM8Cl am).length s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (encodeRcrM8Cl am))
      (Effect.post (rcrMClEffect p (encodeRcrM8Cl am).length 8 am cf)) := by
  unfold encodeRcrM8Cl
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rcr_m8_cl_triple_of_bytes p am hv hx hb cf
    rwa [show (0xD2 :: am.modrm 3 :: am.tail).length =
      2 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rcr_m8_cl_rex_triple_of_bytes p _ hrex.rexPrefix am hv hx hb cf
    rwa [show (am.rexByte false 0 ::
      0xD2 :: am.modrm 3 :: am.tail).length =
      3 + am.tail.length by simp; omega]

theorem rcr_m8_cl_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (cf : Bool) :
    Triple (fun s => SegRmwPre p r base am 1 (r.prefixByte :: encodeRcrM8Cl am).length s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (r.prefixByte :: encodeRcrM8Cl am))
      (Effect.post (rcrMClSegEffect p (r.prefixByte :: encodeRcrM8Cl am).length 8 base am cf)) := by
  unfold encodeRcrM8Cl
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rcr_m8_cl_seg_triple_of_bytes p r base am hv hx hb cf
    rwa [show (r.prefixByte :: 0xD2 :: am.modrm 3 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rcr_m8_cl_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix am hv hx hb cf
    rwa [show (r.prefixByte :: am.rexByte false 0 ::
      0xD2 :: am.modrm 3 :: am.tail).length =
      4 + am.tail.length by simp; omega]

theorem rcr_m8_cl_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (cf : Bool) :
    Triple (fun s => Rmw32Pre p am 1 (0x67 :: encodeRcrM8Cl am).length s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0x67 :: encodeRcrM8Cl am))
      (Effect.post (rcrMClA32Effect p (0x67 :: encodeRcrM8Cl am).length 8 am cf)) := by
  unfold encodeRcrM8Cl
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rcr_m8_cl_a32_triple_of_bytes p am hv hx hb cf
    rwa [show (0x67 :: 0xD2 :: am.modrm 3 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rcr_m8_cl_rex_a32_triple_of_bytes p _ hrex.rexPrefix am hv hx hb cf
    rwa [show (0x67 :: am.rexByte false 0 ::
      0xD2 :: am.modrm 3 :: am.tail).length =
      4 + am.tail.length by simp; omega]

end X86Proofs
