import X86Proofs.Instructions.Not.Generated.M8.Step
import X86Proofs.Instructions.Not.Generated.M8.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Not.Generated.M.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem not_m8_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (RmwPre p am 1 (2 + am.tail.length))
      (codeRange p (0xF6 :: am.modrm 2 :: am.tail))
      (notMEffect p (2 + am.tail.length) 8 am) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := not_m8_step s h [] (by simp) (by simp)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwResult h _ _ _ _ hread.low htables,
    ⟨afterStep_rmwResult_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_rmwResult s _ _ _ _⟩⟩
  exact Operand.read_afterStep_rmwResult (n := 8) s _ (by decide) (by decide) _ _ _

theorem not_m8_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (RmwPre p am 1 (2 + am.tail.length))
      (codeRange p (0xF6 :: am.modrm 2 :: am.tail))
      (Effect.post (notMEffect p (2 + am.tail.length) 8 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [notMEffect_components]; exact mem_components_rmwResult _ _) hpre.code (by simp; omega))
    (not_m8_effect_step p am hv hx hb)

theorem not_m8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 1 (3 + am.tail.length))
      (codeRange p (rex :: 0xF6 :: am.modrm 2 :: am.tail))
      (notMEffect p (3 + am.tail.length) 8 am) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := not_m8_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwResult h _ _ _ _ hread.low htables,
    ⟨afterStep_rmwResult_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_rmwResult s _ _ _ _⟩⟩
  exact Operand.read_afterStep_rmwResult (n := 8) s _ (by decide) (by decide) _ _ _

theorem not_m8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 1 (3 + am.tail.length))
      (codeRange p (rex :: 0xF6 :: am.modrm 2 :: am.tail))
      (Effect.post (notMEffect p (3 + am.tail.length) 8 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [notMEffect_components]; exact mem_components_rmwResult _ _) hpre.code (by simp; omega))
    (not_m8_rex_effect_step p rex hr am hv hx hb)

theorem not_m8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (SegRmwPre p r base am 1 (3 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF6 :: am.modrm 2 :: am.tail))
      (notMSegEffect p (3 + am.tail.length) 8 base am) := by
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
  have hstep := not_m8_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwResult h _ _ _ _ hread.low htables,
    ⟨afterStep_rmwResult_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_rmwResult s _ _ _ _⟩⟩
  exact Operand.read_afterStep_rmwResult (n := 8) s _ (by decide) (by decide) _ _ _

theorem not_m8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (SegRmwPre p r base am 1 (3 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF6 :: am.modrm 2 :: am.tail))
      (Effect.post (notMSegEffect p (3 + am.tail.length) 8 base am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [notMSegEffect_components]; exact mem_components_rmwResult _ _) hpre.store.code (by simp; omega))
    (not_m8_seg_effect_step p r base am hv hx hb)

theorem not_m8_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegRmwPre p r base am 1 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xF6 :: am.modrm 2 :: am.tail))
      (notMSegEffect p (4 + am.tail.length) 8 base am) := by
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
  have hstep := not_m8_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwResult h _ _ _ _ hread.low htables,
    ⟨afterStep_rmwResult_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_rmwResult s _ _ _ _⟩⟩
  exact Operand.read_afterStep_rmwResult (n := 8) s _ (by decide) (by decide) _ _ _

theorem not_m8_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegRmwPre p r base am 1 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xF6 :: am.modrm 2 :: am.tail))
      (Effect.post (notMSegEffect p (4 + am.tail.length) 8 base am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [notMSegEffect_components]; exact mem_components_rmwResult _ _) hpre.store.code (by simp; omega))
    (not_m8_rex_seg_effect_step p r base rex hr am hv hx hb)

theorem not_m8_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (Rmw32Pre p am 1 (3 + am.tail.length))
      (codeRange p (0x67 :: 0xF6 :: am.modrm 2 :: am.tail))
      (notMA32Effect p (3 + am.tail.length) 8 am) := by
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
  have hstep := not_m8_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwResult h _ _ _ _ hread.low htables,
    ⟨afterStep_rmwResult_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_rmwResult s _ _ _ _⟩⟩
  exact Operand.read_afterStep_rmwResult (n := 8) s _ (by decide) (by decide) _ _ _

theorem not_m8_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (Rmw32Pre p am 1 (3 + am.tail.length))
      (codeRange p (0x67 :: 0xF6 :: am.modrm 2 :: am.tail))
      (Effect.post (notMA32Effect p (3 + am.tail.length) 8 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [notMA32Effect_components]; exact mem_components_rmwResult _ _) hpre.code (by simp; omega))
    (not_m8_a32_effect_step p am hv hx hb)

theorem not_m8_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Rmw32Pre p am 1 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xF6 :: am.modrm 2 :: am.tail))
      (notMA32Effect p (4 + am.tail.length) 8 am) := by
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
  have hstep := not_m8_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwResult h _ _ _ _ hread.low htables,
    ⟨afterStep_rmwResult_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_rmwResult s _ _ _ _⟩⟩
  exact Operand.read_afterStep_rmwResult (n := 8) s _ (by decide) (by decide) _ _ _

theorem not_m8_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (Rmw32Pre p am 1 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xF6 :: am.modrm 2 :: am.tail))
      (Effect.post (notMA32Effect p (4 + am.tail.length) 8 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [notMA32Effect_components]; exact mem_components_rmwResult _ _) hpre.code (by simp; omega))
    (not_m8_rex_a32_effect_step p rex hr am hv hx hb)

theorem not_m8_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (RmwPre p am 1 (encodeNotM8 am).length)
      (codeRange p (encodeNotM8 am))
      (Effect.post (notMEffect p (encodeNotM8 am).length 8 am)) := by
  unfold encodeNotM8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := not_m8_triple_of_bytes p am hv hx hb
    rwa [show (0xF6 :: am.modrm 2 :: am.tail).length =
      2 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := not_m8_rex_triple_of_bytes p _ hrex.rexPrefix am hv hx hb
    rwa [show (am.rexByte false 0 :: 0xF6 :: am.modrm 2 :: am.tail).length =
      3 + am.tail.length by simp; omega]

theorem not_m8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegRmwPre p r base am 1 (r.prefixByte :: encodeNotM8 am).length)
      (codeRange p (r.prefixByte :: encodeNotM8 am))
      (Effect.post (notMSegEffect p (r.prefixByte :: encodeNotM8 am).length 8 base am)) := by
  unfold encodeNotM8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := not_m8_seg_triple_of_bytes p r base am hv hx hb
    rwa [show (r.prefixByte :: 0xF6 :: am.modrm 2 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := not_m8_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix am hv hx hb
    rwa [show (r.prefixByte :: am.rexByte false 0 :: 0xF6 :: am.modrm 2 ::
      am.tail).length = 4 + am.tail.length by simp; omega]

theorem not_m8_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (Rmw32Pre p am 1 (0x67 :: encodeNotM8 am).length)
      (codeRange p (0x67 :: encodeNotM8 am))
      (Effect.post (notMA32Effect p (0x67 :: encodeNotM8 am).length 8 am)) := by
  unfold encodeNotM8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := not_m8_a32_triple_of_bytes p am hv hx hb
    rwa [show (0x67 :: 0xF6 :: am.modrm 2 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := not_m8_rex_a32_triple_of_bytes p _ hrex.rexPrefix am hv hx hb
    rwa [show (0x67 :: am.rexByte false 0 :: 0xF6 :: am.modrm 2 ::
      am.tail).length = 4 + am.tail.length by simp; omega]

end X86Proofs
