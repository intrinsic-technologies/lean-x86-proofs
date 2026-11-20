import X86Proofs.Instructions.Not.Generated.M.Step
import X86Proofs.Instructions.Not.Generated.M.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def notMEffect (p : BitVec 64) (len n : Nat) (am : AddrMode) (s : RamState) : Effect :=
  let addr := am.addr s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand n).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem addr : Operand n), ~~~a⟩] }

@[simp] theorem notMEffect_components (p : BitVec 64) (len n : Nat) (am : AddrMode) (s : RamState) :
    (notMEffect p len n am s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) (n / 8), .rip] := rfl

def notMSegEffect (p : BitVec 64) (len n : Nat) (base : BitVec 64) (am : AddrMode) (s : RamState) :
    Effect :=
  let addr := base + am.addr s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand n).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem addr : Operand n), ~~~a⟩] }

@[simp] theorem notMSegEffect_components (p : BitVec 64) (len n : Nat) (base : BitVec 64)
    (am : AddrMode) (s : RamState) : (notMSegEffect p len n base am s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) (n / 8), .rip] :=
  rfl

def notMA32Effect (p : BitVec 64) (len n : Nat) (am : AddrMode) (s : RamState) : Effect :=
  let addr := am.addr32 s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand n).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem addr : Operand n), ~~~a⟩] }

@[simp] theorem notMA32Effect_components (p : BitVec 64) (len n : Nat) (am : AddrMode)
    (s : RamState) : (notMA32Effect p len n am s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) (n / 8), .rip] :=
  rfl

theorem not_m64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 8 (3 + am.tail.length))
      (codeRange p (rex :: 0xF7 :: am.modrm 2 :: am.tail))
      (notMEffect p (3 + am.tail.length) 64 am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := not_m_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwResult h _ _ _ _ hread.low htables,
    ⟨afterStep_rmwResult_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_rmwResult s _ _ _ _⟩⟩
  exact Operand.read_afterStep_rmwResult (n := 64) s _ (by decide) (by decide) _ _ _

theorem not_m64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 8 (3 + am.tail.length))
      (codeRange p (rex :: 0xF7 :: am.modrm 2 :: am.tail))
      (Effect.post (notMEffect p (3 + am.tail.length) 64 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [notMEffect_components]; exact mem_components_rmwResult _ _) hpre.code (by simp; omega))
    (not_m64_effect_step p rex hrex am hv hx hb)

theorem not_m32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (RmwPre p am 4 (2 + am.tail.length))
      (codeRange p (0xF7 :: am.modrm 2 :: am.tail))
      (notMEffect p (2 + am.tail.length) 32 am) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := not_m_step s h [] (by simp) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwResult h _ _ _ _ hread.low htables,
    ⟨afterStep_rmwResult_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_rmwResult s _ _ _ _⟩⟩
  exact Operand.read_afterStep_rmwResult (n := 32) s _ (by decide) (by decide) _ _ _

theorem not_m32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (RmwPre p am 4 (2 + am.tail.length))
      (codeRange p (0xF7 :: am.modrm 2 :: am.tail))
      (Effect.post (notMEffect p (2 + am.tail.length) 32 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [notMEffect_components]; exact mem_components_rmwResult _ _) hpre.code (by simp; omega))
    (not_m32_effect_step p am hv hx hb)

theorem not_m32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 4 (3 + am.tail.length))
      (codeRange p (rex :: 0xF7 :: am.modrm 2 :: am.tail))
      (notMEffect p (3 + am.tail.length) 32 am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := not_m_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwResult h _ _ _ _ hread.low htables,
    ⟨afterStep_rmwResult_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_rmwResult s _ _ _ _⟩⟩
  exact Operand.read_afterStep_rmwResult (n := 32) s _ (by decide) (by decide) _ _ _

theorem not_m32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 4 (3 + am.tail.length))
      (codeRange p (rex :: 0xF7 :: am.modrm 2 :: am.tail))
      (Effect.post (notMEffect p (3 + am.tail.length) 32 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [notMEffect_components]; exact mem_components_rmwResult _ _) hpre.code (by simp; omega))
    (not_m32_rex_effect_step p rex hrex am hv hx hb)

theorem not_m16_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (RmwPre p am 2 (3 + am.tail.length))
      (codeRange p (0x66 :: 0xF7 :: am.modrm 2 :: am.tail))
      (notMEffect p (3 + am.tail.length) 16 am) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := not_m16_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.osz _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwResult h _ _ _ _ hread.low htables,
    ⟨afterStep_rmwResult_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_rmwResult s _ _ _ _⟩⟩
  exact Operand.read_afterStep_rmwResult (n := 16) s _ (by decide) (by decide) _ _ _

theorem not_m16_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (RmwPre p am 2 (3 + am.tail.length))
      (codeRange p (0x66 :: 0xF7 :: am.modrm 2 :: am.tail))
      (Effect.post (notMEffect p (3 + am.tail.length) 16 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [notMEffect_components]; exact mem_components_rmwResult _ _) hpre.code (by simp; omega))
    (not_m16_effect_step p am hv hx hb)

theorem not_m16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 2 (4 + am.tail.length))
      (codeRange p (0x66 :: rex :: 0xF7 :: am.modrm 2 :: am.tail))
      (notMEffect p (4 + am.tail.length) 16 am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := not_m16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_66_rex _ _ hr]; exact (AddrContext.oszRex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_66_rex _ _ hr]; exact hread)
  simp only [scanContext_66_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwResult h _ _ _ _ hread.low htables,
    ⟨afterStep_rmwResult_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_rmwResult s _ _ _ _⟩⟩
  exact Operand.read_afterStep_rmwResult (n := 16) s _ (by decide) (by decide) _ _ _

theorem not_m16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 2 (4 + am.tail.length))
      (codeRange p (0x66 :: rex :: 0xF7 :: am.modrm 2 :: am.tail))
      (Effect.post (notMEffect p (4 + am.tail.length) 16 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [notMEffect_components]; exact mem_components_rmwResult _ _) hpre.code (by simp; omega))
    (not_m16_rex_effect_step p rex hrex am hv hx hb)

theorem not_m64_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegRmwPre p r base am 8 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xF7 :: am.modrm 2 :: am.tail))
      (notMSegEffect p (4 + am.tail.length) 64 base am) := by
  have hr := hrex.rexPrefix
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
  have hstep := not_m_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwResult h _ _ _ _ hread.low htables,
    ⟨afterStep_rmwResult_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_rmwResult s _ _ _ _⟩⟩
  exact Operand.read_afterStep_rmwResult (n := 64) s _ (by decide) (by decide) _ _ _

theorem not_m64_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegRmwPre p r base am 8 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xF7 :: am.modrm 2 :: am.tail))
      (Effect.post (notMSegEffect p (4 + am.tail.length) 64 base am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [notMSegEffect_components]; exact mem_components_rmwResult _ _) hpre.store.code (by simp; omega))
    (not_m64_seg_effect_step p r base rex hrex am hv hx hb)

theorem not_m32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (SegRmwPre p r base am 4 (3 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF7 :: am.modrm 2 :: am.tail))
      (notMSegEffect p (3 + am.tail.length) 32 base am) := by
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
  have hstep := not_m_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwResult h _ _ _ _ hread.low htables,
    ⟨afterStep_rmwResult_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_rmwResult s _ _ _ _⟩⟩
  exact Operand.read_afterStep_rmwResult (n := 32) s _ (by decide) (by decide) _ _ _

theorem not_m32_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (SegRmwPre p r base am 4 (3 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xF7 :: am.modrm 2 :: am.tail))
      (Effect.post (notMSegEffect p (3 + am.tail.length) 32 base am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [notMSegEffect_components]; exact mem_components_rmwResult _ _) hpre.store.code (by simp; omega))
    (not_m32_seg_effect_step p r base am hv hx hb)

theorem not_m32_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegRmwPre p r base am 4 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xF7 :: am.modrm 2 :: am.tail))
      (notMSegEffect p (4 + am.tail.length) 32 base am) := by
  have hr := hrex.rexPrefix
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
  have hstep := not_m_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwResult h _ _ _ _ hread.low htables,
    ⟨afterStep_rmwResult_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_rmwResult s _ _ _ _⟩⟩
  exact Operand.read_afterStep_rmwResult (n := 32) s _ (by decide) (by decide) _ _ _

theorem not_m32_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegRmwPre p r base am 4 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xF7 :: am.modrm 2 :: am.tail))
      (Effect.post (notMSegEffect p (4 + am.tail.length) 32 base am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [notMSegEffect_components]; exact mem_components_rmwResult _ _) hpre.store.code (by simp; omega))
    (not_m32_rex_seg_effect_step p r base rex hrex am hv hx hb)

theorem not_m16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (SegRmwPre p r base am 2 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: 0xF7 :: am.modrm 2 :: am.tail))
      (notMSegEffect p (4 + am.tail.length) 16 base am) := by
  intro s h hcode hpre
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
  have hstep := not_m16_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwResult h _ _ _ _ hread.low htables,
    ⟨afterStep_rmwResult_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_rmwResult s _ _ _ _⟩⟩
  exact Operand.read_afterStep_rmwResult (n := 16) s _ (by decide) (by decide) _ _ _

theorem not_m16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (SegRmwPre p r base am 2 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: 0xF7 :: am.modrm 2 :: am.tail))
      (Effect.post (notMSegEffect p (4 + am.tail.length) 16 base am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [notMSegEffect_components]; exact mem_components_rmwResult _ _) hpre.store.code (by simp; omega))
    (not_m16_seg_effect_step p r base am hv hx hb)

theorem not_m16_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegRmwPre p r base am 2 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0xF7 :: am.modrm 2 :: am.tail))
      (notMSegEffect p (5 + am.tail.length) 16 base am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
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
  have hstep := not_m16_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwResult h _ _ _ _ hread.low htables,
    ⟨afterStep_rmwResult_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_rmwResult s _ _ _ _⟩⟩
  exact Operand.read_afterStep_rmwResult (n := 16) s _ (by decide) (by decide) _ _ _

theorem not_m16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegRmwPre p r base am 2 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0xF7 :: am.modrm 2 :: am.tail))
      (Effect.post (notMSegEffect p (5 + am.tail.length) 16 base am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [notMSegEffect_components]; exact mem_components_rmwResult _ _) hpre.store.code (by simp; omega))
    (not_m16_rex_seg_effect_step p r base rex hrex am hv hx hb)

theorem not_m64_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Rmw32Pre p am 8 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xF7 :: am.modrm 2 :: am.tail))
      (notMA32Effect p (4 + am.tail.length) 64 am) := by
  have hr := hrex.rexPrefix
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
  have hstep := not_m_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwResult h _ _ _ _ hread.low htables,
    ⟨afterStep_rmwResult_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_rmwResult s _ _ _ _⟩⟩
  exact Operand.read_afterStep_rmwResult (n := 64) s _ (by decide) (by decide) _ _ _

theorem not_m64_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (Rmw32Pre p am 8 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xF7 :: am.modrm 2 :: am.tail))
      (Effect.post (notMA32Effect p (4 + am.tail.length) 64 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [notMA32Effect_components]; exact mem_components_rmwResult _ _) hpre.code (by simp; omega))
    (not_m64_a32_effect_step p rex hrex am hv hx hb)

theorem not_m32_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (Rmw32Pre p am 4 (3 + am.tail.length))
      (codeRange p (0x67 :: 0xF7 :: am.modrm 2 :: am.tail))
      (notMA32Effect p (3 + am.tail.length) 32 am) := by
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
  have hstep := not_m_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwResult h _ _ _ _ hread.low htables,
    ⟨afterStep_rmwResult_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_rmwResult s _ _ _ _⟩⟩
  exact Operand.read_afterStep_rmwResult (n := 32) s _ (by decide) (by decide) _ _ _

theorem not_m32_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (Rmw32Pre p am 4 (3 + am.tail.length))
      (codeRange p (0x67 :: 0xF7 :: am.modrm 2 :: am.tail))
      (Effect.post (notMA32Effect p (3 + am.tail.length) 32 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [notMA32Effect_components]; exact mem_components_rmwResult _ _) hpre.code (by simp; omega))
    (not_m32_a32_effect_step p am hv hx hb)

theorem not_m32_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Rmw32Pre p am 4 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xF7 :: am.modrm 2 :: am.tail))
      (notMA32Effect p (4 + am.tail.length) 32 am) := by
  have hr := hrex.rexPrefix
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
  have hstep := not_m_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwResult h _ _ _ _ hread.low htables,
    ⟨afterStep_rmwResult_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_rmwResult s _ _ _ _⟩⟩
  exact Operand.read_afterStep_rmwResult (n := 32) s _ (by decide) (by decide) _ _ _

theorem not_m32_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (Rmw32Pre p am 4 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xF7 :: am.modrm 2 :: am.tail))
      (Effect.post (notMA32Effect p (4 + am.tail.length) 32 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [notMA32Effect_components]; exact mem_components_rmwResult _ _) hpre.code (by simp; omega))
    (not_m32_rex_a32_effect_step p rex hrex am hv hx hb)

theorem not_m16_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (Rmw32Pre p am 2 (4 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: 0xF7 :: am.modrm 2 :: am.tail))
      (notMA32Effect p (4 + am.tail.length) 16 am) := by
  intro s h hcode hpre
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
  have hstep := not_m16_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwResult h _ _ _ _ hread.low htables,
    ⟨afterStep_rmwResult_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_rmwResult s _ _ _ _⟩⟩
  exact Operand.read_afterStep_rmwResult (n := 16) s _ (by decide) (by decide) _ _ _

theorem not_m16_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (Rmw32Pre p am 2 (4 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: 0xF7 :: am.modrm 2 :: am.tail))
      (Effect.post (notMA32Effect p (4 + am.tail.length) 16 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [notMA32Effect_components]; exact mem_components_rmwResult _ _) hpre.code (by simp; omega))
    (not_m16_a32_effect_step p am hv hx hb)

theorem not_m16_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Rmw32Pre p am 2 (5 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: rex :: 0xF7 :: am.modrm 2 :: am.tail))
      (notMA32Effect p (5 + am.tail.length) 16 am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
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
  have hstep := not_m16_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmwResult h _ _ _ _ hread.low htables,
    ⟨afterStep_rmwResult_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_rmwResult s _ _ _ _⟩⟩
  exact Operand.read_afterStep_rmwResult (n := 16) s _ (by decide) (by decide) _ _ _

theorem not_m16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (Rmw32Pre p am 2 (5 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: rex :: 0xF7 :: am.modrm 2 :: am.tail))
      (Effect.post (notMA32Effect p (5 + am.tail.length) 16 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [notMA32Effect_components]; exact mem_components_rmwResult _ _) hpre.code (by simp; omega))
    (not_m16_rex_a32_effect_step p rex hrex am hv hx hb)

theorem not_m64_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (RmwPre p am 8 (3 + am.tail.length))
      (codeRange p (encodeNotM64 am))
      (Effect.post (notMEffect p (3 + am.tail.length) 64 am)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact not_m64_triple_of_bytes p _ hrex am hv hx hb

theorem not_m32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (RmwPre p am 4 (encodeNotM32 am).length)
      (codeRange p (encodeNotM32 am))
      (Effect.post (notMEffect p (encodeNotM32 am).length 32 am)) := by
  unfold encodeNotM32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := not_m32_triple_of_bytes p am hv hx hb
    rwa [show (0xF7 :: am.modrm 2 :: am.tail).length =
      2 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := not_m32_rex_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (am.rexByte false 0 :: 0xF7 :: am.modrm 2 :: am.tail).length =
      3 + am.tail.length by simp; omega]

theorem not_m16_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (RmwPre p am 2 (encodeNotM16 am).length)
      (codeRange p (encodeNotM16 am))
      (Effect.post (notMEffect p (encodeNotM16 am).length 16 am)) := by
  unfold encodeNotM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := not_m16_triple_of_bytes p am hv hx hb
    rwa [show (0x66 :: 0xF7 :: am.modrm 2 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := not_m16_rex_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (0x66 :: am.rexByte false 0 :: 0xF7 :: am.modrm 2 :: am.tail).length =
      4 + am.tail.length by simp; omega]

theorem not_m64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegRmwPre p r base am 8 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: encodeNotM64 am))
      (Effect.post (notMSegEffect p (4 + am.tail.length) 64 base am)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact not_m64_seg_triple_of_bytes p r base _ hrex am hv hx hb

theorem not_m32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegRmwPre p r base am 4 (r.prefixByte :: encodeNotM32 am).length)
      (codeRange p (r.prefixByte :: encodeNotM32 am))
      (Effect.post (notMSegEffect p (r.prefixByte :: encodeNotM32 am).length 32 base am)) := by
  unfold encodeNotM32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := not_m32_seg_triple_of_bytes p r base am hv hx hb
    rwa [show (r.prefixByte :: 0xF7 :: am.modrm 2 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := not_m32_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb
    rwa [show (r.prefixByte :: am.rexByte false 0 :: 0xF7 :: am.modrm 2 ::
      am.tail).length = 4 + am.tail.length by simp; omega]

theorem not_m16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegRmwPre p r base am 2 (r.prefixByte :: encodeNotM16 am).length)
      (codeRange p (r.prefixByte :: encodeNotM16 am))
      (Effect.post (notMSegEffect p (r.prefixByte :: encodeNotM16 am).length 16 base am)) := by
  unfold encodeNotM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := not_m16_seg_triple_of_bytes p r base am hv hx hb
    rwa [show (r.prefixByte :: 0x66 :: 0xF7 :: am.modrm 2 :: am.tail).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := not_m16_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb
    rwa [show (r.prefixByte :: 0x66 :: am.rexByte false 0 :: 0xF7 :: am.modrm 2 ::
      am.tail).length = 5 + am.tail.length by simp; omega]

theorem not_m64_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (Rmw32Pre p am 8 (4 + am.tail.length))
      (codeRange p (0x67 :: encodeNotM64 am))
      (Effect.post (notMA32Effect p (4 + am.tail.length) 64 am)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact not_m64_a32_triple_of_bytes p _ hrex am hv hx hb

theorem not_m32_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (Rmw32Pre p am 4 (0x67 :: encodeNotM32 am).length)
      (codeRange p (0x67 :: encodeNotM32 am))
      (Effect.post (notMA32Effect p (0x67 :: encodeNotM32 am).length 32 am)) := by
  unfold encodeNotM32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := not_m32_a32_triple_of_bytes p am hv hx hb
    rwa [show (0x67 :: 0xF7 :: am.modrm 2 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := not_m32_rex_a32_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (0x67 :: am.rexByte false 0 :: 0xF7 :: am.modrm 2 ::
      am.tail).length = 4 + am.tail.length by simp; omega]

theorem not_m16_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (Rmw32Pre p am 2 (0x67 :: encodeNotM16 am).length)
      (codeRange p (0x67 :: encodeNotM16 am))
      (Effect.post (notMA32Effect p (0x67 :: encodeNotM16 am).length 16 am)) := by
  unfold encodeNotM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := not_m16_a32_triple_of_bytes p am hv hx hb
    rwa [show (0x67 :: 0x66 :: 0xF7 :: am.modrm 2 :: am.tail).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := not_m16_rex_a32_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (0x67 :: 0x66 :: am.rexByte false 0 :: 0xF7 :: am.modrm 2 ::
      am.tail).length = 5 + am.tail.length by simp; omega]

attribute [x86_compose] notMEffect notMSegEffect notMA32Effect

theorem notMEffect_local {p : BitVec 64} {len n : Nat} {am : AddrMode} (hn : n % 8 = 0) :
    Effect.Local (notMEffect p len n am) := by
  effect_local [notMEffect, hn]

@[x86_local] theorem notMEffect_local64 {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (notMEffect p len 64 am) :=
  notMEffect_local (by decide)

@[x86_local] theorem notMEffect_local32 {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (notMEffect p len 32 am) :=
  notMEffect_local (by decide)

@[x86_local] theorem notMEffect_local16 {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (notMEffect p len 16 am) :=
  notMEffect_local (by decide)

@[x86_local] theorem notMEffect_local8 {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (notMEffect p len 8 am) :=
  notMEffect_local (by decide)

theorem notMSegEffect_local {p : BitVec 64} {len n : Nat} {base : BitVec 64} {am : AddrMode}
    (hn : n % 8 = 0) : Effect.Local (notMSegEffect p len n base am) := by
  effect_local [notMSegEffect, hn]

@[x86_local] theorem notMSegEffect_local64 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} : Effect.Local (notMSegEffect p len 64 base am) :=
  notMSegEffect_local (by decide)

@[x86_local] theorem notMSegEffect_local32 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} : Effect.Local (notMSegEffect p len 32 base am) :=
  notMSegEffect_local (by decide)

@[x86_local] theorem notMSegEffect_local16 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} : Effect.Local (notMSegEffect p len 16 base am) :=
  notMSegEffect_local (by decide)

@[x86_local] theorem notMSegEffect_local8 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} : Effect.Local (notMSegEffect p len 8 base am) :=
  notMSegEffect_local (by decide)

theorem notMA32Effect_local {p : BitVec 64} {len n : Nat} {am : AddrMode} (hn : n % 8 = 0) :
    Effect.Local (notMA32Effect p len n am) := by
  effect_local [notMA32Effect, hn]

@[x86_local] theorem notMA32Effect_local64 {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (notMA32Effect p len 64 am) :=
  notMA32Effect_local (by decide)

@[x86_local] theorem notMA32Effect_local32 {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (notMA32Effect p len 32 am) :=
  notMA32Effect_local (by decide)

@[x86_local] theorem notMA32Effect_local16 {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (notMA32Effect p len 16 am) :=
  notMA32Effect_local (by decide)

@[x86_local] theorem notMA32Effect_local8 {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (notMA32Effect p len 8 am) :=
  notMA32Effect_local (by decide)

end X86Proofs
