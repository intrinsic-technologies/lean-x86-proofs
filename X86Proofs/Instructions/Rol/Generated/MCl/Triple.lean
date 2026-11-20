import X86Proofs.Instructions.Rol.Generated.MCl.Step
import X86Proofs.Instructions.Rol.Generated.MCl.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Rol.Generated.M.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def rolMClEffect (p : BitVec 64) (len n : Nat) (am : AddrMode) (s : RamState) :
    Effect :=
  rolMEffect p len n am (shiftCount n ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem rolMClEffect_components (p : BitVec 64) (len n : Nat) (am : AddrMode)
    (s : RamState) : (rolMClEffect p len n am s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) (n / 8), .flags, .rip] := rfl

def rolMClSegEffect (p : BitVec 64) (len n : Nat) (base : BitVec 64) (am : AddrMode)
    (s : RamState) : Effect :=
  rolMSegEffect p len n base am (shiftCount n ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem rolMClSegEffect_components (p : BitVec 64) (len n : Nat) (base : BitVec 64)
    (am : AddrMode) (s : RamState) : (rolMClSegEffect p len n base am s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) (n / 8), .flags, .rip] := rfl

def rolMClA32Effect (p : BitVec 64) (len n : Nat) (am : AddrMode) (s : RamState) :
    Effect :=
  rolMA32Effect p len n am (shiftCount n ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem rolMClA32Effect_components (p : BitVec 64) (len n : Nat) (am : AddrMode)
    (s : RamState) : (rolMClA32Effect p len n am s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) (n / 8), .flags, .rip] := rfl

theorem rol_m64_cl_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 8 (3 + am.tail.length))
      (codeRange p (rex :: 0xD3 :: am.modrm 0 :: am.tail))
      (rolMClEffect p (3 + am.tail.length) 64 am) := by
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
  have hstep := rol_m_cl_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m64_cl_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 8 (3 + am.tail.length))
      (codeRange p (rex :: 0xD3 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMClEffect p (3 + am.tail.length) 64 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMClEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m64_cl_effect_step p rex hrex am hv hx hb)

theorem rol_m32_cl_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (RmwPre p am 4 (2 + am.tail.length))
      (codeRange p (0xD3 :: am.modrm 0 :: am.tail))
      (rolMClEffect p (2 + am.tail.length) 32 am) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := rol_m_cl_step s h [] (by simp) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m32_cl_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (RmwPre p am 4 (2 + am.tail.length))
      (codeRange p (0xD3 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMClEffect p (2 + am.tail.length) 32 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMClEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m32_cl_effect_step p am hv hx hb)

theorem rol_m32_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 4 (3 + am.tail.length))
      (codeRange p (rex :: 0xD3 :: am.modrm 0 :: am.tail))
      (rolMClEffect p (3 + am.tail.length) 32 am) := by
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
  have hstep := rol_m_cl_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m32_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 4 (3 + am.tail.length))
      (codeRange p (rex :: 0xD3 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMClEffect p (3 + am.tail.length) 32 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMClEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m32_cl_rex_effect_step p rex hrex am hv hx hb)

theorem rol_m16_cl_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (RmwPre p am 2 (3 + am.tail.length))
      (codeRange p (0x66 :: 0xD3 :: am.modrm 0 :: am.tail))
      (rolMClEffect p (3 + am.tail.length) 16 am) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := rol_m16_cl_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.osz _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m16_cl_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (RmwPre p am 2 (3 + am.tail.length))
      (codeRange p (0x66 :: 0xD3 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMClEffect p (3 + am.tail.length) 16 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMClEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m16_cl_effect_step p am hv hx hb)

theorem rol_m16_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 2 (4 + am.tail.length))
      (codeRange p (0x66 :: rex :: 0xD3 :: am.modrm 0 :: am.tail))
      (rolMClEffect p (4 + am.tail.length) 16 am) := by
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
  have hstep := rol_m16_cl_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_66_rex _ _ hr]; exact (AddrContext.oszRex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_66_rex _ _ hr]; exact hread)
  simp only [scanContext_66_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m16_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 2 (4 + am.tail.length))
      (codeRange p (0x66 :: rex :: 0xD3 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMClEffect p (4 + am.tail.length) 16 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMClEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m16_cl_rex_effect_step p rex hrex am hv hx hb)

theorem rol_m64_cl_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegRmwPre p r base am 8 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xD3 :: am.modrm 0 :: am.tail))
      (rolMClSegEffect p (4 + am.tail.length) 64 base am) := by
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
  have hstep := rol_m_cl_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m64_cl_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegRmwPre p r base am 8 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xD3 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMClSegEffect p (4 + am.tail.length) 64 base am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMClSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (rol_m64_cl_seg_effect_step p r base rex hrex am hv hx hb)

theorem rol_m32_cl_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (SegRmwPre p r base am 4 (3 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xD3 :: am.modrm 0 :: am.tail))
      (rolMClSegEffect p (3 + am.tail.length) 32 base am) := by
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
  have hstep := rol_m_cl_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m32_cl_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (SegRmwPre p r base am 4 (3 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xD3 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMClSegEffect p (3 + am.tail.length) 32 base am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMClSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (rol_m32_cl_seg_effect_step p r base am hv hx hb)

theorem rol_m32_cl_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegRmwPre p r base am 4 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xD3 :: am.modrm 0 :: am.tail))
      (rolMClSegEffect p (4 + am.tail.length) 32 base am) := by
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
  have hstep := rol_m_cl_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m32_cl_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegRmwPre p r base am 4 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xD3 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMClSegEffect p (4 + am.tail.length) 32 base am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMClSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (rol_m32_cl_rex_seg_effect_step p r base rex hrex am hv hx hb)

theorem rol_m16_cl_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (SegRmwPre p r base am 2 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: 0xD3 :: am.modrm 0 :: am.tail))
      (rolMClSegEffect p (4 + am.tail.length) 16 base am) := by
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
  have hstep := rol_m16_cl_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m16_cl_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (SegRmwPre p r base am 2 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: 0xD3 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMClSegEffect p (4 + am.tail.length) 16 base am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMClSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (rol_m16_cl_seg_effect_step p r base am hv hx hb)

theorem rol_m16_cl_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegRmwPre p r base am 2 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0xD3 :: am.modrm 0 :: am.tail))
      (rolMClSegEffect p (5 + am.tail.length) 16 base am) := by
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
  have hstep := rol_m16_cl_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m16_cl_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegRmwPre p r base am 2 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0xD3 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMClSegEffect p (5 + am.tail.length) 16 base am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMClSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (rol_m16_cl_rex_seg_effect_step p r base rex hrex am hv hx hb)

theorem rol_m64_cl_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Rmw32Pre p am 8 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xD3 :: am.modrm 0 :: am.tail))
      (rolMClA32Effect p (4 + am.tail.length) 64 am) := by
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
  have hstep := rol_m_cl_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m64_cl_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (Rmw32Pre p am 8 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xD3 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMClA32Effect p (4 + am.tail.length) 64 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMClA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m64_cl_a32_effect_step p rex hrex am hv hx hb)

theorem rol_m32_cl_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (Rmw32Pre p am 4 (3 + am.tail.length))
      (codeRange p (0x67 :: 0xD3 :: am.modrm 0 :: am.tail))
      (rolMClA32Effect p (3 + am.tail.length) 32 am) := by
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
  have hstep := rol_m_cl_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m32_cl_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (Rmw32Pre p am 4 (3 + am.tail.length))
      (codeRange p (0x67 :: 0xD3 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMClA32Effect p (3 + am.tail.length) 32 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMClA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m32_cl_a32_effect_step p am hv hx hb)

theorem rol_m32_cl_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Rmw32Pre p am 4 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xD3 :: am.modrm 0 :: am.tail))
      (rolMClA32Effect p (4 + am.tail.length) 32 am) := by
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
  have hstep := rol_m_cl_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m32_cl_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (Rmw32Pre p am 4 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xD3 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMClA32Effect p (4 + am.tail.length) 32 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMClA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m32_cl_rex_a32_effect_step p rex hrex am hv hx hb)

theorem rol_m16_cl_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (Rmw32Pre p am 2 (4 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: 0xD3 :: am.modrm 0 :: am.tail))
      (rolMClA32Effect p (4 + am.tail.length) 16 am) := by
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
  have hstep := rol_m16_cl_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m16_cl_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (Rmw32Pre p am 2 (4 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: 0xD3 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMClA32Effect p (4 + am.tail.length) 16 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMClA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m16_cl_a32_effect_step p am hv hx hb)

theorem rol_m16_cl_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Rmw32Pre p am 2 (5 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: rex :: 0xD3 :: am.modrm 0 :: am.tail))
      (rolMClA32Effect p (5 + am.tail.length) 16 am) := by
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
  have hstep := rol_m16_cl_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m16_cl_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (Rmw32Pre p am 2 (5 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: rex :: 0xD3 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMClA32Effect p (5 + am.tail.length) 16 am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMClA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m16_cl_rex_a32_effect_step p rex hrex am hv hx hb)

theorem rol_m64_cl_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (RmwPre p am 8 (3 + am.tail.length))
      (codeRange p (encodeRolM64Cl am))
      (Effect.post (rolMClEffect p (3 + am.tail.length) 64 am)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact rol_m64_cl_triple_of_bytes p _ hrex am hv hx hb

theorem rol_m32_cl_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (RmwPre p am 4 (encodeRolM32Cl am).length)
      (codeRange p (encodeRolM32Cl am))
      (Effect.post (rolMClEffect p (encodeRolM32Cl am).length 32 am)) := by
  unfold encodeRolM32Cl
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rol_m32_cl_triple_of_bytes p am hv hx hb
    rwa [show (0xD3 :: am.modrm 0 :: am.tail).length =
      2 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rol_m32_cl_rex_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (am.rexByte false 0 ::
      0xD3 :: am.modrm 0 :: am.tail).length =
      3 + am.tail.length by simp; omega]

theorem rol_m16_cl_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (RmwPre p am 2 (encodeRolM16Cl am).length)
      (codeRange p (encodeRolM16Cl am))
      (Effect.post (rolMClEffect p (encodeRolM16Cl am).length 16 am)) := by
  unfold encodeRolM16Cl
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rol_m16_cl_triple_of_bytes p am hv hx hb
    rwa [show (0x66 :: 0xD3 :: am.modrm 0 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rol_m16_cl_rex_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (0x66 :: am.rexByte false 0 ::
      0xD3 :: am.modrm 0 :: am.tail).length =
      4 + am.tail.length by simp; omega]

theorem rol_m64_cl_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegRmwPre p r base am 8 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: encodeRolM64Cl am))
      (Effect.post (rolMClSegEffect p (4 + am.tail.length) 64 base am)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact rol_m64_cl_seg_triple_of_bytes p r base _ hrex am hv hx hb

theorem rol_m32_cl_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegRmwPre p r base am 4 (r.prefixByte :: encodeRolM32Cl am).length)
      (codeRange p (r.prefixByte :: encodeRolM32Cl am))
      (Effect.post (rolMClSegEffect p (r.prefixByte :: encodeRolM32Cl am).length 32 base am)) := by
  unfold encodeRolM32Cl
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rol_m32_cl_seg_triple_of_bytes p r base am hv hx hb
    rwa [show (r.prefixByte :: 0xD3 :: am.modrm 0 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rol_m32_cl_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb
    rwa [show (r.prefixByte :: am.rexByte false 0 ::
      0xD3 :: am.modrm 0 :: am.tail).length =
      4 + am.tail.length by simp; omega]

theorem rol_m16_cl_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegRmwPre p r base am 2 (r.prefixByte :: encodeRolM16Cl am).length)
      (codeRange p (r.prefixByte :: encodeRolM16Cl am))
      (Effect.post (rolMClSegEffect p (r.prefixByte :: encodeRolM16Cl am).length 16 base am)) := by
  unfold encodeRolM16Cl
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rol_m16_cl_seg_triple_of_bytes p r base am hv hx hb
    rwa [show (r.prefixByte :: 0x66 :: 0xD3 :: am.modrm 0 :: am.tail).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rol_m16_cl_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb
    rwa [show (r.prefixByte :: 0x66 :: am.rexByte false 0 ::
      0xD3 :: am.modrm 0 :: am.tail).length =
      5 + am.tail.length by simp; omega]

theorem rol_m64_cl_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (Rmw32Pre p am 8 (4 + am.tail.length))
      (codeRange p (0x67 :: encodeRolM64Cl am))
      (Effect.post (rolMClA32Effect p (4 + am.tail.length) 64 am)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact rol_m64_cl_a32_triple_of_bytes p _ hrex am hv hx hb

theorem rol_m32_cl_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (Rmw32Pre p am 4 (0x67 :: encodeRolM32Cl am).length)
      (codeRange p (0x67 :: encodeRolM32Cl am))
      (Effect.post (rolMClA32Effect p (0x67 :: encodeRolM32Cl am).length 32 am)) := by
  unfold encodeRolM32Cl
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rol_m32_cl_a32_triple_of_bytes p am hv hx hb
    rwa [show (0x67 :: 0xD3 :: am.modrm 0 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rol_m32_cl_rex_a32_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (0x67 :: am.rexByte false 0 ::
      0xD3 :: am.modrm 0 :: am.tail).length =
      4 + am.tail.length by simp; omega]

theorem rol_m16_cl_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (Rmw32Pre p am 2 (0x67 :: encodeRolM16Cl am).length)
      (codeRange p (0x67 :: encodeRolM16Cl am))
      (Effect.post (rolMClA32Effect p (0x67 :: encodeRolM16Cl am).length 16 am)) := by
  unfold encodeRolM16Cl
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rol_m16_cl_a32_triple_of_bytes p am hv hx hb
    rwa [show (0x67 :: 0x66 :: 0xD3 :: am.modrm 0 :: am.tail).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rol_m16_cl_rex_a32_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (0x67 :: 0x66 :: am.rexByte false 0 ::
      0xD3 :: am.modrm 0 :: am.tail).length =
      5 + am.tail.length by simp; omega]

attribute [x86_compose] rolMClEffect

theorem rolMClEffect_local {p : BitVec 64} {len n : Nat} {am : AddrMode}
    (hn : n % 8 = 0) : Effect.Local (rolMClEffect p len n am) :=
  Effect.Local.of_param (e := fun c => rolMEffect p len n am c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => rolMEffect_local hn

@[x86_local] theorem rolMClEffect_local64 {p : BitVec 64} {len : Nat}
    {am : AddrMode} : Effect.Local (rolMClEffect p len 64 am) :=
  rolMClEffect_local (by decide)

@[x86_local] theorem rolMClEffect_local32 {p : BitVec 64} {len : Nat}
    {am : AddrMode} : Effect.Local (rolMClEffect p len 32 am) :=
  rolMClEffect_local (by decide)

@[x86_local] theorem rolMClEffect_local16 {p : BitVec 64} {len : Nat}
    {am : AddrMode} : Effect.Local (rolMClEffect p len 16 am) :=
  rolMClEffect_local (by decide)

@[x86_local] theorem rolMClEffect_local8 {p : BitVec 64} {len : Nat}
    {am : AddrMode} : Effect.Local (rolMClEffect p len 8 am) :=
  rolMClEffect_local (by decide)

attribute [x86_compose] rolMClSegEffect

theorem rolMClSegEffect_local {p : BitVec 64} {len n : Nat} {base : BitVec 64} {am : AddrMode} (hn : n % 8 = 0) :
    Effect.Local (rolMClSegEffect p len n base am) :=
  Effect.Local.of_param (e := fun c => rolMSegEffect p len n base am c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => rolMSegEffect_local hn

@[x86_local] theorem rolMClSegEffect_local64 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} :
    Effect.Local (rolMClSegEffect p len 64 base am) :=
  rolMClSegEffect_local (by decide)

@[x86_local] theorem rolMClSegEffect_local32 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} :
    Effect.Local (rolMClSegEffect p len 32 base am) :=
  rolMClSegEffect_local (by decide)

@[x86_local] theorem rolMClSegEffect_local16 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} :
    Effect.Local (rolMClSegEffect p len 16 base am) :=
  rolMClSegEffect_local (by decide)

@[x86_local] theorem rolMClSegEffect_local8 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} :
    Effect.Local (rolMClSegEffect p len 8 base am) :=
  rolMClSegEffect_local (by decide)

attribute [x86_compose] rolMClA32Effect

theorem rolMClA32Effect_local {p : BitVec 64} {len n : Nat} {am : AddrMode}
    (hn : n % 8 = 0) : Effect.Local (rolMClA32Effect p len n am) :=
  Effect.Local.of_param (e := fun c => rolMA32Effect p len n am c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => rolMA32Effect_local hn

@[x86_local] theorem rolMClA32Effect_local64 {p : BitVec 64} {len : Nat}
    {am : AddrMode} : Effect.Local (rolMClA32Effect p len 64 am) :=
  rolMClA32Effect_local (by decide)

@[x86_local] theorem rolMClA32Effect_local32 {p : BitVec 64} {len : Nat}
    {am : AddrMode} : Effect.Local (rolMClA32Effect p len 32 am) :=
  rolMClA32Effect_local (by decide)

@[x86_local] theorem rolMClA32Effect_local16 {p : BitVec 64} {len : Nat}
    {am : AddrMode} : Effect.Local (rolMClA32Effect p len 16 am) :=
  rolMClA32Effect_local (by decide)

@[x86_local] theorem rolMClA32Effect_local8 {p : BitVec 64} {len : Nat}
    {am : AddrMode} : Effect.Local (rolMClA32Effect p len 8 am) :=
  rolMClA32Effect_local (by decide)

end X86Proofs
