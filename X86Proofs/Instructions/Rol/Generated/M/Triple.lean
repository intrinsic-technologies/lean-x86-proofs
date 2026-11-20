import X86Proofs.Instructions.Rol.Generated.M.Step
import X86Proofs.Instructions.Rol.Generated.M.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def rolMEffect (p : BitVec 64) (len n : Nat) (am : AddrMode) (c : Nat) (s : RamState) :
    Effect :=
  let addr := am.addr s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand n).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem addr : Operand n), a.rotateLeft c⟩]
    flags := some (rolFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[simp] theorem rolMEffect_components (p : BitVec 64) (len n : Nat) (am : AddrMode)
    (c : Nat) (s : RamState) : (rolMEffect p len n am c s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) (n / 8), .flags, .rip] := rfl

def rolMSegEffect (p : BitVec 64) (len n : Nat) (base : BitVec 64) (am : AddrMode) (c : Nat)
    (s : RamState) : Effect :=
  let addr := base + am.addr s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand n).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem addr : Operand n), a.rotateLeft c⟩]
    flags := some (rolFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[simp] theorem rolMSegEffect_components (p : BitVec 64) (len n : Nat) (base : BitVec 64)
    (am : AddrMode) (c : Nat) (s : RamState) :
    (rolMSegEffect p len n base am c s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) (n / 8), .flags, .rip] := rfl

def rolMA32Effect (p : BitVec 64) (len n : Nat) (am : AddrMode) (c : Nat) (s : RamState) :
    Effect :=
  let addr := am.addr32 s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand n).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem addr : Operand n), a.rotateLeft c⟩]
    flags := some (rolFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[simp] theorem rolMA32Effect_components (p : BitVec 64) (len n : Nat) (am : AddrMode)
    (c : Nat) (s : RamState) : (rolMA32Effect p len n am c s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) (n / 8), .flags, .rip] := rfl

theorem rol_m64_imm8_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (RmwPre p am 8 (4 + am.tail.length))
      (codeRange p (rex :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (rolMEffect p (4 + am.tail.length) 64 am
        (shiftCount 64 imm)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := rol_m_imm8_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m64_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (RmwPre p am 8 (4 + am.tail.length))
      (codeRange p (rex :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (rolMEffect p (4 + am.tail.length) 64 am
        (shiftCount 64 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m64_imm8_effect_step p rex hrex am hv hx hb imm)

theorem rol_m32_imm8_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (RmwPre p am 4 (3 + am.tail.length))
      (codeRange p (0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (rolMEffect p (3 + am.tail.length) 32 am
        (shiftCount 32 imm)) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := rol_m_imm8_step s h [] (by simp) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m32_imm8_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (RmwPre p am 4 (3 + am.tail.length))
      (codeRange p (0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (rolMEffect p (3 + am.tail.length) 32 am
        (shiftCount 32 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m32_imm8_effect_step p am hv hx hb imm)

theorem rol_m32_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (RmwPre p am 4 (4 + am.tail.length))
      (codeRange p (rex :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (rolMEffect p (4 + am.tail.length) 32 am
        (shiftCount 32 imm)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := rol_m_imm8_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m32_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (RmwPre p am 4 (4 + am.tail.length))
      (codeRange p (rex :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (rolMEffect p (4 + am.tail.length) 32 am
        (shiftCount 32 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m32_imm8_rex_effect_step p rex hrex am hv hx hb imm)

theorem rol_m16_imm8_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (RmwPre p am 2 (4 + am.tail.length))
      (codeRange p (0x66 :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (rolMEffect p (4 + am.tail.length) 16 am
        (shiftCount 16 imm)) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := rol_m16_imm8_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.osz _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m16_imm8_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (RmwPre p am 2 (4 + am.tail.length))
      (codeRange p (0x66 :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (rolMEffect p (4 + am.tail.length) 16 am
        (shiftCount 16 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m16_imm8_effect_step p am hv hx hb imm)

theorem rol_m16_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (RmwPre p am 2 (5 + am.tail.length))
      (codeRange p (0x66 :: rex :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (rolMEffect p (5 + am.tail.length) 16 am
        (shiftCount 16 imm)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := rol_m16_imm8_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_66_rex _ _ hr]; exact (AddrContext.oszRex _ _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_66_rex _ _ hr]; exact hread)
  simp only [scanContext_66_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m16_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (RmwPre p am 2 (5 + am.tail.length))
      (codeRange p (0x66 :: rex :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (rolMEffect p (5 + am.tail.length) 16 am
        (shiftCount 16 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m16_imm8_rex_effect_step p rex hrex am hv hx hb imm)

theorem rol_m64_imm8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (SegRmwPre p r base am 8 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (rolMSegEffect p (5 + am.tail.length) 64 base am
        (shiftCount 64 imm)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := rol_m_imm8_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m64_imm8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (SegRmwPre p r base am 8 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (rolMSegEffect p (5 + am.tail.length) 64 base am
        (shiftCount 64 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (rol_m64_imm8_seg_effect_step p r base rex hrex am hv hx hb imm)

theorem rol_m32_imm8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (SegRmwPre p r base am 4 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (rolMSegEffect p (4 + am.tail.length) 32 base am
        (shiftCount 32 imm)) := by
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := rol_m_imm8_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m32_imm8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (SegRmwPre p r base am 4 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (rolMSegEffect p (4 + am.tail.length) 32 base am
        (shiftCount 32 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (rol_m32_imm8_seg_effect_step p r base am hv hx hb imm)

theorem rol_m32_imm8_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (SegRmwPre p r base am 4 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (rolMSegEffect p (5 + am.tail.length) 32 base am
        (shiftCount 32 imm)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := rol_m_imm8_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m32_imm8_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (SegRmwPre p r base am 4 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (rolMSegEffect p (5 + am.tail.length) 32 base am
        (shiftCount 32 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (rol_m32_imm8_rex_seg_effect_step p r base rex hrex am hv hx hb imm)

theorem rol_m16_imm8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (SegRmwPre p r base am 2 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (rolMSegEffect p (5 + am.tail.length) 16 base am
        (shiftCount 16 imm)) := by
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66]
      (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := rol_m16_imm8_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m16_imm8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (SegRmwPre p r base am 2 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (rolMSegEffect p (5 + am.tail.length) 16 base am
        (shiftCount 16 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (rol_m16_imm8_seg_effect_step p r base am hv hx hb imm)

theorem rol_m16_imm8_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (SegRmwPre p r base am 2 (6 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (rolMSegEffect p (6 + am.tail.length) 16 base am
        (shiftCount 16 imm)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66, rex] =
      withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66, rex]
      (noSegPrefix_cons noSegPrefix_66 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_66_rex _ _ hr]
  have hstep := rol_m16_imm8_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m16_imm8_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (SegRmwPre p r base am 2 (6 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (rolMSegEffect p (6 + am.tail.length) 16 base am
        (shiftCount 16 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (rol_m16_imm8_rex_seg_effect_step p r base rex hrex am hv hx hb imm)

theorem rol_m64_imm8_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (Rmw32Pre p am 8 (5 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (rolMA32Effect p (5 + am.tail.length) 64 am
        (shiftCount 64 imm)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := rol_m_imm8_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m64_imm8_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (Rmw32Pre p am 8 (5 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (rolMA32Effect p (5 + am.tail.length) 64 am
        (shiftCount 64 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m64_imm8_a32_effect_step p rex hrex am hv hx hb imm)

theorem rol_m32_imm8_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (Rmw32Pre p am 4 (4 + am.tail.length))
      (codeRange p (0x67 :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (rolMA32Effect p (4 + am.tail.length) 32 am
        (shiftCount 32 imm)) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := rol_m_imm8_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m32_imm8_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (Rmw32Pre p am 4 (4 + am.tail.length))
      (codeRange p (0x67 :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (rolMA32Effect p (4 + am.tail.length) 32 am
        (shiftCount 32 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m32_imm8_a32_effect_step p am hv hx hb imm)

theorem rol_m32_imm8_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (Rmw32Pre p am 4 (5 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (rolMA32Effect p (5 + am.tail.length) 32 am
        (shiftCount 32 imm)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := rol_m_imm8_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m32_imm8_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (Rmw32Pre p am 4 (5 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (rolMA32Effect p (5 + am.tail.length) 32 am
        (shiftCount 32 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m32_imm8_rex_a32_effect_step p rex hrex am hv hx hb imm)

theorem rol_m16_imm8_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (Rmw32Pre p am 2 (5 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (rolMA32Effect p (5 + am.tail.length) 16 am
        (shiftCount 16 imm)) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66]) := by
    rw [scanContext_asz_cons]
  have hstep := rol_m16_imm8_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m16_imm8_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (Rmw32Pre p am 2 (5 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (rolMA32Effect p (5 + am.tail.length) 16 am
        (shiftCount 16 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m16_imm8_a32_effect_step p am hv hx hb imm)

theorem rol_m16_imm8_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (Rmw32Pre p am 2 (6 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: rex :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (rolMA32Effect p (6 + am.tail.length) 16 am
        (shiftCount 16 imm)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, rex] =
      withAsz (oszRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_66_rex _ _ hr]
  have hstep := rol_m16_imm8_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · apply rolFlags_allows

theorem rol_m16_imm8_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (Rmw32Pre p am 2 (6 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: rex :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (rolMA32Effect p (6 + am.tail.length) 16 am
        (shiftCount 16 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m16_imm8_rex_a32_effect_step p rex hrex am hv hx hb imm)

theorem rol_m64_imm8_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 8) :
    Triple (RmwPre p am 8 (4 + am.tail.length))
      (codeRange p (encodeRolM64Imm8 am imm))
      (Effect.post (rolMEffect p (4 + am.tail.length) 64 am
        (shiftCount 64 imm))) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact rol_m64_imm8_triple_of_bytes p _ hrex am hv hx hb imm

theorem rol_m32_imm8_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 8) :
    Triple (RmwPre p am 4 (encodeRolM32Imm8 am imm).length)
      (codeRange p (encodeRolM32Imm8 am imm))
      (Effect.post (rolMEffect p (encodeRolM32Imm8 am imm).length 32 am
        (shiftCount 32 imm))) := by
  unfold encodeRolM32Imm8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rol_m32_imm8_triple_of_bytes p am hv hx hb imm
    rwa [show (0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rol_m32_imm8_rex_triple_of_bytes p _ hrex am hv hx hb imm
    rwa [show (am.rexByte false 0 ::
      0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)).length =
      4 + am.tail.length by simp; omega]

theorem rol_m16_imm8_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 8) :
    Triple (RmwPre p am 2 (encodeRolM16Imm8 am imm).length)
      (codeRange p (encodeRolM16Imm8 am imm))
      (Effect.post (rolMEffect p (encodeRolM16Imm8 am imm).length 16 am
        (shiftCount 16 imm))) := by
  unfold encodeRolM16Imm8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rol_m16_imm8_triple_of_bytes p am hv hx hb imm
    rwa [show (0x66 :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rol_m16_imm8_rex_triple_of_bytes p _ hrex am hv hx hb imm
    rwa [show (0x66 :: am.rexByte false 0 ::
      0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)).length =
      5 + am.tail.length by simp; omega]

theorem rol_m64_imm8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (imm : BitVec 8) :
    Triple (SegRmwPre p r base am 8 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: encodeRolM64Imm8 am imm))
      (Effect.post (rolMSegEffect p (5 + am.tail.length) 64 base am
        (shiftCount 64 imm))) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact rol_m64_imm8_seg_triple_of_bytes p r base _ hrex am hv hx hb imm

theorem rol_m32_imm8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (imm : BitVec 8) :
    Triple (SegRmwPre p r base am 4 (r.prefixByte :: encodeRolM32Imm8 am imm).length)
      (codeRange p (r.prefixByte :: encodeRolM32Imm8 am imm))
      (Effect.post (rolMSegEffect p (r.prefixByte :: encodeRolM32Imm8 am imm).length 32 base am
        (shiftCount 32 imm))) := by
  unfold encodeRolM32Imm8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rol_m32_imm8_seg_triple_of_bytes p r base am hv hx hb imm
    rwa [show (r.prefixByte :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rol_m32_imm8_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb imm
    rwa [show (r.prefixByte :: am.rexByte false 0 ::
      0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)).length =
      5 + am.tail.length by simp; omega]

theorem rol_m16_imm8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (imm : BitVec 8) :
    Triple (SegRmwPre p r base am 2 (r.prefixByte :: encodeRolM16Imm8 am imm).length)
      (codeRange p (r.prefixByte :: encodeRolM16Imm8 am imm))
      (Effect.post (rolMSegEffect p (r.prefixByte :: encodeRolM16Imm8 am imm).length 16 base am
        (shiftCount 16 imm))) := by
  unfold encodeRolM16Imm8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rol_m16_imm8_seg_triple_of_bytes p r base am hv hx hb imm
    rwa [show (r.prefixByte :: 0x66 :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)).length =
      5 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rol_m16_imm8_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb imm
    rwa [show (r.prefixByte :: 0x66 :: am.rexByte false 0 ::
      0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)).length =
      6 + am.tail.length by simp; omega]

theorem rol_m64_imm8_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 8) :
    Triple (Rmw32Pre p am 8 (5 + am.tail.length))
      (codeRange p (0x67 :: encodeRolM64Imm8 am imm))
      (Effect.post (rolMA32Effect p (5 + am.tail.length) 64 am
        (shiftCount 64 imm))) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact rol_m64_imm8_a32_triple_of_bytes p _ hrex am hv hx hb imm

theorem rol_m32_imm8_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 8) :
    Triple (Rmw32Pre p am 4 (0x67 :: encodeRolM32Imm8 am imm).length)
      (codeRange p (0x67 :: encodeRolM32Imm8 am imm))
      (Effect.post (rolMA32Effect p (0x67 :: encodeRolM32Imm8 am imm).length 32 am
        (shiftCount 32 imm))) := by
  unfold encodeRolM32Imm8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rol_m32_imm8_a32_triple_of_bytes p am hv hx hb imm
    rwa [show (0x67 :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rol_m32_imm8_rex_a32_triple_of_bytes p _ hrex am hv hx hb imm
    rwa [show (0x67 :: am.rexByte false 0 ::
      0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)).length =
      5 + am.tail.length by simp; omega]

theorem rol_m16_imm8_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 8) :
    Triple (Rmw32Pre p am 2 (0x67 :: encodeRolM16Imm8 am imm).length)
      (codeRange p (0x67 :: encodeRolM16Imm8 am imm))
      (Effect.post (rolMA32Effect p (0x67 :: encodeRolM16Imm8 am imm).length 16 am
        (shiftCount 16 imm))) := by
  unfold encodeRolM16Imm8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rol_m16_imm8_a32_triple_of_bytes p am hv hx hb imm
    rwa [show (0x67 :: 0x66 :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)).length =
      5 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rol_m16_imm8_rex_a32_triple_of_bytes p _ hrex am hv hx hb imm
    rwa [show (0x67 :: 0x66 :: am.rexByte false 0 ::
      0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)).length =
      6 + am.tail.length by simp; omega]

theorem rol_m64_one_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 8 (3 + am.tail.length))
      (codeRange p (rex :: 0xD1 :: am.modrm 0 :: am.tail))
      (rolMEffect p (3 + am.tail.length) 64 am 1) := by
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
  have hstep := rol_m_one_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
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

theorem rol_m64_one_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 8 (3 + am.tail.length))
      (codeRange p (rex :: 0xD1 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMEffect p (3 + am.tail.length) 64 am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m64_one_effect_step p rex hrex am hv hx hb)

theorem rol_m32_one_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (RmwPre p am 4 (2 + am.tail.length))
      (codeRange p (0xD1 :: am.modrm 0 :: am.tail))
      (rolMEffect p (2 + am.tail.length) 32 am 1) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := rol_m_one_step s h [] (by simp) (by simp) 32 (.inr rfl)
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

theorem rol_m32_one_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (RmwPre p am 4 (2 + am.tail.length))
      (codeRange p (0xD1 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMEffect p (2 + am.tail.length) 32 am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m32_one_effect_step p am hv hx hb)

theorem rol_m32_one_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 4 (3 + am.tail.length))
      (codeRange p (rex :: 0xD1 :: am.modrm 0 :: am.tail))
      (rolMEffect p (3 + am.tail.length) 32 am 1) := by
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
  have hstep := rol_m_one_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
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

theorem rol_m32_one_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 4 (3 + am.tail.length))
      (codeRange p (rex :: 0xD1 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMEffect p (3 + am.tail.length) 32 am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m32_one_rex_effect_step p rex hrex am hv hx hb)

theorem rol_m16_one_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (RmwPre p am 2 (3 + am.tail.length))
      (codeRange p (0x66 :: 0xD1 :: am.modrm 0 :: am.tail))
      (rolMEffect p (3 + am.tail.length) 16 am 1) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := rol_m16_one_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
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

theorem rol_m16_one_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (RmwPre p am 2 (3 + am.tail.length))
      (codeRange p (0x66 :: 0xD1 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMEffect p (3 + am.tail.length) 16 am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m16_one_effect_step p am hv hx hb)

theorem rol_m16_one_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 2 (4 + am.tail.length))
      (codeRange p (0x66 :: rex :: 0xD1 :: am.modrm 0 :: am.tail))
      (rolMEffect p (4 + am.tail.length) 16 am 1) := by
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
  have hstep := rol_m16_one_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
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

theorem rol_m16_one_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 2 (4 + am.tail.length))
      (codeRange p (0x66 :: rex :: 0xD1 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMEffect p (4 + am.tail.length) 16 am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m16_one_rex_effect_step p rex hrex am hv hx hb)

theorem rol_m64_one_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegRmwPre p r base am 8 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xD1 :: am.modrm 0 :: am.tail))
      (rolMSegEffect p (4 + am.tail.length) 64 base am 1) := by
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
  have hstep := rol_m_one_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
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

theorem rol_m64_one_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegRmwPre p r base am 8 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xD1 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMSegEffect p (4 + am.tail.length) 64 base am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (rol_m64_one_seg_effect_step p r base rex hrex am hv hx hb)

theorem rol_m32_one_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (SegRmwPre p r base am 4 (3 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xD1 :: am.modrm 0 :: am.tail))
      (rolMSegEffect p (3 + am.tail.length) 32 base am 1) := by
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
  have hstep := rol_m_one_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp) 32 (.inr rfl)
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

theorem rol_m32_one_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (SegRmwPre p r base am 4 (3 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xD1 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMSegEffect p (3 + am.tail.length) 32 base am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (rol_m32_one_seg_effect_step p r base am hv hx hb)

theorem rol_m32_one_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegRmwPre p r base am 4 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xD1 :: am.modrm 0 :: am.tail))
      (rolMSegEffect p (4 + am.tail.length) 32 base am 1) := by
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
  have hstep := rol_m_one_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
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

theorem rol_m32_one_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegRmwPre p r base am 4 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xD1 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMSegEffect p (4 + am.tail.length) 32 base am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (rol_m32_one_rex_seg_effect_step p r base rex hrex am hv hx hb)

theorem rol_m16_one_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (SegRmwPre p r base am 2 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: 0xD1 :: am.modrm 0 :: am.tail))
      (rolMSegEffect p (4 + am.tail.length) 16 base am 1) := by
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
  have hstep := rol_m16_one_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
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

theorem rol_m16_one_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (SegRmwPre p r base am 2 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: 0xD1 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMSegEffect p (4 + am.tail.length) 16 base am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (rol_m16_one_seg_effect_step p r base am hv hx hb)

theorem rol_m16_one_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegRmwPre p r base am 2 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0xD1 :: am.modrm 0 :: am.tail))
      (rolMSegEffect p (5 + am.tail.length) 16 base am 1) := by
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
  have hstep := rol_m16_one_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
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

theorem rol_m16_one_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegRmwPre p r base am 2 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0xD1 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMSegEffect p (5 + am.tail.length) 16 base am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (rol_m16_one_rex_seg_effect_step p r base rex hrex am hv hx hb)

theorem rol_m64_one_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Rmw32Pre p am 8 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xD1 :: am.modrm 0 :: am.tail))
      (rolMA32Effect p (4 + am.tail.length) 64 am 1) := by
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
  have hstep := rol_m_one_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
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

theorem rol_m64_one_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (Rmw32Pre p am 8 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xD1 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMA32Effect p (4 + am.tail.length) 64 am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m64_one_a32_effect_step p rex hrex am hv hx hb)

theorem rol_m32_one_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (Rmw32Pre p am 4 (3 + am.tail.length))
      (codeRange p (0x67 :: 0xD1 :: am.modrm 0 :: am.tail))
      (rolMA32Effect p (3 + am.tail.length) 32 am 1) := by
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
  have hstep := rol_m_one_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp) 32 (.inr rfl)
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

theorem rol_m32_one_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (Rmw32Pre p am 4 (3 + am.tail.length))
      (codeRange p (0x67 :: 0xD1 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMA32Effect p (3 + am.tail.length) 32 am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m32_one_a32_effect_step p am hv hx hb)

theorem rol_m32_one_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Rmw32Pre p am 4 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xD1 :: am.modrm 0 :: am.tail))
      (rolMA32Effect p (4 + am.tail.length) 32 am 1) := by
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
  have hstep := rol_m_one_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
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

theorem rol_m32_one_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (Rmw32Pre p am 4 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xD1 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMA32Effect p (4 + am.tail.length) 32 am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m32_one_rex_a32_effect_step p rex hrex am hv hx hb)

theorem rol_m16_one_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (Rmw32Pre p am 2 (4 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: 0xD1 :: am.modrm 0 :: am.tail))
      (rolMA32Effect p (4 + am.tail.length) 16 am 1) := by
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
  have hstep := rol_m16_one_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
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

theorem rol_m16_one_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (Rmw32Pre p am 2 (4 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: 0xD1 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMA32Effect p (4 + am.tail.length) 16 am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m16_one_a32_effect_step p am hv hx hb)

theorem rol_m16_one_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Rmw32Pre p am 2 (5 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: rex :: 0xD1 :: am.modrm 0 :: am.tail))
      (rolMA32Effect p (5 + am.tail.length) 16 am 1) := by
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
  have hstep := rol_m16_one_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
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

theorem rol_m16_one_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (Rmw32Pre p am 2 (5 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: rex :: 0xD1 :: am.modrm 0 :: am.tail))
      (Effect.post (rolMA32Effect p (5 + am.tail.length) 16 am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rolMA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (rol_m16_one_rex_a32_effect_step p rex hrex am hv hx hb)

theorem rol_m64_one_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (RmwPre p am 8 (3 + am.tail.length))
      (codeRange p (encodeRolM64One am))
      (Effect.post (rolMEffect p (3 + am.tail.length) 64 am 1)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact rol_m64_one_triple_of_bytes p _ hrex am hv hx hb

theorem rol_m32_one_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (RmwPre p am 4 (encodeRolM32One am).length)
      (codeRange p (encodeRolM32One am))
      (Effect.post (rolMEffect p (encodeRolM32One am).length 32 am 1)) := by
  unfold encodeRolM32One
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rol_m32_one_triple_of_bytes p am hv hx hb
    rwa [show (0xD1 :: am.modrm 0 :: am.tail).length =
      2 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rol_m32_one_rex_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (am.rexByte false 0 ::
      0xD1 :: am.modrm 0 :: am.tail).length =
      3 + am.tail.length by simp; omega]

theorem rol_m16_one_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (RmwPre p am 2 (encodeRolM16One am).length)
      (codeRange p (encodeRolM16One am))
      (Effect.post (rolMEffect p (encodeRolM16One am).length 16 am 1)) := by
  unfold encodeRolM16One
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rol_m16_one_triple_of_bytes p am hv hx hb
    rwa [show (0x66 :: 0xD1 :: am.modrm 0 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rol_m16_one_rex_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (0x66 :: am.rexByte false 0 ::
      0xD1 :: am.modrm 0 :: am.tail).length =
      4 + am.tail.length by simp; omega]

theorem rol_m64_one_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegRmwPre p r base am 8 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: encodeRolM64One am))
      (Effect.post (rolMSegEffect p (4 + am.tail.length) 64 base am 1)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact rol_m64_one_seg_triple_of_bytes p r base _ hrex am hv hx hb

theorem rol_m32_one_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegRmwPre p r base am 4 (r.prefixByte :: encodeRolM32One am).length)
      (codeRange p (r.prefixByte :: encodeRolM32One am))
      (Effect.post (rolMSegEffect p (r.prefixByte :: encodeRolM32One am).length 32 base am 1)) := by
  unfold encodeRolM32One
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rol_m32_one_seg_triple_of_bytes p r base am hv hx hb
    rwa [show (r.prefixByte :: 0xD1 :: am.modrm 0 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rol_m32_one_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb
    rwa [show (r.prefixByte :: am.rexByte false 0 ::
      0xD1 :: am.modrm 0 :: am.tail).length =
      4 + am.tail.length by simp; omega]

theorem rol_m16_one_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegRmwPre p r base am 2 (r.prefixByte :: encodeRolM16One am).length)
      (codeRange p (r.prefixByte :: encodeRolM16One am))
      (Effect.post (rolMSegEffect p (r.prefixByte :: encodeRolM16One am).length 16 base am 1)) := by
  unfold encodeRolM16One
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rol_m16_one_seg_triple_of_bytes p r base am hv hx hb
    rwa [show (r.prefixByte :: 0x66 :: 0xD1 :: am.modrm 0 :: am.tail).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rol_m16_one_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb
    rwa [show (r.prefixByte :: 0x66 :: am.rexByte false 0 ::
      0xD1 :: am.modrm 0 :: am.tail).length =
      5 + am.tail.length by simp; omega]

theorem rol_m64_one_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (Rmw32Pre p am 8 (4 + am.tail.length))
      (codeRange p (0x67 :: encodeRolM64One am))
      (Effect.post (rolMA32Effect p (4 + am.tail.length) 64 am 1)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact rol_m64_one_a32_triple_of_bytes p _ hrex am hv hx hb

theorem rol_m32_one_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (Rmw32Pre p am 4 (0x67 :: encodeRolM32One am).length)
      (codeRange p (0x67 :: encodeRolM32One am))
      (Effect.post (rolMA32Effect p (0x67 :: encodeRolM32One am).length 32 am 1)) := by
  unfold encodeRolM32One
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rol_m32_one_a32_triple_of_bytes p am hv hx hb
    rwa [show (0x67 :: 0xD1 :: am.modrm 0 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rol_m32_one_rex_a32_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (0x67 :: am.rexByte false 0 ::
      0xD1 :: am.modrm 0 :: am.tail).length =
      4 + am.tail.length by simp; omega]

theorem rol_m16_one_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (Rmw32Pre p am 2 (0x67 :: encodeRolM16One am).length)
      (codeRange p (0x67 :: encodeRolM16One am))
      (Effect.post (rolMA32Effect p (0x67 :: encodeRolM16One am).length 16 am 1)) := by
  unfold encodeRolM16One
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rol_m16_one_a32_triple_of_bytes p am hv hx hb
    rwa [show (0x67 :: 0x66 :: 0xD1 :: am.modrm 0 :: am.tail).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rol_m16_one_rex_a32_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (0x67 :: 0x66 :: am.rexByte false 0 ::
      0xD1 :: am.modrm 0 :: am.tail).length =
      5 + am.tail.length by simp; omega]

attribute [x86_compose] rolMEffect

theorem rolMEffect_local {p : BitVec 64} {len n : Nat} {am : AddrMode} {c : Nat}
    (hn : n % 8 = 0) :
    Effect.Local (rolMEffect p len n am c) := by
  effect_local [rolMEffect, rolFlags, hn]

@[x86_local] theorem rolMEffect_local64 {p : BitVec 64} {len : Nat} {am : AddrMode}
    {c : Nat} : Effect.Local (rolMEffect p len 64 am c) :=
  rolMEffect_local (by decide)

@[x86_local] theorem rolMEffect_local32 {p : BitVec 64} {len : Nat} {am : AddrMode}
    {c : Nat} : Effect.Local (rolMEffect p len 32 am c) :=
  rolMEffect_local (by decide)

@[x86_local] theorem rolMEffect_local16 {p : BitVec 64} {len : Nat} {am : AddrMode}
    {c : Nat} : Effect.Local (rolMEffect p len 16 am c) :=
  rolMEffect_local (by decide)

@[x86_local] theorem rolMEffect_local8 {p : BitVec 64} {len : Nat} {am : AddrMode}
    {c : Nat} : Effect.Local (rolMEffect p len 8 am c) :=
  rolMEffect_local (by decide)

attribute [x86_compose] rolMSegEffect

theorem rolMSegEffect_local {p : BitVec 64} {len n : Nat} {base : BitVec 64} {am : AddrMode} {c : Nat}
    (hn : n % 8 = 0) :
    Effect.Local (rolMSegEffect p len n base am c) := by
  effect_local [rolMSegEffect, rolFlags, hn]

@[x86_local] theorem rolMSegEffect_local64 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {c : Nat} :
    Effect.Local (rolMSegEffect p len 64 base am c) :=
  rolMSegEffect_local (by decide)

@[x86_local] theorem rolMSegEffect_local32 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {c : Nat} :
    Effect.Local (rolMSegEffect p len 32 base am c) :=
  rolMSegEffect_local (by decide)

@[x86_local] theorem rolMSegEffect_local16 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {c : Nat} :
    Effect.Local (rolMSegEffect p len 16 base am c) :=
  rolMSegEffect_local (by decide)

@[x86_local] theorem rolMSegEffect_local8 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {c : Nat} :
    Effect.Local (rolMSegEffect p len 8 base am c) :=
  rolMSegEffect_local (by decide)

attribute [x86_compose] rolMA32Effect

theorem rolMA32Effect_local {p : BitVec 64} {len n : Nat} {am : AddrMode} {c : Nat}
    (hn : n % 8 = 0) :
    Effect.Local (rolMA32Effect p len n am c) := by
  effect_local [rolMA32Effect, rolFlags, hn]

@[x86_local] theorem rolMA32Effect_local64 {p : BitVec 64} {len : Nat} {am : AddrMode}
    {c : Nat} : Effect.Local (rolMA32Effect p len 64 am c) :=
  rolMA32Effect_local (by decide)

@[x86_local] theorem rolMA32Effect_local32 {p : BitVec 64} {len : Nat} {am : AddrMode}
    {c : Nat} : Effect.Local (rolMA32Effect p len 32 am c) :=
  rolMA32Effect_local (by decide)

@[x86_local] theorem rolMA32Effect_local16 {p : BitVec 64} {len : Nat} {am : AddrMode}
    {c : Nat} : Effect.Local (rolMA32Effect p len 16 am c) :=
  rolMA32Effect_local (by decide)

@[x86_local] theorem rolMA32Effect_local8 {p : BitVec 64} {len : Nat} {am : AddrMode}
    {c : Nat} : Effect.Local (rolMA32Effect p len 8 am c) :=
  rolMA32Effect_local (by decide)

end X86Proofs
