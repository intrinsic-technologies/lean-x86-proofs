import X86Proofs.Instructions.Sal.Generated.M.Step
import X86Proofs.Instructions.Sal.Generated.M.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def salMEffect (p : BitVec 64) (len n : Nat) (am : AddrMode) (c : Nat) (s : RamState) :
    Effect :=
  let addr := am.addr s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand n).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem addr : Operand n), a <<< c⟩]
    flags := some (shlFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[simp] theorem salMEffect_components (p : BitVec 64) (len n : Nat) (am : AddrMode)
    (c : Nat) (s : RamState) : (salMEffect p len n am c s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) (n / 8), .flags, .rip] := rfl

def salMSegEffect (p : BitVec 64) (len n : Nat) (base : BitVec 64) (am : AddrMode) (c : Nat)
    (s : RamState) : Effect :=
  let addr := base + am.addr s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand n).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem addr : Operand n), a <<< c⟩]
    flags := some (shlFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[simp] theorem salMSegEffect_components (p : BitVec 64) (len n : Nat) (base : BitVec 64)
    (am : AddrMode) (c : Nat) (s : RamState) :
    (salMSegEffect p len n base am c s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) (n / 8), .flags, .rip] := rfl

def salMA32Effect (p : BitVec 64) (len n : Nat) (am : AddrMode) (c : Nat) (s : RamState) :
    Effect :=
  let addr := am.addr32 s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand n).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem addr : Operand n), a <<< c⟩]
    flags := some (shlFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[simp] theorem salMA32Effect_components (p : BitVec 64) (len n : Nat) (am : AddrMode)
    (c : Nat) (s : RamState) : (salMA32Effect p len n am c s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) (n / 8), .flags, .rip] := rfl

theorem sal_m64_imm8_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (RmwPre p am 8 (4 + am.tail.length))
      (codeRange p (rex :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (salMEffect p (4 + am.tail.length) 64 am
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
  have hstep := sal_m_imm8_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
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
  · apply shlFlags_allows

theorem sal_m64_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (RmwPre p am 8 (4 + am.tail.length))
      (codeRange p (rex :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (salMEffect p (4 + am.tail.length) 64 am
        (shiftCount 64 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (sal_m64_imm8_effect_step p rex hrex am hv hx hb imm)

theorem sal_m32_imm8_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (RmwPre p am 4 (3 + am.tail.length))
      (codeRange p (0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (salMEffect p (3 + am.tail.length) 32 am
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
  have hstep := sal_m_imm8_step s h [] (by simp) (by simp) 32 (.inr rfl)
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
  · apply shlFlags_allows

theorem sal_m32_imm8_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (RmwPre p am 4 (3 + am.tail.length))
      (codeRange p (0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (salMEffect p (3 + am.tail.length) 32 am
        (shiftCount 32 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (sal_m32_imm8_effect_step p am hv hx hb imm)

theorem sal_m32_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (RmwPre p am 4 (4 + am.tail.length))
      (codeRange p (rex :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (salMEffect p (4 + am.tail.length) 32 am
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
  have hstep := sal_m_imm8_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
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
  · apply shlFlags_allows

theorem sal_m32_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (RmwPre p am 4 (4 + am.tail.length))
      (codeRange p (rex :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (salMEffect p (4 + am.tail.length) 32 am
        (shiftCount 32 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (sal_m32_imm8_rex_effect_step p rex hrex am hv hx hb imm)

theorem sal_m16_imm8_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (RmwPre p am 2 (4 + am.tail.length))
      (codeRange p (0x66 :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (salMEffect p (4 + am.tail.length) 16 am
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
  have hstep := sal_m16_imm8_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
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
  · apply shlFlags_allows

theorem sal_m16_imm8_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (RmwPre p am 2 (4 + am.tail.length))
      (codeRange p (0x66 :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (salMEffect p (4 + am.tail.length) 16 am
        (shiftCount 16 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (sal_m16_imm8_effect_step p am hv hx hb imm)

theorem sal_m16_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (RmwPre p am 2 (5 + am.tail.length))
      (codeRange p (0x66 :: rex :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (salMEffect p (5 + am.tail.length) 16 am
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
  have hstep := sal_m16_imm8_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
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
  · apply shlFlags_allows

theorem sal_m16_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (RmwPre p am 2 (5 + am.tail.length))
      (codeRange p (0x66 :: rex :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (salMEffect p (5 + am.tail.length) 16 am
        (shiftCount 16 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (sal_m16_imm8_rex_effect_step p rex hrex am hv hx hb imm)

theorem sal_m64_imm8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (SegRmwPre p r base am 8 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (salMSegEffect p (5 + am.tail.length) 64 base am
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
  have hstep := sal_m_imm8_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
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
  · apply shlFlags_allows

theorem sal_m64_imm8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (SegRmwPre p r base am 8 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (salMSegEffect p (5 + am.tail.length) 64 base am
        (shiftCount 64 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (sal_m64_imm8_seg_effect_step p r base rex hrex am hv hx hb imm)

theorem sal_m32_imm8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (SegRmwPre p r base am 4 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (salMSegEffect p (4 + am.tail.length) 32 base am
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
  have hstep := sal_m_imm8_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp) 32 (.inr rfl)
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
  · apply shlFlags_allows

theorem sal_m32_imm8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (SegRmwPre p r base am 4 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (salMSegEffect p (4 + am.tail.length) 32 base am
        (shiftCount 32 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (sal_m32_imm8_seg_effect_step p r base am hv hx hb imm)

theorem sal_m32_imm8_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (SegRmwPre p r base am 4 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (salMSegEffect p (5 + am.tail.length) 32 base am
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
  have hstep := sal_m_imm8_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
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
  · apply shlFlags_allows

theorem sal_m32_imm8_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (SegRmwPre p r base am 4 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (salMSegEffect p (5 + am.tail.length) 32 base am
        (shiftCount 32 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (sal_m32_imm8_rex_seg_effect_step p r base rex hrex am hv hx hb imm)

theorem sal_m16_imm8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (SegRmwPre p r base am 2 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (salMSegEffect p (5 + am.tail.length) 16 base am
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
  have hstep := sal_m16_imm8_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
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
  · apply shlFlags_allows

theorem sal_m16_imm8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (SegRmwPre p r base am 2 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (salMSegEffect p (5 + am.tail.length) 16 base am
        (shiftCount 16 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (sal_m16_imm8_seg_effect_step p r base am hv hx hb imm)

theorem sal_m16_imm8_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (SegRmwPre p r base am 2 (6 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (salMSegEffect p (6 + am.tail.length) 16 base am
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
  have hstep := sal_m16_imm8_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
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
  · apply shlFlags_allows

theorem sal_m16_imm8_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (SegRmwPre p r base am 2 (6 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (salMSegEffect p (6 + am.tail.length) 16 base am
        (shiftCount 16 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (sal_m16_imm8_rex_seg_effect_step p r base rex hrex am hv hx hb imm)

theorem sal_m64_imm8_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (Rmw32Pre p am 8 (5 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (salMA32Effect p (5 + am.tail.length) 64 am
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
  have hstep := sal_m_imm8_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
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
  · apply shlFlags_allows

theorem sal_m64_imm8_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (Rmw32Pre p am 8 (5 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (salMA32Effect p (5 + am.tail.length) 64 am
        (shiftCount 64 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (sal_m64_imm8_a32_effect_step p rex hrex am hv hx hb imm)

theorem sal_m32_imm8_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (Rmw32Pre p am 4 (4 + am.tail.length))
      (codeRange p (0x67 :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (salMA32Effect p (4 + am.tail.length) 32 am
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
  have hstep := sal_m_imm8_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp) 32 (.inr rfl)
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
  · apply shlFlags_allows

theorem sal_m32_imm8_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (Rmw32Pre p am 4 (4 + am.tail.length))
      (codeRange p (0x67 :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (salMA32Effect p (4 + am.tail.length) 32 am
        (shiftCount 32 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (sal_m32_imm8_a32_effect_step p am hv hx hb imm)

theorem sal_m32_imm8_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (Rmw32Pre p am 4 (5 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (salMA32Effect p (5 + am.tail.length) 32 am
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
  have hstep := sal_m_imm8_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
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
  · apply shlFlags_allows

theorem sal_m32_imm8_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (Rmw32Pre p am 4 (5 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (salMA32Effect p (5 + am.tail.length) 32 am
        (shiftCount 32 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (sal_m32_imm8_rex_a32_effect_step p rex hrex am hv hx hb imm)

theorem sal_m16_imm8_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (Rmw32Pre p am 2 (5 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (salMA32Effect p (5 + am.tail.length) 16 am
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
  have hstep := sal_m16_imm8_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
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
  · apply shlFlags_allows

theorem sal_m16_imm8_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (Rmw32Pre p am 2 (5 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (salMA32Effect p (5 + am.tail.length) 16 am
        (shiftCount 16 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (sal_m16_imm8_a32_effect_step p am hv hx hb imm)

theorem sal_m16_imm8_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (Rmw32Pre p am 2 (6 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: rex :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (salMA32Effect p (6 + am.tail.length) 16 am
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
  have hstep := sal_m16_imm8_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
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
  · apply shlFlags_allows

theorem sal_m16_imm8_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (Rmw32Pre p am 2 (6 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: rex :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (salMA32Effect p (6 + am.tail.length) 16 am
        (shiftCount 16 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (sal_m16_imm8_rex_a32_effect_step p rex hrex am hv hx hb imm)

theorem sal_m64_imm8_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 8) :
    Triple (RmwPre p am 8 (4 + am.tail.length))
      (codeRange p (encodeSalM64Imm8 am imm))
      (Effect.post (salMEffect p (4 + am.tail.length) 64 am
        (shiftCount 64 imm))) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact sal_m64_imm8_triple_of_bytes p _ hrex am hv hx hb imm

theorem sal_m32_imm8_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 8) :
    Triple (RmwPre p am 4 (encodeSalM32Imm8 am imm).length)
      (codeRange p (encodeSalM32Imm8 am imm))
      (Effect.post (salMEffect p (encodeSalM32Imm8 am imm).length 32 am
        (shiftCount 32 imm))) := by
  unfold encodeSalM32Imm8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := sal_m32_imm8_triple_of_bytes p am hv hx hb imm
    rwa [show (0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := sal_m32_imm8_rex_triple_of_bytes p _ hrex am hv hx hb imm
    rwa [show (am.rexByte false 0 ::
      0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)).length =
      4 + am.tail.length by simp; omega]

theorem sal_m16_imm8_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 8) :
    Triple (RmwPre p am 2 (encodeSalM16Imm8 am imm).length)
      (codeRange p (encodeSalM16Imm8 am imm))
      (Effect.post (salMEffect p (encodeSalM16Imm8 am imm).length 16 am
        (shiftCount 16 imm))) := by
  unfold encodeSalM16Imm8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := sal_m16_imm8_triple_of_bytes p am hv hx hb imm
    rwa [show (0x66 :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := sal_m16_imm8_rex_triple_of_bytes p _ hrex am hv hx hb imm
    rwa [show (0x66 :: am.rexByte false 0 ::
      0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)).length =
      5 + am.tail.length by simp; omega]

theorem sal_m64_imm8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (imm : BitVec 8) :
    Triple (SegRmwPre p r base am 8 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: encodeSalM64Imm8 am imm))
      (Effect.post (salMSegEffect p (5 + am.tail.length) 64 base am
        (shiftCount 64 imm))) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact sal_m64_imm8_seg_triple_of_bytes p r base _ hrex am hv hx hb imm

theorem sal_m32_imm8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (imm : BitVec 8) :
    Triple (SegRmwPre p r base am 4 (r.prefixByte :: encodeSalM32Imm8 am imm).length)
      (codeRange p (r.prefixByte :: encodeSalM32Imm8 am imm))
      (Effect.post (salMSegEffect p (r.prefixByte :: encodeSalM32Imm8 am imm).length 32 base am
        (shiftCount 32 imm))) := by
  unfold encodeSalM32Imm8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := sal_m32_imm8_seg_triple_of_bytes p r base am hv hx hb imm
    rwa [show (r.prefixByte :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := sal_m32_imm8_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb imm
    rwa [show (r.prefixByte :: am.rexByte false 0 ::
      0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)).length =
      5 + am.tail.length by simp; omega]

theorem sal_m16_imm8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (imm : BitVec 8) :
    Triple (SegRmwPre p r base am 2 (r.prefixByte :: encodeSalM16Imm8 am imm).length)
      (codeRange p (r.prefixByte :: encodeSalM16Imm8 am imm))
      (Effect.post (salMSegEffect p (r.prefixByte :: encodeSalM16Imm8 am imm).length 16 base am
        (shiftCount 16 imm))) := by
  unfold encodeSalM16Imm8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := sal_m16_imm8_seg_triple_of_bytes p r base am hv hx hb imm
    rwa [show (r.prefixByte :: 0x66 :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)).length =
      5 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := sal_m16_imm8_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb imm
    rwa [show (r.prefixByte :: 0x66 :: am.rexByte false 0 ::
      0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)).length =
      6 + am.tail.length by simp; omega]

theorem sal_m64_imm8_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 8) :
    Triple (Rmw32Pre p am 8 (5 + am.tail.length))
      (codeRange p (0x67 :: encodeSalM64Imm8 am imm))
      (Effect.post (salMA32Effect p (5 + am.tail.length) 64 am
        (shiftCount 64 imm))) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact sal_m64_imm8_a32_triple_of_bytes p _ hrex am hv hx hb imm

theorem sal_m32_imm8_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 8) :
    Triple (Rmw32Pre p am 4 (0x67 :: encodeSalM32Imm8 am imm).length)
      (codeRange p (0x67 :: encodeSalM32Imm8 am imm))
      (Effect.post (salMA32Effect p (0x67 :: encodeSalM32Imm8 am imm).length 32 am
        (shiftCount 32 imm))) := by
  unfold encodeSalM32Imm8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := sal_m32_imm8_a32_triple_of_bytes p am hv hx hb imm
    rwa [show (0x67 :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := sal_m32_imm8_rex_a32_triple_of_bytes p _ hrex am hv hx hb imm
    rwa [show (0x67 :: am.rexByte false 0 ::
      0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)).length =
      5 + am.tail.length by simp; omega]

theorem sal_m16_imm8_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 8) :
    Triple (Rmw32Pre p am 2 (0x67 :: encodeSalM16Imm8 am imm).length)
      (codeRange p (0x67 :: encodeSalM16Imm8 am imm))
      (Effect.post (salMA32Effect p (0x67 :: encodeSalM16Imm8 am imm).length 16 am
        (shiftCount 16 imm))) := by
  unfold encodeSalM16Imm8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := sal_m16_imm8_a32_triple_of_bytes p am hv hx hb imm
    rwa [show (0x67 :: 0x66 :: 0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)).length =
      5 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := sal_m16_imm8_rex_a32_triple_of_bytes p _ hrex am hv hx hb imm
    rwa [show (0x67 :: 0x66 :: am.rexByte false 0 ::
      0xC1 :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)).length =
      6 + am.tail.length by simp; omega]

theorem sal_m64_one_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 8 (3 + am.tail.length))
      (codeRange p (rex :: 0xD1 :: am.modrm 6 :: am.tail))
      (salMEffect p (3 + am.tail.length) 64 am 1) := by
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
  have hstep := sal_m_one_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
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
  · apply shlFlags_allows

theorem sal_m64_one_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 8 (3 + am.tail.length))
      (codeRange p (rex :: 0xD1 :: am.modrm 6 :: am.tail))
      (Effect.post (salMEffect p (3 + am.tail.length) 64 am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (sal_m64_one_effect_step p rex hrex am hv hx hb)

theorem sal_m32_one_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (RmwPre p am 4 (2 + am.tail.length))
      (codeRange p (0xD1 :: am.modrm 6 :: am.tail))
      (salMEffect p (2 + am.tail.length) 32 am 1) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := sal_m_one_step s h [] (by simp) (by simp) 32 (.inr rfl)
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
  · apply shlFlags_allows

theorem sal_m32_one_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (RmwPre p am 4 (2 + am.tail.length))
      (codeRange p (0xD1 :: am.modrm 6 :: am.tail))
      (Effect.post (salMEffect p (2 + am.tail.length) 32 am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (sal_m32_one_effect_step p am hv hx hb)

theorem sal_m32_one_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 4 (3 + am.tail.length))
      (codeRange p (rex :: 0xD1 :: am.modrm 6 :: am.tail))
      (salMEffect p (3 + am.tail.length) 32 am 1) := by
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
  have hstep := sal_m_one_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
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
  · apply shlFlags_allows

theorem sal_m32_one_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 4 (3 + am.tail.length))
      (codeRange p (rex :: 0xD1 :: am.modrm 6 :: am.tail))
      (Effect.post (salMEffect p (3 + am.tail.length) 32 am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (sal_m32_one_rex_effect_step p rex hrex am hv hx hb)

theorem sal_m16_one_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (RmwPre p am 2 (3 + am.tail.length))
      (codeRange p (0x66 :: 0xD1 :: am.modrm 6 :: am.tail))
      (salMEffect p (3 + am.tail.length) 16 am 1) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := sal_m16_one_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
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
  · apply shlFlags_allows

theorem sal_m16_one_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (RmwPre p am 2 (3 + am.tail.length))
      (codeRange p (0x66 :: 0xD1 :: am.modrm 6 :: am.tail))
      (Effect.post (salMEffect p (3 + am.tail.length) 16 am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (sal_m16_one_effect_step p am hv hx hb)

theorem sal_m16_one_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 2 (4 + am.tail.length))
      (codeRange p (0x66 :: rex :: 0xD1 :: am.modrm 6 :: am.tail))
      (salMEffect p (4 + am.tail.length) 16 am 1) := by
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
  have hstep := sal_m16_one_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
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
  · apply shlFlags_allows

theorem sal_m16_one_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 2 (4 + am.tail.length))
      (codeRange p (0x66 :: rex :: 0xD1 :: am.modrm 6 :: am.tail))
      (Effect.post (salMEffect p (4 + am.tail.length) 16 am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMEffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (sal_m16_one_rex_effect_step p rex hrex am hv hx hb)

theorem sal_m64_one_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegRmwPre p r base am 8 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xD1 :: am.modrm 6 :: am.tail))
      (salMSegEffect p (4 + am.tail.length) 64 base am 1) := by
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
  have hstep := sal_m_one_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
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
  · apply shlFlags_allows

theorem sal_m64_one_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegRmwPre p r base am 8 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xD1 :: am.modrm 6 :: am.tail))
      (Effect.post (salMSegEffect p (4 + am.tail.length) 64 base am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (sal_m64_one_seg_effect_step p r base rex hrex am hv hx hb)

theorem sal_m32_one_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (SegRmwPre p r base am 4 (3 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xD1 :: am.modrm 6 :: am.tail))
      (salMSegEffect p (3 + am.tail.length) 32 base am 1) := by
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
  have hstep := sal_m_one_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp) 32 (.inr rfl)
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
  · apply shlFlags_allows

theorem sal_m32_one_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (SegRmwPre p r base am 4 (3 + am.tail.length))
      (codeRange p (r.prefixByte :: 0xD1 :: am.modrm 6 :: am.tail))
      (Effect.post (salMSegEffect p (3 + am.tail.length) 32 base am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (sal_m32_one_seg_effect_step p r base am hv hx hb)

theorem sal_m32_one_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegRmwPre p r base am 4 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xD1 :: am.modrm 6 :: am.tail))
      (salMSegEffect p (4 + am.tail.length) 32 base am 1) := by
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
  have hstep := sal_m_one_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
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
  · apply shlFlags_allows

theorem sal_m32_one_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegRmwPre p r base am 4 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0xD1 :: am.modrm 6 :: am.tail))
      (Effect.post (salMSegEffect p (4 + am.tail.length) 32 base am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (sal_m32_one_rex_seg_effect_step p r base rex hrex am hv hx hb)

theorem sal_m16_one_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (SegRmwPre p r base am 2 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: 0xD1 :: am.modrm 6 :: am.tail))
      (salMSegEffect p (4 + am.tail.length) 16 base am 1) := by
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
  have hstep := sal_m16_one_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
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
  · apply shlFlags_allows

theorem sal_m16_one_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (SegRmwPre p r base am 2 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: 0xD1 :: am.modrm 6 :: am.tail))
      (Effect.post (salMSegEffect p (4 + am.tail.length) 16 base am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (sal_m16_one_seg_effect_step p r base am hv hx hb)

theorem sal_m16_one_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegRmwPre p r base am 2 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0xD1 :: am.modrm 6 :: am.tail))
      (salMSegEffect p (5 + am.tail.length) 16 base am 1) := by
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
  have hstep := sal_m16_one_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
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
  · apply shlFlags_allows

theorem sal_m16_one_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegRmwPre p r base am 2 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0xD1 :: am.modrm 6 :: am.tail))
      (Effect.post (salMSegEffect p (5 + am.tail.length) 16 base am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code (by simp; omega))
    (sal_m16_one_rex_seg_effect_step p r base rex hrex am hv hx hb)

theorem sal_m64_one_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Rmw32Pre p am 8 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xD1 :: am.modrm 6 :: am.tail))
      (salMA32Effect p (4 + am.tail.length) 64 am 1) := by
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
  have hstep := sal_m_one_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
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
  · apply shlFlags_allows

theorem sal_m64_one_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (Rmw32Pre p am 8 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xD1 :: am.modrm 6 :: am.tail))
      (Effect.post (salMA32Effect p (4 + am.tail.length) 64 am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (sal_m64_one_a32_effect_step p rex hrex am hv hx hb)

theorem sal_m32_one_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (Rmw32Pre p am 4 (3 + am.tail.length))
      (codeRange p (0x67 :: 0xD1 :: am.modrm 6 :: am.tail))
      (salMA32Effect p (3 + am.tail.length) 32 am 1) := by
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
  have hstep := sal_m_one_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp) 32 (.inr rfl)
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
  · apply shlFlags_allows

theorem sal_m32_one_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (Rmw32Pre p am 4 (3 + am.tail.length))
      (codeRange p (0x67 :: 0xD1 :: am.modrm 6 :: am.tail))
      (Effect.post (salMA32Effect p (3 + am.tail.length) 32 am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (sal_m32_one_a32_effect_step p am hv hx hb)

theorem sal_m32_one_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Rmw32Pre p am 4 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xD1 :: am.modrm 6 :: am.tail))
      (salMA32Effect p (4 + am.tail.length) 32 am 1) := by
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
  have hstep := sal_m_one_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
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
  · apply shlFlags_allows

theorem sal_m32_one_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (Rmw32Pre p am 4 (4 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0xD1 :: am.modrm 6 :: am.tail))
      (Effect.post (salMA32Effect p (4 + am.tail.length) 32 am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (sal_m32_one_rex_a32_effect_step p rex hrex am hv hx hb)

theorem sal_m16_one_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (Rmw32Pre p am 2 (4 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: 0xD1 :: am.modrm 6 :: am.tail))
      (salMA32Effect p (4 + am.tail.length) 16 am 1) := by
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
  have hstep := sal_m16_one_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
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
  · apply shlFlags_allows

theorem sal_m16_one_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (Rmw32Pre p am 2 (4 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: 0xD1 :: am.modrm 6 :: am.tail))
      (Effect.post (salMA32Effect p (4 + am.tail.length) 16 am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (sal_m16_one_a32_effect_step p am hv hx hb)

theorem sal_m16_one_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Rmw32Pre p am 2 (5 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: rex :: 0xD1 :: am.modrm 6 :: am.tail))
      (salMA32Effect p (5 + am.tail.length) 16 am 1) := by
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
  have hstep := sal_m16_one_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
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
  · apply shlFlags_allows

theorem sal_m16_one_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (Rmw32Pre p am 2 (5 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: rex :: 0xD1 :: am.modrm 6 :: am.tail))
      (Effect.post (salMA32Effect p (5 + am.tail.length) 16 am 1)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [salMA32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (sal_m16_one_rex_a32_effect_step p rex hrex am hv hx hb)

theorem sal_m64_one_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (RmwPre p am 8 (3 + am.tail.length))
      (codeRange p (encodeSalM64One am))
      (Effect.post (salMEffect p (3 + am.tail.length) 64 am 1)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact sal_m64_one_triple_of_bytes p _ hrex am hv hx hb

theorem sal_m32_one_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (RmwPre p am 4 (encodeSalM32One am).length)
      (codeRange p (encodeSalM32One am))
      (Effect.post (salMEffect p (encodeSalM32One am).length 32 am 1)) := by
  unfold encodeSalM32One
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := sal_m32_one_triple_of_bytes p am hv hx hb
    rwa [show (0xD1 :: am.modrm 6 :: am.tail).length =
      2 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := sal_m32_one_rex_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (am.rexByte false 0 ::
      0xD1 :: am.modrm 6 :: am.tail).length =
      3 + am.tail.length by simp; omega]

theorem sal_m16_one_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (RmwPre p am 2 (encodeSalM16One am).length)
      (codeRange p (encodeSalM16One am))
      (Effect.post (salMEffect p (encodeSalM16One am).length 16 am 1)) := by
  unfold encodeSalM16One
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := sal_m16_one_triple_of_bytes p am hv hx hb
    rwa [show (0x66 :: 0xD1 :: am.modrm 6 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := sal_m16_one_rex_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (0x66 :: am.rexByte false 0 ::
      0xD1 :: am.modrm 6 :: am.tail).length =
      4 + am.tail.length by simp; omega]

theorem sal_m64_one_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegRmwPre p r base am 8 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: encodeSalM64One am))
      (Effect.post (salMSegEffect p (4 + am.tail.length) 64 base am 1)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact sal_m64_one_seg_triple_of_bytes p r base _ hrex am hv hx hb

theorem sal_m32_one_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegRmwPre p r base am 4 (r.prefixByte :: encodeSalM32One am).length)
      (codeRange p (r.prefixByte :: encodeSalM32One am))
      (Effect.post (salMSegEffect p (r.prefixByte :: encodeSalM32One am).length 32 base am 1)) := by
  unfold encodeSalM32One
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := sal_m32_one_seg_triple_of_bytes p r base am hv hx hb
    rwa [show (r.prefixByte :: 0xD1 :: am.modrm 6 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := sal_m32_one_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb
    rwa [show (r.prefixByte :: am.rexByte false 0 ::
      0xD1 :: am.modrm 6 :: am.tail).length =
      4 + am.tail.length by simp; omega]

theorem sal_m16_one_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegRmwPre p r base am 2 (r.prefixByte :: encodeSalM16One am).length)
      (codeRange p (r.prefixByte :: encodeSalM16One am))
      (Effect.post (salMSegEffect p (r.prefixByte :: encodeSalM16One am).length 16 base am 1)) := by
  unfold encodeSalM16One
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := sal_m16_one_seg_triple_of_bytes p r base am hv hx hb
    rwa [show (r.prefixByte :: 0x66 :: 0xD1 :: am.modrm 6 :: am.tail).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := sal_m16_one_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb
    rwa [show (r.prefixByte :: 0x66 :: am.rexByte false 0 ::
      0xD1 :: am.modrm 6 :: am.tail).length =
      5 + am.tail.length by simp; omega]

theorem sal_m64_one_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (Rmw32Pre p am 8 (4 + am.tail.length))
      (codeRange p (0x67 :: encodeSalM64One am))
      (Effect.post (salMA32Effect p (4 + am.tail.length) 64 am 1)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact sal_m64_one_a32_triple_of_bytes p _ hrex am hv hx hb

theorem sal_m32_one_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (Rmw32Pre p am 4 (0x67 :: encodeSalM32One am).length)
      (codeRange p (0x67 :: encodeSalM32One am))
      (Effect.post (salMA32Effect p (0x67 :: encodeSalM32One am).length 32 am 1)) := by
  unfold encodeSalM32One
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := sal_m32_one_a32_triple_of_bytes p am hv hx hb
    rwa [show (0x67 :: 0xD1 :: am.modrm 6 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := sal_m32_one_rex_a32_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (0x67 :: am.rexByte false 0 ::
      0xD1 :: am.modrm 6 :: am.tail).length =
      4 + am.tail.length by simp; omega]

theorem sal_m16_one_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (Rmw32Pre p am 2 (0x67 :: encodeSalM16One am).length)
      (codeRange p (0x67 :: encodeSalM16One am))
      (Effect.post (salMA32Effect p (0x67 :: encodeSalM16One am).length 16 am 1)) := by
  unfold encodeSalM16One
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := sal_m16_one_a32_triple_of_bytes p am hv hx hb
    rwa [show (0x67 :: 0x66 :: 0xD1 :: am.modrm 6 :: am.tail).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := sal_m16_one_rex_a32_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (0x67 :: 0x66 :: am.rexByte false 0 ::
      0xD1 :: am.modrm 6 :: am.tail).length =
      5 + am.tail.length by simp; omega]

attribute [x86_compose] salMEffect

theorem salMEffect_local {p : BitVec 64} {len n : Nat} {am : AddrMode} {c : Nat}
    (hn : n % 8 = 0) :
    Effect.Local (salMEffect p len n am c) := by
  effect_local [salMEffect, shlFlags, hn]

@[x86_local] theorem salMEffect_local64 {p : BitVec 64} {len : Nat} {am : AddrMode}
    {c : Nat} : Effect.Local (salMEffect p len 64 am c) :=
  salMEffect_local (by decide)

@[x86_local] theorem salMEffect_local32 {p : BitVec 64} {len : Nat} {am : AddrMode}
    {c : Nat} : Effect.Local (salMEffect p len 32 am c) :=
  salMEffect_local (by decide)

@[x86_local] theorem salMEffect_local16 {p : BitVec 64} {len : Nat} {am : AddrMode}
    {c : Nat} : Effect.Local (salMEffect p len 16 am c) :=
  salMEffect_local (by decide)

@[x86_local] theorem salMEffect_local8 {p : BitVec 64} {len : Nat} {am : AddrMode}
    {c : Nat} : Effect.Local (salMEffect p len 8 am c) :=
  salMEffect_local (by decide)

attribute [x86_compose] salMSegEffect

theorem salMSegEffect_local {p : BitVec 64} {len n : Nat} {base : BitVec 64} {am : AddrMode} {c : Nat}
    (hn : n % 8 = 0) :
    Effect.Local (salMSegEffect p len n base am c) := by
  effect_local [salMSegEffect, shlFlags, hn]

@[x86_local] theorem salMSegEffect_local64 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {c : Nat} :
    Effect.Local (salMSegEffect p len 64 base am c) :=
  salMSegEffect_local (by decide)

@[x86_local] theorem salMSegEffect_local32 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {c : Nat} :
    Effect.Local (salMSegEffect p len 32 base am c) :=
  salMSegEffect_local (by decide)

@[x86_local] theorem salMSegEffect_local16 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {c : Nat} :
    Effect.Local (salMSegEffect p len 16 base am c) :=
  salMSegEffect_local (by decide)

@[x86_local] theorem salMSegEffect_local8 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {c : Nat} :
    Effect.Local (salMSegEffect p len 8 base am c) :=
  salMSegEffect_local (by decide)

attribute [x86_compose] salMA32Effect

theorem salMA32Effect_local {p : BitVec 64} {len n : Nat} {am : AddrMode} {c : Nat}
    (hn : n % 8 = 0) :
    Effect.Local (salMA32Effect p len n am c) := by
  effect_local [salMA32Effect, shlFlags, hn]

@[x86_local] theorem salMA32Effect_local64 {p : BitVec 64} {len : Nat} {am : AddrMode}
    {c : Nat} : Effect.Local (salMA32Effect p len 64 am c) :=
  salMA32Effect_local (by decide)

@[x86_local] theorem salMA32Effect_local32 {p : BitVec 64} {len : Nat} {am : AddrMode}
    {c : Nat} : Effect.Local (salMA32Effect p len 32 am c) :=
  salMA32Effect_local (by decide)

@[x86_local] theorem salMA32Effect_local16 {p : BitVec 64} {len : Nat} {am : AddrMode}
    {c : Nat} : Effect.Local (salMA32Effect p len 16 am c) :=
  salMA32Effect_local (by decide)

@[x86_local] theorem salMA32Effect_local8 {p : BitVec 64} {len : Nat} {am : AddrMode}
    {c : Nat} : Effect.Local (salMA32Effect p len 8 am c) :=
  salMA32Effect_local (by decide)

end X86Proofs
