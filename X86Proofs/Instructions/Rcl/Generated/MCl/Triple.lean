import X86Proofs.Instructions.Rcl.Generated.MCl.Step
import X86Proofs.Instructions.Rcl.Generated.MCl.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Rcl.Generated.M.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def rclMClEffect (p : BitVec 64) (len n : Nat) (am : AddrMode) (cf : Bool) (s : RamState) :
    Effect :=
  rclMEffect p len n am (shiftCount n ((Operand.reg 1 : Operand 8).read s)) cf s

@[simp] theorem rclMClEffect_components (p : BitVec 64) (len n : Nat) (am : AddrMode) (cf : Bool)
    (s : RamState) : (rclMClEffect p len n am cf s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) (n / 8), .flags, .rip] := rfl

def rclMClSegEffect (p : BitVec 64) (len n : Nat) (base : BitVec 64) (am : AddrMode) (cf : Bool)
    (s : RamState) : Effect :=
  rclMSegEffect p len n base am (shiftCount n ((Operand.reg 1 : Operand 8).read s)) cf s

@[simp] theorem rclMClSegEffect_components (p : BitVec 64) (len n : Nat) (base : BitVec 64)
    (am : AddrMode) (cf : Bool) (s : RamState) : (rclMClSegEffect p len n base am cf s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) (n / 8), .flags, .rip] := rfl

def rclMClA32Effect (p : BitVec 64) (len n : Nat) (am : AddrMode) (cf : Bool) (s : RamState) :
    Effect :=
  rclMA32Effect p len n am (shiftCount n ((Operand.reg 1 : Operand 8).read s)) cf s

@[simp] theorem rclMClA32Effect_components (p : BitVec 64) (len n : Nat) (am : AddrMode) (cf : Bool)
    (s : RamState) : (rclMClA32Effect p len n am cf s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) (n / 8), .flags, .rip] := rfl

theorem rcl_m64_cl_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    StepEffect (fun s => RmwPre p am 8 (3 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (rex :: 0xD3 :: am.modrm 2 :: am.tail))
      (rclMClEffect p (3 + am.tail.length) 64 am cf) := by
  have hr := hrex.rexPrefix
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
  have hstep := rcl_m_cl_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
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
  · apply rclFlags_allows

theorem rcl_m64_cl_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    Triple (fun s => RmwPre p am 8 (3 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (rex :: 0xD3 :: am.modrm 2 :: am.tail))
      (Effect.post (rclMClEffect p (3 + am.tail.length) 64 am cf)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rclMClEffect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (rcl_m64_cl_effect_step p rex hrex am hv hx hb cf)

theorem rcl_m32_cl_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (cf : Bool) :
    StepEffect (fun s => RmwPre p am 4 (2 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0xD3 :: am.modrm 2 :: am.tail))
      (rclMClEffect p (2 + am.tail.length) 32 am cf) := by
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
  have hstep := rcl_m_cl_step s h [] (by simp) (by simp) 32 (.inr rfl)
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
  · apply rclFlags_allows

theorem rcl_m32_cl_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (cf : Bool) :
    Triple (fun s => RmwPre p am 4 (2 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0xD3 :: am.modrm 2 :: am.tail))
      (Effect.post (rclMClEffect p (2 + am.tail.length) 32 am cf)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rclMClEffect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (rcl_m32_cl_effect_step p am hv hx hb cf)

theorem rcl_m32_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    StepEffect (fun s => RmwPre p am 4 (3 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (rex :: 0xD3 :: am.modrm 2 :: am.tail))
      (rclMClEffect p (3 + am.tail.length) 32 am cf) := by
  have hr := hrex.rexPrefix
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
  have hstep := rcl_m_cl_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
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
  · apply rclFlags_allows

theorem rcl_m32_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    Triple (fun s => RmwPre p am 4 (3 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (rex :: 0xD3 :: am.modrm 2 :: am.tail))
      (Effect.post (rclMClEffect p (3 + am.tail.length) 32 am cf)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rclMClEffect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (rcl_m32_cl_rex_effect_step p rex hrex am hv hx hb cf)

theorem rcl_m16_cl_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (cf : Bool) :
    StepEffect (fun s => RmwPre p am 2 (3 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0x66 :: 0xD3 :: am.modrm 2 :: am.tail))
      (rclMClEffect p (3 + am.tail.length) 16 am cf) := by
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
  have hstep := rcl_m16_cl_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
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
  · apply rclFlags_allows

theorem rcl_m16_cl_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (cf : Bool) :
    Triple (fun s => RmwPre p am 2 (3 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0x66 :: 0xD3 :: am.modrm 2 :: am.tail))
      (Effect.post (rclMClEffect p (3 + am.tail.length) 16 am cf)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rclMClEffect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (rcl_m16_cl_effect_step p am hv hx hb cf)

theorem rcl_m16_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    StepEffect (fun s => RmwPre p am 2 (4 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0x66 :: rex :: 0xD3 :: am.modrm 2 :: am.tail))
      (rclMClEffect p (4 + am.tail.length) 16 am cf) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := rcl_m16_cl_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
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
  · apply rclFlags_allows

theorem rcl_m16_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    Triple (fun s => RmwPre p am 2 (4 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0x66 :: rex :: 0xD3 :: am.modrm 2 :: am.tail))
      (Effect.post (rclMClEffect p (4 + am.tail.length) 16 am cf)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rclMClEffect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (rcl_m16_cl_rex_effect_step p rex hrex am hv hx hb cf)

theorem rcl_m64_cl_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 8 (4 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (r.prefixByte :: rex :: 0xD3 :: am.modrm 2 :: am.tail))
      (rclMClSegEffect p (4 + am.tail.length) 64 base am cf) := by
  have hr := hrex.rexPrefix
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
  have hstep := rcl_m_cl_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
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
  · apply rclFlags_allows

theorem rcl_m64_cl_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    Triple (fun s => SegRmwPre p r base am 8 (4 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (r.prefixByte :: rex :: 0xD3 :: am.modrm 2 :: am.tail))
      (Effect.post (rclMClSegEffect p (4 + am.tail.length) 64 base am cf)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rclMClSegEffect_components]; exact mem_components_rmw _ _) hpre.1.store.code (by simp; omega))
    (rcl_m64_cl_seg_effect_step p r base rex hrex am hv hx hb cf)

theorem rcl_m32_cl_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (cf : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 4 (3 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (r.prefixByte :: 0xD3 :: am.modrm 2 :: am.tail))
      (rclMClSegEffect p (3 + am.tail.length) 32 base am cf) := by
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
  have hstep := rcl_m_cl_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp) 32 (.inr rfl)
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
  · apply rclFlags_allows

theorem rcl_m32_cl_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (cf : Bool) :
    Triple (fun s => SegRmwPre p r base am 4 (3 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (r.prefixByte :: 0xD3 :: am.modrm 2 :: am.tail))
      (Effect.post (rclMClSegEffect p (3 + am.tail.length) 32 base am cf)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rclMClSegEffect_components]; exact mem_components_rmw _ _) hpre.1.store.code (by simp; omega))
    (rcl_m32_cl_seg_effect_step p r base am hv hx hb cf)

theorem rcl_m32_cl_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 4 (4 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (r.prefixByte :: rex :: 0xD3 :: am.modrm 2 :: am.tail))
      (rclMClSegEffect p (4 + am.tail.length) 32 base am cf) := by
  have hr := hrex.rexPrefix
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
  have hstep := rcl_m_cl_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
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
  · apply rclFlags_allows

theorem rcl_m32_cl_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    Triple (fun s => SegRmwPre p r base am 4 (4 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (r.prefixByte :: rex :: 0xD3 :: am.modrm 2 :: am.tail))
      (Effect.post (rclMClSegEffect p (4 + am.tail.length) 32 base am cf)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rclMClSegEffect_components]; exact mem_components_rmw _ _) hpre.1.store.code (by simp; omega))
    (rcl_m32_cl_rex_seg_effect_step p r base rex hrex am hv hx hb cf)

theorem rcl_m16_cl_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (cf : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 2 (4 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (r.prefixByte :: 0x66 :: 0xD3 :: am.modrm 2 :: am.tail))
      (rclMClSegEffect p (4 + am.tail.length) 16 base am cf) := by
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  subst hc
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66]
      (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := rcl_m16_cl_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
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
  · apply rclFlags_allows

theorem rcl_m16_cl_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (cf : Bool) :
    Triple (fun s => SegRmwPre p r base am 2 (4 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (r.prefixByte :: 0x66 :: 0xD3 :: am.modrm 2 :: am.tail))
      (Effect.post (rclMClSegEffect p (4 + am.tail.length) 16 base am cf)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rclMClSegEffect_components]; exact mem_components_rmw _ _) hpre.1.store.code (by simp; omega))
    (rcl_m16_cl_seg_effect_step p r base am hv hx hb cf)

theorem rcl_m16_cl_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    StepEffect (fun s => SegRmwPre p r base am 2 (5 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0xD3 :: am.modrm 2 :: am.tail))
      (rclMClSegEffect p (5 + am.tail.length) 16 base am cf) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hp hbase
  subst hc
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66, rex] =
      withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66, rex]
      (noSegPrefix_cons noSegPrefix_66 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_66_rex _ _ hr]
  have hstep := rcl_m16_cl_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
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
  · apply rclFlags_allows

theorem rcl_m16_cl_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    Triple (fun s => SegRmwPre p r base am 2 (5 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0xD3 :: am.modrm 2 :: am.tail))
      (Effect.post (rclMClSegEffect p (5 + am.tail.length) 16 base am cf)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rclMClSegEffect_components]; exact mem_components_rmw _ _) hpre.1.store.code (by simp; omega))
    (rcl_m16_cl_rex_seg_effect_step p r base rex hrex am hv hx hb cf)

theorem rcl_m64_cl_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    StepEffect (fun s => Rmw32Pre p am 8 (4 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0x67 :: rex :: 0xD3 :: am.modrm 2 :: am.tail))
      (rclMClA32Effect p (4 + am.tail.length) 64 am cf) := by
  have hr := hrex.rexPrefix
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
  have hstep := rcl_m_cl_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
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
  · apply rclFlags_allows

theorem rcl_m64_cl_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    Triple (fun s => Rmw32Pre p am 8 (4 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0x67 :: rex :: 0xD3 :: am.modrm 2 :: am.tail))
      (Effect.post (rclMClA32Effect p (4 + am.tail.length) 64 am cf)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rclMClA32Effect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (rcl_m64_cl_a32_effect_step p rex hrex am hv hx hb cf)

theorem rcl_m32_cl_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (cf : Bool) :
    StepEffect (fun s => Rmw32Pre p am 4 (3 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0x67 :: 0xD3 :: am.modrm 2 :: am.tail))
      (rclMClA32Effect p (3 + am.tail.length) 32 am cf) := by
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
  have hstep := rcl_m_cl_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp) 32 (.inr rfl)
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
  · apply rclFlags_allows

theorem rcl_m32_cl_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (cf : Bool) :
    Triple (fun s => Rmw32Pre p am 4 (3 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0x67 :: 0xD3 :: am.modrm 2 :: am.tail))
      (Effect.post (rclMClA32Effect p (3 + am.tail.length) 32 am cf)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rclMClA32Effect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (rcl_m32_cl_a32_effect_step p am hv hx hb cf)

theorem rcl_m32_cl_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    StepEffect (fun s => Rmw32Pre p am 4 (4 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0x67 :: rex :: 0xD3 :: am.modrm 2 :: am.tail))
      (rclMClA32Effect p (4 + am.tail.length) 32 am cf) := by
  have hr := hrex.rexPrefix
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
  have hstep := rcl_m_cl_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
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
  · apply rclFlags_allows

theorem rcl_m32_cl_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    Triple (fun s => Rmw32Pre p am 4 (4 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0x67 :: rex :: 0xD3 :: am.modrm 2 :: am.tail))
      (Effect.post (rclMClA32Effect p (4 + am.tail.length) 32 am cf)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rclMClA32Effect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (rcl_m32_cl_rex_a32_effect_step p rex hrex am hv hx hb cf)

theorem rcl_m16_cl_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (cf : Bool) :
    StepEffect (fun s => Rmw32Pre p am 2 (4 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0x67 :: 0x66 :: 0xD3 :: am.modrm 2 :: am.tail))
      (rclMClA32Effect p (4 + am.tail.length) 16 am cf) := by
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
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66]) := by
    rw [scanContext_asz_cons]
  have hstep := rcl_m16_cl_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
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
  · apply rclFlags_allows

theorem rcl_m16_cl_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) (cf : Bool) :
    Triple (fun s => Rmw32Pre p am 2 (4 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0x67 :: 0x66 :: 0xD3 :: am.modrm 2 :: am.tail))
      (Effect.post (rclMClA32Effect p (4 + am.tail.length) 16 am cf)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rclMClA32Effect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (rcl_m16_cl_a32_effect_step p am hv hx hb cf)

theorem rcl_m16_cl_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    StepEffect (fun s => Rmw32Pre p am 2 (5 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0x67 :: 0x66 :: rex :: 0xD3 :: am.modrm 2 :: am.tail))
      (rclMClA32Effect p (5 + am.tail.length) 16 am cf) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  subst hc
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, rex] =
      withAsz (oszRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_66_rex _ _ hr]
  have hstep := rcl_m16_cl_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
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
  · apply rclFlags_allows

theorem rcl_m16_cl_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) (cf : Bool) :
    Triple (fun s => Rmw32Pre p am 2 (5 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0x67 :: 0x66 :: rex :: 0xD3 :: am.modrm 2 :: am.tail))
      (Effect.post (rclMClA32Effect p (5 + am.tail.length) 16 am cf)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [rclMClA32Effect_components]; exact mem_components_rmw _ _) hpre.1.code (by simp; omega))
    (rcl_m16_cl_rex_a32_effect_step p rex hrex am hv hx hb cf)

theorem rcl_m64_cl_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (cf : Bool) :
    Triple (fun s => RmwPre p am 8 (3 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (encodeRclM64Cl am))
      (Effect.post (rclMClEffect p (3 + am.tail.length) 64 am cf)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact rcl_m64_cl_triple_of_bytes p _ hrex am hv hx hb cf

theorem rcl_m32_cl_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (cf : Bool) :
    Triple (fun s => RmwPre p am 4 (encodeRclM32Cl am).length s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (encodeRclM32Cl am))
      (Effect.post (rclMClEffect p (encodeRclM32Cl am).length 32 am cf)) := by
  unfold encodeRclM32Cl
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rcl_m32_cl_triple_of_bytes p am hv hx hb cf
    rwa [show (0xD3 :: am.modrm 2 :: am.tail).length =
      2 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rcl_m32_cl_rex_triple_of_bytes p _ hrex am hv hx hb cf
    rwa [show (am.rexByte false 0 ::
      0xD3 :: am.modrm 2 :: am.tail).length =
      3 + am.tail.length by simp; omega]

theorem rcl_m16_cl_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (cf : Bool) :
    Triple (fun s => RmwPre p am 2 (encodeRclM16Cl am).length s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (encodeRclM16Cl am))
      (Effect.post (rclMClEffect p (encodeRclM16Cl am).length 16 am cf)) := by
  unfold encodeRclM16Cl
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rcl_m16_cl_triple_of_bytes p am hv hx hb cf
    rwa [show (0x66 :: 0xD3 :: am.modrm 2 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rcl_m16_cl_rex_triple_of_bytes p _ hrex am hv hx hb cf
    rwa [show (0x66 :: am.rexByte false 0 ::
      0xD3 :: am.modrm 2 :: am.tail).length =
      4 + am.tail.length by simp; omega]

theorem rcl_m64_cl_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (cf : Bool) :
    Triple (fun s => SegRmwPre p r base am 8 (4 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (r.prefixByte :: encodeRclM64Cl am))
      (Effect.post (rclMClSegEffect p (4 + am.tail.length) 64 base am cf)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact rcl_m64_cl_seg_triple_of_bytes p r base _ hrex am hv hx hb cf

theorem rcl_m32_cl_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (cf : Bool) :
    Triple (fun s => SegRmwPre p r base am 4 (r.prefixByte :: encodeRclM32Cl am).length s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (r.prefixByte :: encodeRclM32Cl am))
      (Effect.post (rclMClSegEffect p (r.prefixByte :: encodeRclM32Cl am).length 32 base am cf)) := by
  unfold encodeRclM32Cl
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rcl_m32_cl_seg_triple_of_bytes p r base am hv hx hb cf
    rwa [show (r.prefixByte :: 0xD3 :: am.modrm 2 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rcl_m32_cl_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb cf
    rwa [show (r.prefixByte :: am.rexByte false 0 ::
      0xD3 :: am.modrm 2 :: am.tail).length =
      4 + am.tail.length by simp; omega]

theorem rcl_m16_cl_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (cf : Bool) :
    Triple (fun s => SegRmwPre p r base am 2 (r.prefixByte :: encodeRclM16Cl am).length s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (r.prefixByte :: encodeRclM16Cl am))
      (Effect.post (rclMClSegEffect p (r.prefixByte :: encodeRclM16Cl am).length 16 base am cf)) := by
  unfold encodeRclM16Cl
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rcl_m16_cl_seg_triple_of_bytes p r base am hv hx hb cf
    rwa [show (r.prefixByte :: 0x66 :: 0xD3 :: am.modrm 2 :: am.tail).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rcl_m16_cl_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb cf
    rwa [show (r.prefixByte :: 0x66 :: am.rexByte false 0 ::
      0xD3 :: am.modrm 2 :: am.tail).length =
      5 + am.tail.length by simp; omega]

theorem rcl_m64_cl_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (cf : Bool) :
    Triple (fun s => Rmw32Pre p am 8 (4 + am.tail.length) s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0x67 :: encodeRclM64Cl am))
      (Effect.post (rclMClA32Effect p (4 + am.tail.length) 64 am cf)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact rcl_m64_cl_a32_triple_of_bytes p _ hrex am hv hx hb cf

theorem rcl_m32_cl_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (cf : Bool) :
    Triple (fun s => Rmw32Pre p am 4 (0x67 :: encodeRclM32Cl am).length s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0x67 :: encodeRclM32Cl am))
      (Effect.post (rclMClA32Effect p (0x67 :: encodeRclM32Cl am).length 32 am cf)) := by
  unfold encodeRclM32Cl
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rcl_m32_cl_a32_triple_of_bytes p am hv hx hb cf
    rwa [show (0x67 :: 0xD3 :: am.modrm 2 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rcl_m32_cl_rex_a32_triple_of_bytes p _ hrex am hv hx hb cf
    rwa [show (0x67 :: am.rexByte false 0 ::
      0xD3 :: am.modrm 2 :: am.tail).length =
      4 + am.tail.length by simp; omega]

theorem rcl_m16_cl_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (cf : Bool) :
    Triple (fun s => Rmw32Pre p am 2 (0x67 :: encodeRclM16Cl am).length s ∧
      (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p (0x67 :: encodeRclM16Cl am))
      (Effect.post (rclMClA32Effect p (0x67 :: encodeRclM16Cl am).length 16 am cf)) := by
  unfold encodeRclM16Cl
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := rcl_m16_cl_a32_triple_of_bytes p am hv hx hb cf
    rwa [show (0x67 :: 0x66 :: 0xD3 :: am.modrm 2 :: am.tail).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := rcl_m16_cl_rex_a32_triple_of_bytes p _ hrex am hv hx hb cf
    rwa [show (0x67 :: 0x66 :: am.rexByte false 0 ::
      0xD3 :: am.modrm 2 :: am.tail).length =
      5 + am.tail.length by simp; omega]

attribute [x86_compose] rclMClEffect

theorem rclMClEffect_local {p : BitVec 64} {len n : Nat} {am : AddrMode} {cf : Bool}
    (hn : n % 8 = 0) : Effect.Local (rclMClEffect p len n am cf) :=
  Effect.Local.of_param (e := fun c => rclMEffect p len n am c cf)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => rclMEffect_local hn

@[x86_local] theorem rclMClEffect_local64 {p : BitVec 64} {len : Nat}
    {am : AddrMode} {cf : Bool} : Effect.Local (rclMClEffect p len 64 am cf) :=
  rclMClEffect_local (by decide)

@[x86_local] theorem rclMClEffect_local32 {p : BitVec 64} {len : Nat}
    {am : AddrMode} {cf : Bool} : Effect.Local (rclMClEffect p len 32 am cf) :=
  rclMClEffect_local (by decide)

@[x86_local] theorem rclMClEffect_local16 {p : BitVec 64} {len : Nat}
    {am : AddrMode} {cf : Bool} : Effect.Local (rclMClEffect p len 16 am cf) :=
  rclMClEffect_local (by decide)

@[x86_local] theorem rclMClEffect_local8 {p : BitVec 64} {len : Nat}
    {am : AddrMode} {cf : Bool} : Effect.Local (rclMClEffect p len 8 am cf) :=
  rclMClEffect_local (by decide)

attribute [x86_compose] rclMClSegEffect

theorem rclMClSegEffect_local {p : BitVec 64} {len n : Nat} {base : BitVec 64} {am : AddrMode}
    {cf : Bool} (hn : n % 8 = 0) :
    Effect.Local (rclMClSegEffect p len n base am cf) :=
  Effect.Local.of_param (e := fun c => rclMSegEffect p len n base am c cf)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => rclMSegEffect_local hn

@[x86_local] theorem rclMClSegEffect_local64 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {cf : Bool} :
    Effect.Local (rclMClSegEffect p len 64 base am cf) :=
  rclMClSegEffect_local (by decide)

@[x86_local] theorem rclMClSegEffect_local32 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {cf : Bool} :
    Effect.Local (rclMClSegEffect p len 32 base am cf) :=
  rclMClSegEffect_local (by decide)

@[x86_local] theorem rclMClSegEffect_local16 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {cf : Bool} :
    Effect.Local (rclMClSegEffect p len 16 base am cf) :=
  rclMClSegEffect_local (by decide)

@[x86_local] theorem rclMClSegEffect_local8 {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {cf : Bool} :
    Effect.Local (rclMClSegEffect p len 8 base am cf) :=
  rclMClSegEffect_local (by decide)

attribute [x86_compose] rclMClA32Effect

theorem rclMClA32Effect_local {p : BitVec 64} {len n : Nat} {am : AddrMode} {cf : Bool}
    (hn : n % 8 = 0) : Effect.Local (rclMClA32Effect p len n am cf) :=
  Effect.Local.of_param (e := fun c => rclMA32Effect p len n am c cf)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => rclMA32Effect_local hn

@[x86_local] theorem rclMClA32Effect_local64 {p : BitVec 64} {len : Nat}
    {am : AddrMode} {cf : Bool} : Effect.Local (rclMClA32Effect p len 64 am cf) :=
  rclMClA32Effect_local (by decide)

@[x86_local] theorem rclMClA32Effect_local32 {p : BitVec 64} {len : Nat}
    {am : AddrMode} {cf : Bool} : Effect.Local (rclMClA32Effect p len 32 am cf) :=
  rclMClA32Effect_local (by decide)

@[x86_local] theorem rclMClA32Effect_local16 {p : BitVec 64} {len : Nat}
    {am : AddrMode} {cf : Bool} : Effect.Local (rclMClA32Effect p len 16 am cf) :=
  rclMClA32Effect_local (by decide)

@[x86_local] theorem rclMClA32Effect_local8 {p : BitVec 64} {len : Nat}
    {am : AddrMode} {cf : Bool} : Effect.Local (rclMClA32Effect p len 8 am cf) :=
  rclMClA32Effect_local (by decide)

end X86Proofs
