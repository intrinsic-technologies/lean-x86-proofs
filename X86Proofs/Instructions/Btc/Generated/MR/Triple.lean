import X86Proofs.Instructions.Btc.Generated.MR.Step
import X86Proofs.Instructions.Btc.Generated.MR.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def btcMREffect (p : BitVec 64) (len n : Nat) (src : BitVec 5) (am : AddrMode) (s : RamState) :
    Effect :=
  let a := bitStringAddr n am src (p + BitVec.ofNat 64 len) s
  let x := (Operand.mem a : Operand n).read s
  let y := (Operand.reg src : Operand n).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand n), x ^^^ BitVec.twoPow n (bitOffset y)⟩]
    flags := some (btFlags (StatusFlags.ofRFLAGS s.RFLAGS) x y) }

@[simp] theorem btcMREffect_components (p : BitVec 64) (len n : Nat) (src : BitVec 5)
    (am : AddrMode) (s : RamState) : (btcMREffect p len n src am s).components =
      [.mem (bitStringAddr n am src (p + BitVec.ofNat 64 len) s) (n / 8), .flags, .rip] := rfl

def btcMRSegEffect (p : BitVec 64) (len n : Nat) (base : BitVec 64) (src : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := base + bitStringAddr n am src (p + BitVec.ofNat 64 len) s
  let x := (Operand.mem a : Operand n).read s
  let y := (Operand.reg src : Operand n).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand n), x ^^^ BitVec.twoPow n (bitOffset y)⟩]
    flags := some (btFlags (StatusFlags.ofRFLAGS s.RFLAGS) x y) }

@[simp] theorem btcMRSegEffect_components (p : BitVec 64) (len n : Nat) (base : BitVec 64)
    (src : BitVec 5) (am : AddrMode) (s : RamState) :
    (btcMRSegEffect p len n base src am s).components =
      [.mem (base + bitStringAddr n am src (p + BitVec.ofNat 64 len) s) (n / 8), .flags, .rip] :=
    rfl

def btcMRA32Effect (p : BitVec 64) (len n : Nat) (src : BitVec 5) (am : AddrMode) (s : RamState) :
    Effect :=
  let a := bitStringAddr32 n am src (p + BitVec.ofNat 64 len) s
  let x := (Operand.mem a : Operand n).read s
  let y := (Operand.reg src : Operand n).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand n), x ^^^ BitVec.twoPow n (bitOffset y)⟩]
    flags := some (btFlags (StatusFlags.ofRFLAGS s.RFLAGS) x y) }

@[simp] theorem btcMRA32Effect_components (p : BitVec 64) (len n : Nat) (src : BitVec 5)
    (am : AddrMode) (s : RamState) : (btcMRA32Effect p len n src am s).components =
      [.mem (bitStringAddr32 n am src (p + BitVec.ofNat 64 len) s) (n / 8), .flags, .rip] := rfl

theorem btc_m64_r64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (BitRmwPre p am 64 (gprNumber 0 (rexR rex.toBitVec) reg) (4 + am.tail.length))
      (codeRange p (rex :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (btcMREffect p (4 + am.tail.length) 64
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hp, hread, htables⟩ := bitRmw_facts hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := btc_m_r_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _
  · exact btFlags_allows _ _ _ _

theorem btc_m64_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (BitRmwPre p am 64 (gprNumber 0 (rexR rex.toBitVec) reg) (4 + am.tail.length))
      (codeRange p (rex :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (Effect.post (btcMREffect p (4 + am.tail.length) 64
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [btcMREffect_components]; exact mem_components_rmw _ _)
    hpre.code (by simp; omega))
    (btc_m64_r64_effect_step p rex hrex reg am hv hx hb)

theorem btc_m32_r32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (BitRmwPre p am 32 (gprNumber 0 0 reg) (3 + am.tail.length))
      (codeRange p (0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (btcMREffect p (3 + am.tail.length) 32
        (gprNumber 0 0 reg) am) := by
  intro s h hcode hpre
  obtain ⟨hp, hread, htables⟩ := bitRmw_facts hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := btc_m_r_step s h [] (by simp)
    (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) reg am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · exact btFlags_allows _ _ _ _

theorem btc_m32_r32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (BitRmwPre p am 32 (gprNumber 0 0 reg) (3 + am.tail.length))
      (codeRange p (0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (Effect.post (btcMREffect p (3 + am.tail.length) 32
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [btcMREffect_components]; exact mem_components_rmw _ _)
    hpre.code (by simp; omega))
    (btc_m32_r32_effect_step p reg am hv hx hb)

theorem btc_m32_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (BitRmwPre p am 32 (gprNumber 0 (rexR rex.toBitVec) reg) (4 + am.tail.length))
      (codeRange p (rex :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (btcMREffect p (4 + am.tail.length) 32
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hp, hread, htables⟩ := bitRmw_facts hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := btc_m_r_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · exact btFlags_allows _ _ _ _

theorem btc_m32_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (BitRmwPre p am 32 (gprNumber 0 (rexR rex.toBitVec) reg) (4 + am.tail.length))
      (codeRange p (rex :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (Effect.post (btcMREffect p (4 + am.tail.length) 32
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [btcMREffect_components]; exact mem_components_rmw _ _)
    hpre.code (by simp; omega))
    (btc_m32_r32_rex_effect_step p rex hrex reg am hv hx hb)

theorem btc_m16_r16_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (BitRmwPre p am 16 (gprNumber 0 0 reg) (4 + am.tail.length))
      (codeRange p (0x66 :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (btcMREffect p (4 + am.tail.length) 16
        (gprNumber 0 0 reg) am) := by
  intro s h hcode hpre
  obtain ⟨hp, hread, htables⟩ := bitRmw_facts hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := btc_m16_r16_step s h [0x66] (by simpa using scanPrefix_66)
    (by simp)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) reg am hv
    (by exact (AddrContext.osz _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · exact btFlags_allows _ _ _ _

theorem btc_m16_r16_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (BitRmwPre p am 16 (gprNumber 0 0 reg) (4 + am.tail.length))
      (codeRange p (0x66 :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (Effect.post (btcMREffect p (4 + am.tail.length) 16
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [btcMREffect_components]; exact mem_components_rmw _ _)
    hpre.code (by simp; omega))
    (btc_m16_r16_effect_step p reg am hv hx hb)

theorem btc_m16_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (BitRmwPre p am 16 (gprNumber 0 (rexR rex.toBitVec) reg) (5 + am.tail.length))
      (codeRange p (0x66 :: rex :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (btcMREffect p (5 + am.tail.length) 16
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hp, hread, htables⟩ := bitRmw_facts hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := btc_m16_r16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix])
    (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_66_rex _ _ hr]; exact (AddrContext.oszRex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_66_rex _ _ hr]; exact hread)
  simp only [scanContext_66_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · exact btFlags_allows _ _ _ _

theorem btc_m16_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (BitRmwPre p am 16 (gprNumber 0 (rexR rex.toBitVec) reg) (5 + am.tail.length))
      (codeRange p (0x66 :: rex :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (Effect.post (btcMREffect p (5 + am.tail.length) 16
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [btcMREffect_components]; exact mem_components_rmw _ _)
    hpre.code (by simp; omega))
    (btc_m16_r16_rex_effect_step p rex hrex reg am hv hx hb)

theorem btc_m64_r64_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegBitRmwPre p r base am 64 (gprNumber 0 (rexR rex.toBitVec) reg) (5 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (btcMRSegEffect p (5 + am.tail.length) 64 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segBitRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := btc_m_r_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix))
    (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _
  · exact btFlags_allows _ _ _ _

theorem btc_m64_r64_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegBitRmwPre p r base am 64 (gprNumber 0 (rexR rex.toBitVec) reg) (5 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (Effect.post (btcMRSegEffect p (5 + am.tail.length) 64 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [btcMRSegEffect_components]; exact mem_components_rmw _ _)
    hpre.store.code (by simp; omega))
    (btc_m64_r64_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem btc_m32_r32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SegBitRmwPre p r base am 32 (gprNumber 0 0 reg) (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (btcMRSegEffect p (4 + am.tail.length) 32 base
        (gprNumber 0 0 reg) am) := by
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segBitRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := btc_m_r_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp))
    (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · exact btFlags_allows _ _ _ _

theorem btc_m32_r32_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegBitRmwPre p r base am 32 (gprNumber 0 0 reg) (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (Effect.post (btcMRSegEffect p (4 + am.tail.length) 32 base
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [btcMRSegEffect_components]; exact mem_components_rmw _ _)
    hpre.store.code (by simp; omega))
    (btc_m32_r32_seg_effect_step p r base reg am hv hx hb)

theorem btc_m32_r32_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegBitRmwPre p r base am 32 (gprNumber 0 (rexR rex.toBitVec) reg) (5 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (btcMRSegEffect p (5 + am.tail.length) 32 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segBitRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := btc_m_r_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix))
    (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · exact btFlags_allows _ _ _ _

theorem btc_m32_r32_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegBitRmwPre p r base am 32 (gprNumber 0 (rexR rex.toBitVec) reg) (5 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (Effect.post (btcMRSegEffect p (5 + am.tail.length) 32 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [btcMRSegEffect_components]; exact mem_components_rmw _ _)
    hpre.store.code (by simp; omega))
    (btc_m32_r32_rex_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem btc_m16_r16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SegBitRmwPre p r base am 16 (gprNumber 0 0 reg) (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (btcMRSegEffect p (5 + am.tail.length) 16 base
        (gprNumber 0 0 reg) am) := by
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segBitRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66]
      (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := btc_m16_r16_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66))
    (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · exact btFlags_allows _ _ _ _

theorem btc_m16_r16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegBitRmwPre p r base am 16 (gprNumber 0 0 reg) (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (Effect.post (btcMRSegEffect p (5 + am.tail.length) 16 base
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [btcMRSegEffect_components]; exact mem_components_rmw _ _)
    hpre.store.code (by simp; omega))
    (btc_m16_r16_seg_effect_step p r base reg am hv hx hb)

theorem btc_m16_r16_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegBitRmwPre p r base am 16 (gprNumber 0 (rexR rex.toBitVec) reg) (6 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (btcMRSegEffect p (6 + am.tail.length) 16 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segBitRmw_facts hpre
  subst hp hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66, rex] =
      withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66, rex]
      (noSegPrefix_cons noSegPrefix_66 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_66_rex _ _ hr]
  have hstep := btc_m16_r16_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix]))
    (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · exact btFlags_allows _ _ _ _

theorem btc_m16_r16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegBitRmwPre p r base am 16 (gprNumber 0 (rexR rex.toBitVec) reg) (6 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (Effect.post (btcMRSegEffect p (6 + am.tail.length) 16 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [btcMRSegEffect_components]; exact mem_components_rmw _ _)
    hpre.store.code (by simp; omega))
    (btc_m16_r16_rex_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem btc_m64_r64_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (BitRmw32Pre p am 64 (gprNumber 0 (rexR rex.toBitVec) reg) (5 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (btcMRA32Effect p (5 + am.tail.length) 64
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hp, hread, htables⟩ := bitRmw32_facts hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := btc_m_r_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix))
    (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _
  · exact btFlags_allows _ _ _ _

theorem btc_m64_r64_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (BitRmw32Pre p am 64 (gprNumber 0 (rexR rex.toBitVec) reg) (5 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (Effect.post (btcMRA32Effect p (5 + am.tail.length) 64
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [btcMRA32Effect_components]; exact mem_components_rmw _ _)
    hpre.code (by simp; omega))
    (btc_m64_r64_a32_effect_step p rex hrex reg am hv hx hb)

theorem btc_m32_r32_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (BitRmw32Pre p am 32 (gprNumber 0 0 reg) (4 + am.tail.length))
      (codeRange p (0x67 :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (btcMRA32Effect p (4 + am.tail.length) 32
        (gprNumber 0 0 reg) am) := by
  intro s h hcode hpre
  obtain ⟨hp, hread, htables⟩ := bitRmw32_facts hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := btc_m_r_a32_step s h [0x67] (scanPrefix_asz_cons (by simp))
    (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · exact btFlags_allows _ _ _ _

theorem btc_m32_r32_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (BitRmw32Pre p am 32 (gprNumber 0 0 reg) (4 + am.tail.length))
      (codeRange p (0x67 :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (Effect.post (btcMRA32Effect p (4 + am.tail.length) 32
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [btcMRA32Effect_components]; exact mem_components_rmw _ _)
    hpre.code (by simp; omega))
    (btc_m32_r32_a32_effect_step p reg am hv hx hb)

theorem btc_m32_r32_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (BitRmw32Pre p am 32 (gprNumber 0 (rexR rex.toBitVec) reg) (5 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (btcMRA32Effect p (5 + am.tail.length) 32
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hp, hread, htables⟩ := bitRmw32_facts hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := btc_m_r_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix))
    (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · exact btFlags_allows _ _ _ _

theorem btc_m32_r32_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (BitRmw32Pre p am 32 (gprNumber 0 (rexR rex.toBitVec) reg) (5 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (Effect.post (btcMRA32Effect p (5 + am.tail.length) 32
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [btcMRA32Effect_components]; exact mem_components_rmw _ _)
    hpre.code (by simp; omega))
    (btc_m32_r32_rex_a32_effect_step p rex hrex reg am hv hx hb)

theorem btc_m16_r16_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (BitRmw32Pre p am 16 (gprNumber 0 0 reg) (5 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (btcMRA32Effect p (5 + am.tail.length) 16
        (gprNumber 0 0 reg) am) := by
  intro s h hcode hpre
  obtain ⟨hp, hread, htables⟩ := bitRmw32_facts hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66]) := by
    rw [scanContext_asz_cons]
  have hstep := btc_m16_r16_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66))
    (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · exact btFlags_allows _ _ _ _

theorem btc_m16_r16_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (BitRmw32Pre p am 16 (gprNumber 0 0 reg) (5 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (Effect.post (btcMRA32Effect p (5 + am.tail.length) 16
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [btcMRA32Effect_components]; exact mem_components_rmw _ _)
    hpre.code (by simp; omega))
    (btc_m16_r16_a32_effect_step p reg am hv hx hb)

theorem btc_m16_r16_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (BitRmw32Pre p am 16 (gprNumber 0 (rexR rex.toBitVec) reg) (6 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (btcMRA32Effect p (6 + am.tail.length) 16
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hp, hread, htables⟩ := bitRmw32_facts hpre
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, rex] =
      withAsz (oszRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_66_rex _ _ hr]
  have hstep := btc_m16_r16_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix]))
    (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _
  · exact btFlags_allows _ _ _ _

theorem btc_m16_r16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (BitRmw32Pre p am 16 (gprNumber 0 (rexR rex.toBitVec) reg) (6 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: 0xBB :: am.modrm reg :: am.tail))
      (Effect.post (btcMRA32Effect p (6 + am.tail.length) 16
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [btcMRA32Effect_components]; exact mem_components_rmw _ _)
    hpre.code (by simp; omega))
    (btc_m16_r16_rex_a32_effect_step p rex hrex reg am hv hx hb)

theorem btc_m64_r64_triple [Bindings] (p : BitVec 64) (src : BitVec 4)
    (am : AddrMode) (hv : am.Valid) :
    Triple (BitRmwPre p am 64 (src.setWidth 5) (4 + am.tail.length))
      (codeRange p (encodeBtcM64R64 src am))
      (Effect.post (btcMREffect p (4 + am.tail.length) 64 (src.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := btc_m64_r64_triple_of_bytes p _ hrex (regLow src) am hv hx hb
  rwa [hr, gprNumber_reg] at this

theorem btc_m32_r32_triple [Bindings] (p : BitVec 64) (src : BitVec 4)
    (am : AddrMode) (hv : am.Valid) :
    Triple (BitRmwPre p am 32 (src.setWidth 5) (encodeBtcM32R32 src am).length)
      (codeRange p (encodeBtcM32R32 src am))
      (Effect.post (btcMREffect p (encodeBtcM32R32 src am).length 32
        (src.setWidth 5) am)) := by
  unfold encodeBtcM32R32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := btc_m32_r32_triple_of_bytes p (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := btc_m32_r32_rex_triple_of_bytes p _ hrex (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem btc_m16_r16_triple [Bindings] (p : BitVec 64) (src : BitVec 4)
    (am : AddrMode) (hv : am.Valid) :
    Triple (BitRmwPre p am 16 (src.setWidth 5) (encodeBtcM16R16 src am).length)
      (codeRange p (encodeBtcM16R16 src am))
      (Effect.post (btcMREffect p (encodeBtcM16R16 src am).length 16
        (src.setWidth 5) am)) := by
  unfold encodeBtcM16R16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := btc_m16_r16_triple_of_bytes p (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := btc_m16_r16_rex_triple_of_bytes p _ hrex (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

theorem btc_m64_r64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) (src : BitVec 4)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegBitRmwPre p r base am 64 (src.setWidth 5) (5 + am.tail.length))
      (codeRange p (r.prefixByte :: encodeBtcM64R64 src am))
      (Effect.post (btcMRSegEffect p (5 + am.tail.length) 64 base (src.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := btc_m64_r64_seg_triple_of_bytes p r base _ hrex (regLow src) am hv hx hb
  rwa [hr, gprNumber_reg] at this

theorem btc_m32_r32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) (src : BitVec 4)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegBitRmwPre p r base am 32 (src.setWidth 5) (r.prefixByte :: encodeBtcM32R32 src am).length)
      (codeRange p (r.prefixByte :: encodeBtcM32R32 src am))
      (Effect.post (btcMRSegEffect p (r.prefixByte :: encodeBtcM32R32 src am).length 32 base
        (src.setWidth 5) am)) := by
  unfold encodeBtcM32R32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := btc_m32_r32_seg_triple_of_bytes p r base (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := btc_m32_r32_rex_seg_triple_of_bytes p r base _ hrex (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

theorem btc_m16_r16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) (src : BitVec 4)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegBitRmwPre p r base am 16 (src.setWidth 5) (r.prefixByte :: encodeBtcM16R16 src am).length)
      (codeRange p (r.prefixByte :: encodeBtcM16R16 src am))
      (Effect.post (btcMRSegEffect p (r.prefixByte :: encodeBtcM16R16 src am).length 16 base
        (src.setWidth 5) am)) := by
  unfold encodeBtcM16R16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := btc_m16_r16_seg_triple_of_bytes p r base (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := btc_m16_r16_rex_seg_triple_of_bytes p r base _ hrex (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 + 1 = 6 + am.tail.length by omega]

theorem btc_m64_r64_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4)
    (am : AddrMode) (hv : am.Valid) :
    Triple (BitRmw32Pre p am 64 (src.setWidth 5) (5 + am.tail.length))
      (codeRange p (0x67 :: encodeBtcM64R64 src am))
      (Effect.post (btcMRA32Effect p (5 + am.tail.length) 64 (src.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := btc_m64_r64_a32_triple_of_bytes p _ hrex (regLow src) am hv hx hb
  rwa [hr, gprNumber_reg] at this

theorem btc_m32_r32_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4)
    (am : AddrMode) (hv : am.Valid) :
    Triple (BitRmw32Pre p am 32 (src.setWidth 5) (0x67 :: encodeBtcM32R32 src am).length)
      (codeRange p (0x67 :: encodeBtcM32R32 src am))
      (Effect.post (btcMRA32Effect p (0x67 :: encodeBtcM32R32 src am).length 32
        (src.setWidth 5) am)) := by
  unfold encodeBtcM32R32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := btc_m32_r32_a32_triple_of_bytes p (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := btc_m32_r32_rex_a32_triple_of_bytes p _ hrex (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

theorem btc_m16_r16_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4)
    (am : AddrMode) (hv : am.Valid) :
    Triple (BitRmw32Pre p am 16 (src.setWidth 5) (0x67 :: encodeBtcM16R16 src am).length)
      (codeRange p (0x67 :: encodeBtcM16R16 src am))
      (Effect.post (btcMRA32Effect p (0x67 :: encodeBtcM16R16 src am).length 16
        (src.setWidth 5) am)) := by
  unfold encodeBtcM16R16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := btc_m16_r16_a32_triple_of_bytes p (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := btc_m16_r16_rex_a32_triple_of_bytes p _ hrex (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 + 1 = 6 + am.tail.length by omega]

attribute [x86_compose] btcMREffect

theorem btcMREffect_local {p : BitVec 64} {len n : Nat} {src : BitVec 5} {am : AddrMode}
    (hn : n % 8 = 0) :
    Effect.Local (btcMREffect p len n src am) := by
  effect_local [btcMREffect, bitStringAddr, btFlags, hn]

@[x86_local] theorem btcMREffect_local64 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} : Effect.Local (btcMREffect p len 64 src am) :=
  btcMREffect_local (by decide)

@[x86_local] theorem btcMREffect_local32 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} : Effect.Local (btcMREffect p len 32 src am) :=
  btcMREffect_local (by decide)

@[x86_local] theorem btcMREffect_local16 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} : Effect.Local (btcMREffect p len 16 src am) :=
  btcMREffect_local (by decide)

attribute [x86_compose] btcMRSegEffect

theorem btcMRSegEffect_local {p : BitVec 64} {len n : Nat} {base : BitVec 64} {src : BitVec 5} {am : AddrMode}
    (hn : n % 8 = 0) :
    Effect.Local (btcMRSegEffect p len n base src am) := by
  effect_local [btcMRSegEffect, bitStringAddr, btFlags, hn]

@[x86_local] theorem btcMRSegEffect_local64 {p : BitVec 64} {len : Nat} {base : BitVec 64} {src : BitVec 5}
    {am : AddrMode} : Effect.Local (btcMRSegEffect p len 64 base src am) :=
  btcMRSegEffect_local (by decide)

@[x86_local] theorem btcMRSegEffect_local32 {p : BitVec 64} {len : Nat} {base : BitVec 64} {src : BitVec 5}
    {am : AddrMode} : Effect.Local (btcMRSegEffect p len 32 base src am) :=
  btcMRSegEffect_local (by decide)

@[x86_local] theorem btcMRSegEffect_local16 {p : BitVec 64} {len : Nat} {base : BitVec 64} {src : BitVec 5}
    {am : AddrMode} : Effect.Local (btcMRSegEffect p len 16 base src am) :=
  btcMRSegEffect_local (by decide)

attribute [x86_compose] btcMRA32Effect

theorem btcMRA32Effect_local {p : BitVec 64} {len n : Nat} {src : BitVec 5} {am : AddrMode}
    (hn : n % 8 = 0) :
    Effect.Local (btcMRA32Effect p len n src am) := by
  effect_local [btcMRA32Effect, bitStringAddr32, bitStringAddr, btFlags, hn]

@[x86_local] theorem btcMRA32Effect_local64 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} : Effect.Local (btcMRA32Effect p len 64 src am) :=
  btcMRA32Effect_local (by decide)

@[x86_local] theorem btcMRA32Effect_local32 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} : Effect.Local (btcMRA32Effect p len 32 src am) :=
  btcMRA32Effect_local (by decide)

@[x86_local] theorem btcMRA32Effect_local16 {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} : Effect.Local (btcMRA32Effect p len 16 src am) :=
  btcMRA32Effect_local (by decide)

end X86Proofs
