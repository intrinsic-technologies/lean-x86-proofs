import X86Proofs.Instructions.Test.Generated.M8R8.Step
import X86Proofs.Instructions.Test.Generated.M8R8.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Test.Generated.MR.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def testM8R8NoRexEffect (p : BitVec 64) (len : Nat) (src : BitVec 3) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := am.addr s (p + BitVec.ofNat 64 len)
  let r := (Operand.mem a : Operand 8).read s &&& (Operand.byteReg src).read s
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (testFlags r) }

@[simp] theorem testM8R8NoRexEffect_components (p : BitVec 64) (len : Nat) (src : BitVec 3)
    (am : AddrMode) (s : RamState) : (testM8R8NoRexEffect p len src am s).components =
      [.flags, .rip] := rfl

def testM8R8NoRexSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (src : BitVec 3)
    (am : AddrMode) (s : RamState) : Effect :=
  let a := base + am.addr s (p + BitVec.ofNat 64 len)
  let r := (Operand.mem a : Operand 8).read s &&& (Operand.byteReg src).read s
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (testFlags r) }

@[simp] theorem testM8R8NoRexSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (src : BitVec 3) (am : AddrMode) (s : RamState) :
    (testM8R8NoRexSegEffect p len base src am s).components =
      [.flags, .rip] := rfl

theorem test_m8_r8_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 1)
      (codeRange p (0x84 :: am.modrm reg :: am.tail))
      (testMREffect p (2 + am.tail.length) 8
        (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := test_m8_r8_step s h [] (by simp) (by simp)
    (by rfl) (by rfl)
    (by rfl) reg
    (.inr (by exact gprNumber_low4 reg hreg)) am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_m8_r8_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 1)
      (codeRange p (0x84 :: am.modrm reg :: am.tail))
      (Effect.post (testMREffect p (2 + am.tail.length) 8
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testMREffect_components]; simp [Component.Covers]) _)
    (test_m8_r8_effect_step p reg hreg am hv hx hb)

theorem test_m8_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (rex :: 0x84 :: am.modrm reg :: am.tail))
      (testMREffect p (3 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := test_m8_r8_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg
    (.inl (by rw [scanContext_rex _ _ hr]; rfl)) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_m8_r8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (rex :: 0x84 :: am.modrm reg :: am.tail))
      (Effect.post (testMREffect p (3 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testMREffect_components]; simp [Component.Covers]) _)
    (test_m8_r8_rex_effect_step p rex hr reg am hv hx hb)

theorem test_m8_r8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: 0x84 :: am.modrm reg :: am.tail))
      (testMRSegEffect p (3 + am.tail.length) 8 base
        (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
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
  have hstep := test_m8_r8_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inr (by rw [hsc]; exact gprNumber_low4 reg hreg)) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_m8_r8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: 0x84 :: am.modrm reg :: am.tail))
      (Effect.post (testMRSegEffect p (3 + am.tail.length) 8 base
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testMRSegEffect_components]; simp [Component.Covers]) _)
    (test_m8_r8_seg_effect_step p r base reg hreg am hv hx hb)

theorem test_m8_r8_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: rex :: 0x84 :: am.modrm reg :: am.tail))
      (testMRSegEffect p (4 + am.tail.length) 8 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
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
  have hstep := test_m8_r8_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inl (by rw [hsc]; rfl)) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_m8_r8_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: rex :: 0x84 :: am.modrm reg :: am.tail))
      (Effect.post (testMRSegEffect p (4 + am.tail.length) 8 base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testMRSegEffect_components]; simp [Component.Covers]) _)
    (test_m8_r8_rex_seg_effect_step p r base rex hr reg am hv hx hb)

theorem test_m8_r8_norex_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 1)
      (codeRange p (0x84 :: am.modrm reg :: am.tail))
      (testM8R8NoRexEffect p (2 + am.tail.length)
        reg am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := test_m8_r8_gpr8_step s h [] (by simp) (by simp)
    (by rfl) (by rfl)
    (by rfl) reg am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_m8_r8_norex_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 1)
      (codeRange p (0x84 :: am.modrm reg :: am.tail))
      (Effect.post (testM8R8NoRexEffect p (2 + am.tail.length)
        reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testM8R8NoRexEffect_components]; simp [Component.Covers]) _)
    (test_m8_r8_norex_effect_step p reg am hv hx hb)

theorem test_m8_r8_norex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: 0x84 :: am.modrm reg :: am.tail))
      (testM8R8NoRexSegEffect p (3 + am.tail.length) base
        reg am) := by
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
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
  have hstep := test_m8_r8_gpr8_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_m8_r8_norex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: 0x84 :: am.modrm reg :: am.tail))
      (Effect.post (testM8R8NoRexSegEffect p (3 + am.tail.length) base
        reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testM8R8NoRexSegEffect_components]; simp [Component.Covers]) _)
    (test_m8_r8_norex_seg_effect_step p r base reg am hv hx hb)

theorem test_m8_r8_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (encodeTestM8R8 src am).length)) 1)
      (codeRange p (encodeTestM8R8 src am))
      (Effect.post (testMREffect p (encodeTestM8R8 src am).length 8 (src.setWidth 5) am)) := by
  unfold encodeTestM8R8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec src hs
    have := test_m8_r8_triple_of_bytes p (regLow src) hl am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 = 2 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := test_m8_r8_rex_triple_of_bytes p _ hrex.rexPrefix (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]

theorem test_m8_r8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeTestM8R8 src am).length)) 1)
      (codeRange p (r.prefixByte :: encodeTestM8R8 src am))
      (Effect.post (testMRSegEffect p (r.prefixByte :: encodeTestM8R8 src am).length 8 base
        (src.setWidth 5) am)) := by
  unfold encodeTestM8R8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec src hs
    have := test_m8_r8_seg_triple_of_bytes p r base (regLow src) hl am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := test_m8_r8_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix (regLow src) am hv
      hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem test_m8_r8_norex_triple [Bindings] (p : BitVec 64) (src : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 1)
      (codeRange p (encodeTestM8R8NoRex src am))
      (Effect.post (testM8R8NoRexEffect p (2 + am.tail.length) src am)) :=
  test_m8_r8_norex_triple_of_bytes p src am hv hx hb

theorem test_m8_r8_norex_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: encodeTestM8R8NoRex src am))
      (Effect.post (testM8R8NoRexSegEffect p (3 + am.tail.length) base src am)) :=
  test_m8_r8_norex_seg_triple_of_bytes p r base src am hv hx hb

attribute [x86_compose] testM8R8NoRexEffect testM8R8NoRexSegEffect

@[x86_local] theorem testM8R8NoRexEffect_local {p : BitVec 64} {len : Nat} {src : BitVec 3}
    {am : AddrMode} : Effect.Local (testM8R8NoRexEffect p len src am) := by
  effect_local [testM8R8NoRexEffect]

@[x86_local] theorem testM8R8NoRexSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 3} {am : AddrMode} :
    Effect.Local (testM8R8NoRexSegEffect p len base src am) := by
  effect_local [testM8R8NoRexSegEffect]

def testM8R8NoRexA32Effect (p : BitVec 64) (len : Nat) (src : BitVec 3) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := am.addr32 s (p + BitVec.ofNat 64 len)
  let r := (Operand.mem a : Operand 8).read s &&& (Operand.byteReg src).read s
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (testFlags r) }

@[simp] theorem testM8R8NoRexA32Effect_components (p : BitVec 64) (len : Nat) (src : BitVec 3)
    (am : AddrMode) (s : RamState) : (testM8R8NoRexA32Effect p len src am s).components =
      [.flags, .rip] := rfl

theorem test_m8_r8_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (0x67 :: 0x84 :: am.modrm reg :: am.tail))
      (testMRA32Effect p (3 + am.tail.length) 8
        (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := test_m8_r8_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inr (by rw [hsc]; exact gprNumber_low4 reg hreg)) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_m8_r8_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (0x67 :: 0x84 :: am.modrm reg :: am.tail))
      (Effect.post (testMRA32Effect p (3 + am.tail.length) 8
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testMRA32Effect_components]; simp [Component.Covers]) _)
    (test_m8_r8_a32_effect_step p reg hreg am hv hx hb)

theorem test_m8_r8_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (0x67 :: rex :: 0x84 :: am.modrm reg :: am.tail))
      (testMRA32Effect p (4 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := test_m8_r8_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg
    (.inl (by rw [hsc]; rfl)) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_m8_r8_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (0x67 :: rex :: 0x84 :: am.modrm reg :: am.tail))
      (Effect.post (testMRA32Effect p (4 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testMRA32Effect_components]; simp [Component.Covers]) _)
    (test_m8_r8_rex_a32_effect_step p rex hr reg am hv hx hb)

theorem test_m8_r8_norex_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (0x67 :: 0x84 :: am.modrm reg :: am.tail))
      (testM8R8NoRexA32Effect p (3 + am.tail.length)
        reg am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := test_m8_r8_gpr8_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_m8_r8_norex_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (0x67 :: 0x84 :: am.modrm reg :: am.tail))
      (Effect.post (testM8R8NoRexA32Effect p (3 + am.tail.length)
        reg am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [testM8R8NoRexA32Effect_components]; simp [Component.Covers]) _)
    (test_m8_r8_norex_a32_effect_step p reg am hv hx hb)

theorem test_m8_r8_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeTestM8R8 src am).length)) 1)
      (codeRange p (0x67 :: encodeTestM8R8 src am))
      (Effect.post (testMRA32Effect p (0x67 :: encodeTestM8R8 src am).length 8 (src.setWidth 5) am)) := by
  unfold encodeTestM8R8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec src hs
    have := test_m8_r8_a32_triple_of_bytes p (regLow src) hl am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := test_m8_r8_rex_a32_triple_of_bytes p _ hrex.rexPrefix (regLow src) am hv
      hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem test_m8_r8_norex_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (0x67 :: encodeTestM8R8NoRex src am))
      (Effect.post (testM8R8NoRexA32Effect p (3 + am.tail.length) src am)) :=
  test_m8_r8_norex_a32_triple_of_bytes p src am hv hx hb

attribute [x86_compose] testM8R8NoRexA32Effect

@[x86_local] theorem testM8R8NoRexA32Effect_local {p : BitVec 64} {len : Nat} {src : BitVec 3}
    {am : AddrMode} : Effect.Local (testM8R8NoRexA32Effect p len src am) := by
  effect_local [testM8R8NoRexA32Effect]

end X86Proofs
