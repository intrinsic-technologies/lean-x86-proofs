import X86Proofs.Instructions.Cmp.Generated.M8Imm8.Step
import X86Proofs.Instructions.Cmp.Generated.M8Imm8.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cmpM8Imm8Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    Effect :=
  { rip := p + BitVec.ofNat 64 len
    flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) :
      Operand 8).read s) imm)) }

@[simp] theorem cmpM8Imm8Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) : (cmpM8Imm8Effect p len am imm s).components =
      [.flags, .rip] := rfl

def cmpM8Imm8SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) :
      Operand 8).read s) imm)) }

@[simp] theorem cmpM8Imm8SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) : (cmpM8Imm8SegEffect p len base am imm s).components =
      [.flags, .rip] := rfl

def cmpM8Imm8A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    Effect :=
  { rip := p + BitVec.ofNat 64 len
    flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) :
      Operand 8).read s) imm)) }

@[simp] theorem cmpM8Imm8A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) : (cmpM8Imm8A32Effect p len am imm s).components =
      [.flags, .rip] := rfl

theorem cmp_m8_imm8_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : UInt8) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (0x80 :: am.modrm 7 :: (am.tail ++ [imm])))
      (cmpM8Imm8Effect p (3 + am.tail.length) am imm.toBitVec) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append] at this
    omega
  have hstep := cmp_m8_imm8_step s h [] (by simp) (by simp)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by exact hread)
  simp only [BitVec.signExtend_eq] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_m8_imm8_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : UInt8) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (0x80 :: am.modrm 7 :: (am.tail ++ [imm])))
      (Effect.post (cmpM8Imm8Effect p (3 + am.tail.length) am imm.toBitVec)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpM8Imm8Effect_components]; simp [Component.Covers]) _)
    (cmp_m8_imm8_effect_step p am hv hx hb imm)

theorem cmp_m8_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : UInt8) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (rex :: 0x80 :: am.modrm 7 :: (am.tail ++ [imm])))
      (cmpM8Imm8Effect p (4 + am.tail.length) am imm.toBitVec) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append] at this
    omega
  have hstep := cmp_m8_imm8_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr, BitVec.signExtend_eq] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_m8_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : UInt8) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (rex :: 0x80 :: am.modrm 7 :: (am.tail ++ [imm])))
      (Effect.post (cmpM8Imm8Effect p (4 + am.tail.length) am imm.toBitVec)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpM8Imm8Effect_components]; simp [Component.Covers]) _)
    (cmp_m8_imm8_rex_effect_step p rex hr am hv hx hb imm)

theorem cmp_m8_imm8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : UInt8) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: 0x80 :: am.modrm 7 :: (am.tail ++ [imm])))
      (cmpM8Imm8SegEffect p (4 + am.tail.length) base am imm.toBitVec) := by
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := cmp_m8_imm8_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg, BitVec.signExtend_eq] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_m8_imm8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : UInt8) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: 0x80 :: am.modrm 7 :: (am.tail ++ [imm])))
      (Effect.post (cmpM8Imm8SegEffect p (4 + am.tail.length) base am imm.toBitVec)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpM8Imm8SegEffect_components]; simp [Component.Covers]) _)
    (cmp_m8_imm8_seg_effect_step p r base am hv hx hb imm)

theorem cmp_m8_imm8_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : UInt8) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: rex :: 0x80 :: am.modrm 7 :: (am.tail ++ [imm])))
      (cmpM8Imm8SegEffect p (5 + am.tail.length) base am imm.toBitVec) := by
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := cmp_m8_imm8_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg, BitVec.signExtend_eq] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_m8_imm8_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : UInt8) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: rex :: 0x80 :: am.modrm 7 :: (am.tail ++ [imm])))
      (Effect.post (cmpM8Imm8SegEffect p (5 + am.tail.length) base am imm.toBitVec)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpM8Imm8SegEffect_components]; simp [Component.Covers]) _)
    (cmp_m8_imm8_rex_seg_effect_step p r base rex hr am hv hx hb imm)

theorem cmp_m8_imm8_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : UInt8) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (0x67 :: 0x80 :: am.modrm 7 :: (am.tail ++ [imm])))
      (cmpM8Imm8A32Effect p (4 + am.tail.length) am imm.toBitVec) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := cmp_m8_imm8_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc, BitVec.signExtend_eq] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_m8_imm8_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : UInt8) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (0x67 :: 0x80 :: am.modrm 7 :: (am.tail ++ [imm])))
      (Effect.post (cmpM8Imm8A32Effect p (4 + am.tail.length) am imm.toBitVec)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpM8Imm8A32Effect_components]; simp [Component.Covers]) _)
    (cmp_m8_imm8_a32_effect_step p am hv hx hb imm)

theorem cmp_m8_imm8_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : UInt8) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 1)
      (codeRange p (0x67 :: rex :: 0x80 :: am.modrm 7 :: (am.tail ++ [imm])))
      (cmpM8Imm8A32Effect p (5 + am.tail.length) am imm.toBitVec) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := cmp_m8_imm8_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc, BitVec.signExtend_eq] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_m8_imm8_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : UInt8) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 1)
      (codeRange p (0x67 :: rex :: 0x80 :: am.modrm 7 :: (am.tail ++ [imm])))
      (Effect.post (cmpM8Imm8A32Effect p (5 + am.tail.length) am imm.toBitVec)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpM8Imm8A32Effect_components]; simp [Component.Covers]) _)
    (cmp_m8_imm8_rex_a32_effect_step p rex hr am hv hx hb imm)

theorem cmp_m8_imm8_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (encodeCmpM8Imm8 am imm))
      (Effect.post (cmpM8Imm8Effect p (3 + am.tail.length) am imm)) :=
  cmp_m8_imm8_triple_of_bytes p am hv hx hb (UInt8.ofBitVec imm)

theorem cmp_m8_imm8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: encodeCmpM8Imm8 am imm))
      (Effect.post (cmpM8Imm8SegEffect p (4 + am.tail.length) base am imm)) :=
  cmp_m8_imm8_seg_triple_of_bytes p r base am hv hx hb (UInt8.ofBitVec imm)

theorem cmp_m8_imm8_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (0x67 :: encodeCmpM8Imm8 am imm))
      (Effect.post (cmpM8Imm8A32Effect p (4 + am.tail.length) am imm)) :=
  cmp_m8_imm8_a32_triple_of_bytes p am hv hx hb (UInt8.ofBitVec imm)

attribute [x86_compose] cmpM8Imm8Effect
  cmpM8Imm8SegEffect
  cmpM8Imm8A32Effect

@[x86_local] theorem cmpM8Imm8Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode}
    {imm8 : BitVec 8} :
    Effect.Local (cmpM8Imm8Effect p len am imm8) := by
  effect_local [cmpM8Imm8Effect]

@[x86_local] theorem cmpM8Imm8SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} {am : AddrMode}
    {imm8 : BitVec 8} :
    Effect.Local (cmpM8Imm8SegEffect p len base am imm8) := by
  effect_local [cmpM8Imm8SegEffect]

@[x86_local] theorem cmpM8Imm8A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode}
    {imm8 : BitVec 8} :
    Effect.Local (cmpM8Imm8A32Effect p len am imm8) := by
  effect_local [cmpM8Imm8A32Effect]

end X86Proofs
