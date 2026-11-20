import X86Proofs.Instructions.Mul.Generated.M8.Step
import X86Proofs.Instructions.Mul.Generated.M8.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def mulM8Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 8).read s
  let a := (Operand.reg 0 : Operand 8).read s
  let r := mulResult a b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 16 (r.2 ++ r.1) ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (mulFlags a b) }

@[simp] theorem mulM8Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) :
    (mulM8Effect p len am s).components = [.reg 0, .flags, .rip] := rfl

def mulM8SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) (s : RamState) :
    Effect :=
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 8).read s
  let a := (Operand.reg 0 : Operand 8).read s
  let r := mulResult a b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 16 (r.2 ++ r.1) ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (mulFlags a b) }

@[simp] theorem mulM8SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (s : RamState) : (mulM8SegEffect p len base am s).components = [.reg 0, .flags, .rip] := rfl

def mulM8A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 8).read s
  let a := (Operand.reg 0 : Operand 8).read s
  let r := mulResult a b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 16 (r.2 ++ r.1) ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (mulFlags a b) }

@[simp] theorem mulM8A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (s : RamState) : (mulM8A32Effect p len am s).components = [.reg 0, .flags, .rip] := rfl

theorem mul_m8_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 1)
      (codeRange p (0xF6 :: am.modrm 4 :: am.tail))
      (mulM8Effect p (2 + am.tail.length) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := mul_m8_step s h [] (by simp) (by simp)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ 4 _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ 4 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_writeOutputs_self_merge]
    simp only [mulSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact mulFlags_allows _ _ _

theorem mul_m8_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 1)
      (codeRange p (0xF6 :: am.modrm 4 :: am.tail))
      (Effect.post (mulM8Effect p (2 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [mulM8Effect_components]; simp [Component.Covers]) _)
    (mul_m8_effect_step p am hv hx hb)

theorem mul_m8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (rex :: 0xF6 :: am.modrm 4 :: am.tail))
      (mulM8Effect p (3 + am.tail.length) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := mul_m8_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ 4 _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ 4 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_writeOutputs_self_merge]
    simp only [mulSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact mulFlags_allows _ _ _

theorem mul_m8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (rex :: 0xF6 :: am.modrm 4 :: am.tail))
      (Effect.post (mulM8Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [mulM8Effect_components]; simp [Component.Covers]) _)
    (mul_m8_rex_effect_step p rex hr am hv hx hb)

theorem mul_m8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: 0xF6 :: am.modrm 4 :: am.tail))
      (mulM8SegEffect p (3 + am.tail.length) base am) := by
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
  have hstep := mul_m8_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ 4 _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ 4 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_writeOutputs_self_merge]
    simp only [mulSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact mulFlags_allows _ _ _

theorem mul_m8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: 0xF6 :: am.modrm 4 :: am.tail))
      (Effect.post (mulM8SegEffect p (3 + am.tail.length) base am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [mulM8SegEffect_components]; simp [Component.Covers]) _)
    (mul_m8_seg_effect_step p r base am hv hx hb)

theorem mul_m8_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: rex :: 0xF6 :: am.modrm 4 :: am.tail))
      (mulM8SegEffect p (4 + am.tail.length) base am) := by
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
  have hstep := mul_m8_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ 4 _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ 4 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_writeOutputs_self_merge]
    simp only [mulSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact mulFlags_allows _ _ _

theorem mul_m8_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: rex :: 0xF6 :: am.modrm 4 :: am.tail))
      (Effect.post (mulM8SegEffect p (4 + am.tail.length) base am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [mulM8SegEffect_components]; simp [Component.Covers]) _)
    (mul_m8_rex_seg_effect_step p r base rex hr am hv hx hb)

theorem mul_m8_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (0x67 :: 0xF6 :: am.modrm 4 :: am.tail))
      (mulM8A32Effect p (3 + am.tail.length) am) := by
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
  have hstep := mul_m8_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ 4 _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ 4 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_writeOutputs_self_merge]
    simp only [mulSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact mulFlags_allows _ _ _

theorem mul_m8_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (0x67 :: 0xF6 :: am.modrm 4 :: am.tail))
      (Effect.post (mulM8A32Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [mulM8A32Effect_components]; simp [Component.Covers]) _)
    (mul_m8_a32_effect_step p am hv hx hb)

theorem mul_m8_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (0x67 :: rex :: 0xF6 :: am.modrm 4 :: am.tail))
      (mulM8A32Effect p (4 + am.tail.length) am) := by
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
  have hstep := mul_m8_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ 4 _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ 4 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_writeOutputs_self_merge]
    simp only [mulSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact mulFlags_allows _ _ _

theorem mul_m8_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (0x67 :: rex :: 0xF6 :: am.modrm 4 :: am.tail))
      (Effect.post (mulM8A32Effect p (4 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [mulM8A32Effect_components]; simp [Component.Covers]) _)
    (mul_m8_rex_a32_effect_step p rex hr am hv hx hb)

theorem mul_m8_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (encodeMulM8 am).length)) 1)
      (codeRange p (encodeMulM8 am))
      (Effect.post (mulM8Effect p (encodeMulM8 am).length am)) := by
  unfold encodeMulM8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := mul_m8_triple_of_bytes p am hv hx hb
    rwa [show (0xF6 :: am.modrm 4 :: am.tail).length =
      2 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := mul_m8_rex_triple_of_bytes p _ hrex.rexPrefix am hv hx hb
    rwa [show (am.rexByte false 0 :: 0xF6 :: am.modrm 4 :: am.tail).length =
      3 + am.tail.length by simp; omega]

theorem mul_m8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeMulM8 am).length)) 1)
      (codeRange p (r.prefixByte :: encodeMulM8 am))
      (Effect.post (mulM8SegEffect p (r.prefixByte :: encodeMulM8 am).length base
        am)) := by
  unfold encodeMulM8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := mul_m8_seg_triple_of_bytes p r base am hv hx hb
    rwa [show (r.prefixByte :: 0xF6 :: am.modrm 4 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := mul_m8_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix am hv hx hb
    rwa [show (r.prefixByte :: am.rexByte false 0 :: 0xF6 :: am.modrm 4 ::
      am.tail).length = 4 + am.tail.length by simp; omega]

theorem mul_m8_a32_triple [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeMulM8 am).length)) 1)
      (codeRange p (0x67 :: encodeMulM8 am))
      (Effect.post (mulM8A32Effect p (0x67 :: encodeMulM8 am).length
        am)) := by
  unfold encodeMulM8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := mul_m8_a32_triple_of_bytes p am hv hx hb
    rwa [show (0x67 :: 0xF6 :: am.modrm 4 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := mul_m8_rex_a32_triple_of_bytes p _ hrex.rexPrefix am hv hx hb
    rwa [show (0x67 :: am.rexByte false 0 :: 0xF6 :: am.modrm 4 ::
      am.tail).length = 4 + am.tail.length by simp; omega]

attribute [x86_compose] mulM8Effect mulM8SegEffect mulM8A32Effect

@[x86_local] theorem mulM8Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (mulM8Effect p len am) := by
  effect_local [mulM8Effect, mulFlags]

@[x86_local] theorem mulM8SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} : Effect.Local (mulM8SegEffect p len base am) := by
  effect_local [mulM8SegEffect, mulFlags]

@[x86_local] theorem mulM8A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (mulM8A32Effect p len am) := by
  effect_local [mulM8A32Effect, mulFlags]

end X86Proofs
