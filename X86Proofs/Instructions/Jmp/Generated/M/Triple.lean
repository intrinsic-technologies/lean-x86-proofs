import X86Proofs.Instructions.Jmp.Generated.M.Step
import X86Proofs.Instructions.Jmp.Generated.M.Encode
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Program.ReadWrite.Load
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def jmpM64Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Effect :=
  { rip := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s }

@[simp] theorem jmpM64Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (s : RamState) : (jmpM64Effect p len am s).components = [.rip] := rfl

abbrev JmpMemPre (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Prop :=
  LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8 s ∧
    (jmpM64Effect p len am s).rip.toNat < 2^32

def jmpM64SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode)
    (s : RamState) : Effect :=
  { rip := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s }

@[simp] theorem jmpM64SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (s : RamState) : (jmpM64SegEffect p len base am s).components = [.rip] := rfl

abbrev JmpMemSegPre (p : BitVec 64) (len : Nat) (r : SegReg) (base : BitVec 64) (am : AddrMode)
    (s : RamState) : Prop :=
  SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8 s ∧
    (jmpM64SegEffect p len base am s).rip.toNat < 2^32

def jmpM64A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Effect :=
  { rip := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 64).read s }

@[simp] theorem jmpM64A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (s : RamState) : (jmpM64A32Effect p len am s).components = [.rip] := rfl

abbrev JmpMemA32Pre (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Prop :=
  LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 len)) 8 s ∧
    (jmpM64A32Effect p len am s).rip.toNat < 2^32

theorem jmp_m64_effect_step [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (JmpMemPre p (2 + am.tail.length) am) (codeRange p (0xFF :: am.modrm 4 :: am.tail))
      (jmpM64Effect p (2 + am.tail.length) am) := by
  rintro s h hcode ⟨⟨hp, hread⟩, htarget⟩
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := jmp_m64_step s h [] (by simp) (by simp)
    (by rfl)
    (by rfl) (by rfl) am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg) hcode.bytesAt hlow (by exact hread)
    (by exact htarget)
  exact ⟨_, hstep, ReadyToStep.afterStep_jumpLoad h _ _ _,
    ⟨afterStep_jumpLoad_rip _ _ _ _, trivial, trivial, AgreesExcept.afterStep_jumpLoad _ _ _ _⟩⟩

theorem jmp_m64_triple_of_bytes [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (JmpMemPre p (2 + am.tail.length) am) (codeRange p (0xFF :: am.modrm 4 :: am.tail))
      (Effect.post (jmpM64Effect p (2 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [jmpM64Effect_components]; simp [Component.Covers]) _)
    (jmp_m64_effect_step p am hv hx hb)

theorem jmp_m64_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (JmpMemPre p (3 + am.tail.length) am) (codeRange p (rex :: 0xFF :: am.modrm 4 :: am.tail))
      (jmpM64Effect p (3 + am.tail.length) am) := by
  rintro s h hcode ⟨⟨hp, hread⟩, htarget⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := jmp_m64_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg) hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
    (by rw [scanContext_rex _ _ hr]; exact htarget)
  simp only [scanContext_rex _ _ hr] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_jumpLoad h _ _ _,
    ⟨afterStep_jumpLoad_rip _ _ _ _, trivial, trivial, AgreesExcept.afterStep_jumpLoad _ _ _ _⟩⟩

theorem jmp_m64_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (JmpMemPre p (3 + am.tail.length) am) (codeRange p (rex :: 0xFF :: am.modrm 4 :: am.tail))
      (Effect.post (jmpM64Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [jmpM64Effect_components]; simp [Component.Covers]) _)
    (jmp_m64_rex_effect_step p rex hr am hv hx hb)

theorem jmp_m64_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (JmpMemSegPre p (3 + am.tail.length) r base am) (codeRange p (r.prefixByte :: 0xFF :: am.modrm 4 :: am.tail))
      (jmpM64SegEffect p (3 + am.tail.length) base am) := by
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, htarget⟩
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
  have hstep := jmp_m64_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg) hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
    (by rw [hsc, segAddr_withSeg]; exact htarget)
  simp only [hsc, segAddr_withSeg] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_jumpLoad h _ _ _,
    ⟨afterStep_jumpLoad_rip _ _ _ _, trivial, trivial, AgreesExcept.afterStep_jumpLoad _ _ _ _⟩⟩

theorem jmp_m64_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (JmpMemSegPre p (3 + am.tail.length) r base am) (codeRange p (r.prefixByte :: 0xFF :: am.modrm 4 :: am.tail))
      (Effect.post (jmpM64SegEffect p (3 + am.tail.length) base am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [jmpM64SegEffect_components]; simp [Component.Covers]) _)
    (jmp_m64_seg_effect_step p r base am hv hx hb)

theorem jmp_m64_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (JmpMemSegPre p (4 + am.tail.length) r base am) (codeRange p (r.prefixByte :: rex :: 0xFF :: am.modrm 4 :: am.tail))
      (jmpM64SegEffect p (4 + am.tail.length) base am) := by
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, htarget⟩
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
  have hstep := jmp_m64_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg) hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
    (by rw [hsc, segAddr_withSeg]; exact htarget)
  simp only [hsc, segAddr_withSeg] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_jumpLoad h _ _ _,
    ⟨afterStep_jumpLoad_rip _ _ _ _, trivial, trivial, AgreesExcept.afterStep_jumpLoad _ _ _ _⟩⟩

theorem jmp_m64_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (JmpMemSegPre p (4 + am.tail.length) r base am) (codeRange p (r.prefixByte :: rex :: 0xFF :: am.modrm 4 :: am.tail))
      (Effect.post (jmpM64SegEffect p (4 + am.tail.length) base am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [jmpM64SegEffect_components]; simp [Component.Covers]) _)
    (jmp_m64_rex_seg_effect_step p r base rex hr am hv hx hb)

theorem jmp_m64_a32_effect_step [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (JmpMemA32Pre p (3 + am.tail.length) am) (codeRange p (0x67 :: 0xFF :: am.modrm 4 :: am.tail))
      (jmpM64A32Effect p (3 + am.tail.length) am) := by
  rintro s h hcode ⟨⟨hp, hread⟩, htarget⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := jmp_m64_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz) hcode.bytesAt hlow (by rw [hsc]; exact hread)
    (by rw [hsc]; exact htarget)
  simp only [hsc] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_jumpLoad h _ _ _,
    ⟨afterStep_jumpLoad_rip _ _ _ _, trivial, trivial, AgreesExcept.afterStep_jumpLoad _ _ _ _⟩⟩

theorem jmp_m64_a32_triple_of_bytes [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (JmpMemA32Pre p (3 + am.tail.length) am) (codeRange p (0x67 :: 0xFF :: am.modrm 4 :: am.tail))
      (Effect.post (jmpM64A32Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [jmpM64A32Effect_components]; simp [Component.Covers]) _)
    (jmp_m64_a32_effect_step p am hv hx hb)

theorem jmp_m64_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (JmpMemA32Pre p (4 + am.tail.length) am) (codeRange p (0x67 :: rex :: 0xFF :: am.modrm 4 :: am.tail))
      (jmpM64A32Effect p (4 + am.tail.length) am) := by
  rintro s h hcode ⟨⟨hp, hread⟩, htarget⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := jmp_m64_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz) hcode.bytesAt hlow (by rw [hsc]; exact hread)
    (by rw [hsc]; exact htarget)
  simp only [hsc] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_jumpLoad h _ _ _,
    ⟨afterStep_jumpLoad_rip _ _ _ _, trivial, trivial, AgreesExcept.afterStep_jumpLoad _ _ _ _⟩⟩

theorem jmp_m64_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (JmpMemA32Pre p (4 + am.tail.length) am) (codeRange p (0x67 :: rex :: 0xFF :: am.modrm 4 :: am.tail))
      (Effect.post (jmpM64A32Effect p (4 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [jmpM64A32Effect_components]; simp [Component.Covers]) _)
    (jmp_m64_rex_a32_effect_step p rex hr am hv hx hb)

theorem jmp_m64_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (JmpMemPre p (encodeJmpM64 am).length am) (codeRange p (encodeJmpM64 am))
      (Effect.post (jmpM64Effect p (encodeJmpM64 am).length am)) := by
  unfold encodeJmpM64
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := jmp_m64_triple_of_bytes p am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 = 2 + am.tail.length by omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := jmp_m64_rex_triple_of_bytes p _ hrex.rexPrefix am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]

theorem jmp_m64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (JmpMemSegPre p (r.prefixByte :: encodeJmpM64 am).length r base am)
      (codeRange p (r.prefixByte :: encodeJmpM64 am))
      (Effect.post (jmpM64SegEffect p (r.prefixByte :: encodeJmpM64 am).length base am)) := by
  unfold encodeJmpM64
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := jmp_m64_seg_triple_of_bytes p r base am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := jmp_m64_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem jmp_m64_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (JmpMemA32Pre p (0x67 :: encodeJmpM64 am).length am)
      (codeRange p (0x67 :: encodeJmpM64 am))
      (Effect.post (jmpM64A32Effect p (0x67 :: encodeJmpM64 am).length am)) := by
  unfold encodeJmpM64
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := jmp_m64_a32_triple_of_bytes p am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := jmp_m64_rex_a32_triple_of_bytes p _ hrex.rexPrefix am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

attribute [x86_compose] jmpM64Effect jmpM64SegEffect jmpM64A32Effect

@[x86_local] theorem jmpM64Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (jmpM64Effect p len am) := by
  effect_local [jmpM64Effect]

@[x86_local] theorem jmpM64SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} : Effect.Local (jmpM64SegEffect p len base am) := by
  effect_local [jmpM64SegEffect]

@[x86_local] theorem jmpM64A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (jmpM64A32Effect p len am) := by
  effect_local [jmpM64A32Effect]

end X86Proofs
