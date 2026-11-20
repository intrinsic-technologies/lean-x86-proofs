import X86Proofs.Instructions.Ldmxcsr.Generated.M.Step
import X86Proofs.Instructions.Ldmxcsr.Generated.M.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def ldmxcsrM32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mxcsr : Operand 32),
      ldmxcsrSpec ((Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s)⟩] }

@[simp] theorem ldmxcsrM32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (s : RamState) : (ldmxcsrM32Effect p len am s).components = [.mxcsr, .rip] := rfl

def ldmxcsrM32SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode)
    (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mxcsr : Operand 32),
      ldmxcsrSpec ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s)⟩] }

@[simp] theorem ldmxcsrM32SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (s : RamState) :
    (ldmxcsrM32SegEffect p len base am s).components = [.mxcsr, .rip] := rfl

def ldmxcsrM32A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mxcsr : Operand 32),
      ldmxcsrSpec ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 32).read s)⟩] }

@[simp] theorem ldmxcsrM32A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (s : RamState) : (ldmxcsrM32A32Effect p len am s).components = [.mxcsr, .rip] := rfl

theorem ldmxcsr_m32_effect_step [Bindings] (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (LdmxcsrPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))))
      (codeRange p (0x0F :: 0xAE :: am.modrm 2 :: am.tail))
      (ldmxcsrM32Effect p (3 + am.tail.length) am) := by
  intro s h hcode hpre
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := ldmxcsr_m32_step s h hpre.sse hpre.sse.feature []
    (by simp) (by simp)
    rfl rfl rfl
    rfl rfl
    am hv (AddrContext.legacy _ am hx hb).toSeg
    hcode.bytesAt hlow hpre.read hpre.reserved
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_ldmxcsr h _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_ldmxcsr s _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_ldmxcsr]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem ldmxcsr_m32_triple_of_bytes [Bindings]
    (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (LdmxcsrPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))))
      (codeRange p (0x0F :: 0xAE :: am.modrm 2 :: am.tail))
      (Effect.post (ldmxcsrM32Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [ldmxcsrM32Effect_components]; simp [Component.Covers]) _)
    (ldmxcsr_m32_effect_step p am hv hx hb)

theorem ldmxcsr_m32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (LdmxcsrPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))))
      (codeRange p (rex :: 0x0F :: 0xAE :: am.modrm 2 :: am.tail))
      (ldmxcsrM32Effect p (4 + am.tail.length) am) := by
  intro s h hcode hpre
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := ldmxcsr_m32_step s h hpre.sse hpre.sse.feature [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl)
    am hv (by rw [hc]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [hc]; exact hpre.read) (by rw [hc]; exact hpre.reserved)
  simp only [hc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_ldmxcsr h _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_ldmxcsr s _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_ldmxcsr]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem ldmxcsr_m32_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (LdmxcsrPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))))
      (codeRange p (rex :: 0x0F :: 0xAE :: am.modrm 2 :: am.tail))
      (Effect.post (ldmxcsrM32Effect p (4 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [ldmxcsrM32Effect_components]; simp [Component.Covers]) _)
    (ldmxcsr_m32_rex_effect_step p rex hr am hv hx hb)

theorem ldmxcsr_m32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => LdmxcsrPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x0F :: 0xAE :: am.modrm 2 :: am.tail))
      (ldmxcsrM32SegEffect p (4 + am.tail.length) base am) := by
  intro s h hcode ⟨hpre, hseg, hbase⟩
  have hp := hpre.rip
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
  have hstep := ldmxcsr_m32_step s h hpre.sse hpre.sse.feature [r.prefixByte]
    (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.read) (by rw [hsc, segAddr_withSeg]; exact hpre.reserved)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_ldmxcsr h _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_ldmxcsr s _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_ldmxcsr]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem ldmxcsr_m32_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => LdmxcsrPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x0F :: 0xAE :: am.modrm 2 :: am.tail))
      (Effect.post (ldmxcsrM32SegEffect p (4 + am.tail.length) base am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [ldmxcsrM32SegEffect_components]; simp [Component.Covers]) _)
    (ldmxcsr_m32_seg_effect_step p r base am hv hx hb)

theorem ldmxcsr_m32_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => LdmxcsrPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xAE :: am.modrm 2 :: am.tail))
      (ldmxcsrM32SegEffect p (5 + am.tail.length) base am) := by
  intro s h hcode ⟨hpre, hseg, hbase⟩
  have hp := hpre.rip
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex s.DS (PrefixSegments.ofState s) hr]
  have hstep := ldmxcsr_m32_step s h hpre.sse hpre.sse.feature [r.prefixByte, rex]
    (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.read) (by rw [hsc, segAddr_withSeg]; exact hpre.reserved)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_ldmxcsr h _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_ldmxcsr s _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_ldmxcsr]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem ldmxcsr_m32_rex_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => LdmxcsrPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xAE :: am.modrm 2 :: am.tail))
      (Effect.post (ldmxcsrM32SegEffect p (5 + am.tail.length) base am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [ldmxcsrM32SegEffect_components]; simp [Component.Covers]) _)
    (ldmxcsr_m32_rex_seg_effect_step p r base rex hr am hv hx hb)

theorem ldmxcsr_m32_a32_effect_step [Bindings] (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (LdmxcsrPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))))
      (codeRange p (0x67 :: 0x0F :: 0xAE :: am.modrm 2 :: am.tail))
      (ldmxcsrM32A32Effect p (4 + am.tail.length) am) := by
  intro s h hcode hpre
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := ldmxcsr_m32_a32_step s h hpre.sse hpre.sse.feature [0x67]
    (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.read) (by rw [hsc]; exact hpre.reserved)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_ldmxcsr h _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_ldmxcsr s _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_ldmxcsr]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem ldmxcsr_m32_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (LdmxcsrPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))))
      (codeRange p (0x67 :: 0x0F :: 0xAE :: am.modrm 2 :: am.tail))
      (Effect.post (ldmxcsrM32A32Effect p (4 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [ldmxcsrM32A32Effect_components]; simp [Component.Covers]) _)
    (ldmxcsr_m32_a32_effect_step p am hv hx hb)

theorem ldmxcsr_m32_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (LdmxcsrPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))))
      (codeRange p (0x67 :: rex :: 0x0F :: 0xAE :: am.modrm 2 :: am.tail))
      (ldmxcsrM32A32Effect p (5 + am.tail.length) am) := by
  intro s h hcode hpre
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex s.DS (PrefixSegments.ofState s) hr]
  have hstep := ldmxcsr_m32_a32_step s h hpre.sse hpre.sse.feature [0x67, rex]
    (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.read) (by rw [hsc]; exact hpre.reserved)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_ldmxcsr h _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_ldmxcsr s _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_ldmxcsr]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem ldmxcsr_m32_rex_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (LdmxcsrPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))))
      (codeRange p (0x67 :: rex :: 0x0F :: 0xAE :: am.modrm 2 :: am.tail))
      (Effect.post (ldmxcsrM32A32Effect p (5 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [ldmxcsrM32A32Effect_components]; simp [Component.Covers]) _)
    (ldmxcsr_m32_rex_a32_effect_step p rex hr am hv hx hb)

theorem ldmxcsr_m32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple
      (LdmxcsrPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeLdmxcsrM32 am).length)))
      (codeRange p (encodeLdmxcsrM32 am))
      (Effect.post (ldmxcsrM32Effect p (encodeLdmxcsrM32 am).length am)) := by
  unfold encodeLdmxcsrM32
  rcases encodeSseMem_spec 0xAE 2 am with ⟨hbytes, hx, hb, -⟩ | hbytes
  · have hl : (0x0F :: 0xAE :: am.modrm (regLow 2) :: am.tail :
        List UInt8).length = 3 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact ldmxcsr_m32_triple_of_bytes p am hv hx hb
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 2
    have hl : (am.rexByte false 2 :: 0x0F :: 0xAE :: am.modrm (regLow 2) ::
        am.tail).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact ldmxcsr_m32_rex_triple_of_bytes p _ hrex.rexPrefix am hv hx hb

theorem ldmxcsr_m32_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple
      (LdmxcsrPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeLdmxcsrM32 am).length)))
      (codeRange p (0x67 :: encodeLdmxcsrM32 am))
      (Effect.post (ldmxcsrM32A32Effect p (0x67 :: encodeLdmxcsrM32 am).length am)) := by
  unfold encodeLdmxcsrM32
  rcases encodeSseMem_spec 0xAE 2 am with ⟨hbytes, hx, hb, -⟩ | hbytes
  · have hl : (0x67 :: 0x0F :: 0xAE :: am.modrm (regLow 2) :: am.tail :
        List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact ldmxcsr_m32_a32_triple_of_bytes p am hv hx hb
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 2
    have hl : (0x67 :: am.rexByte false 2 :: 0x0F :: 0xAE :: am.modrm (regLow 2) ::
        am.tail).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact ldmxcsr_m32_rex_a32_triple_of_bytes p _ hrex.rexPrefix am hv hx hb

theorem ldmxcsr_m32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple
      (fun s => LdmxcsrPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeLdmxcsrM32 am).length)) s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: encodeLdmxcsrM32 am))
      (Effect.post (ldmxcsrM32SegEffect p (r.prefixByte :: encodeLdmxcsrM32 am).length base am)) := by
  unfold encodeLdmxcsrM32
  rcases encodeSseMem_spec 0xAE 2 am with ⟨hbytes, hx, hb, -⟩ | hbytes
  · have hl : (r.prefixByte :: 0x0F :: 0xAE :: am.modrm (regLow 2) ::
        am.tail : List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact ldmxcsr_m32_seg_triple_of_bytes p r base am hv hx hb
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 2
    have hl : (r.prefixByte :: am.rexByte false 2 :: 0x0F :: 0xAE ::
        am.modrm (regLow 2) :: am.tail).length = 5 + am.tail.length := by
      simp; omega
    rw [hbytes, hl]
    exact ldmxcsr_m32_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix am hv hx hb

attribute [x86_compose] ldmxcsrM32Effect

@[x86_local] theorem ldmxcsrM32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (ldmxcsrM32Effect p len am) := by
  effect_local [ldmxcsrM32Effect]

attribute [x86_compose] ldmxcsrM32SegEffect

@[x86_local] theorem ldmxcsrM32SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} :
    Effect.Local (ldmxcsrM32SegEffect p len base am) := by
  effect_local [ldmxcsrM32SegEffect]

attribute [x86_compose] ldmxcsrM32A32Effect

@[x86_local] theorem ldmxcsrM32A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (ldmxcsrM32A32Effect p len am) := by
  effect_local [ldmxcsrM32A32Effect]

end X86Proofs
