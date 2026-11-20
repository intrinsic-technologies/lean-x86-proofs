import X86Proofs.Instructions.Movq.Generated.XM6E.Step
import X86Proofs.Instructions.Movq.Generated.XM6E.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movqXmmM64RexwEffect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), movdSpec 64 128 b⟩] }

@[simp] theorem movqXmmM64RexwEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (movqXmmM64RexwEffect p len dst am s).components = [.xmm dst, .rip] := rfl

def movqXmmM64RexwSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) : Effect :=
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), movdSpec 64 128 b⟩] }

@[simp] theorem movqXmmM64RexwSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (movqXmmM64RexwSegEffect p len base dst am s).components = [.xmm dst, .rip] := rfl

def movqXmmM64RexwA32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.xmm dst : Operand 128), movdSpec 64 128 b⟩] }

@[simp] theorem movqXmmM64RexwA32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (movqXmmM64RexwA32Effect p len dst am s).components = [.xmm dst, .rip] := rfl

theorem movq_xmm_m64_rexw_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (Sse2LoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (0x66 :: rex :: 0x0F :: 0x6E :: am.modrm reg :: am.tail))
      (movqXmmM64RexwEffect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode hpre
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hc := scanContext_66_rex s.DS (PrefixSegments.ofState s) hr.rexPrefix
  have hstep := movq_xmm_m64_rexw_step s h hpre.sse hpre.sse2 [0x66, rex]
    (by simp [scanPrefix_66, hr.rexPrefix.scanPrefix]) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; exact hr.rex_w s.DS) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl)
    reg am hv (by rw [hc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [hc]; exact hpre.read)
  simp only [hc] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_r4
      (oszRexContext s.DS rex.toBitVec).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem movq_xmm_m64_rexw_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (Sse2LoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (0x66 :: rex :: 0x0F :: 0x6E :: am.modrm reg :: am.tail))
      (Effect.post (movqXmmM64RexwEffect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movqXmmM64RexwEffect_components]; simp [Component.Covers]) _)
    (movq_xmm_m64_rexw_rex_effect_step p rex hr reg am hv hx hb)

theorem movq_xmm_m64_rexw_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => Sse2LoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (6 + am.tail.length))) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: 0x6E :: am.modrm reg :: am.tail))
      (movqXmmM64RexwSegEffect p (6 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode ⟨hpre, hseg, hbase⟩
  have hp := hpre.rip
  subst hp hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66, rex] =
      withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66, rex]
      (noSegPrefix_cons noSegPrefix_66 (noSegPrefix_cons hr.rexPrefix.noSegPrefix noSegPrefix_nil)), scanContext_66_rex s.DS (PrefixSegments.ofState s) hr.rexPrefix]
  have hstep := movq_xmm_m64_rexw_step s h hpre.sse hpre.sse2 [r.prefixByte, 0x66, rex]
    (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.rexPrefix.scanPrefix])) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; exact hr.rex_w s.DS) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.read)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem movq_xmm_m64_rexw_rex_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => Sse2LoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (6 + am.tail.length))) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: 0x6E :: am.modrm reg :: am.tail))
      (Effect.post (movqXmmM64RexwSegEffect p (6 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movqXmmM64RexwSegEffect_components]; simp [Component.Covers]) _)
    (movq_xmm_m64_rexw_rex_seg_effect_step p r base rex hr reg am hv hx hb)

theorem movq_xmm_m64_rexw_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (Sse2LoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 8)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: 0x6E :: am.modrm reg :: am.tail))
      (movqXmmM64RexwA32Effect p (6 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode hpre
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, rex] =
      withAsz (oszRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_66_rex s.DS (PrefixSegments.ofState s) hr.rexPrefix]
  have hstep := movq_xmm_m64_rexw_a32_step s h hpre.sse hpre.sse2 [0x67, 0x66, rex]
    (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.rexPrefix.scanPrefix])) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; exact hr.rex_w s.DS) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.read)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (oszRexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (oszRexContext s.DS rex.toBitVec)).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem movq_xmm_m64_rexw_rex_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (Sse2LoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 8)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: 0x6E :: am.modrm reg :: am.tail))
      (Effect.post (movqXmmM64RexwA32Effect p (6 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movqXmmM64RexwA32Effect_components]; simp [Component.Covers]) _)
    (movq_xmm_m64_rexw_rex_a32_effect_step p rex hr reg am hv hx hb)

theorem movq_xmm_m64_rexw_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (Sse2LoadNPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeMovqXmmM64Rexw dst am).length)) 8)
      (codeRange p (encodeMovqXmmM64Rexw dst am))
      (Effect.post (movqXmmM64RexwEffect p (encodeMovqXmmM64Rexw dst am).length
        (dst.setWidth 5) am)) := by
  unfold encodeMovqXmmM64Rexw
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := movq_xmm_m64_rexw_rex_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
  rw [hr, gprNumber_reg] at this
  have hl : (0x66 :: am.rexByte true dst :: 0x0F :: 0x6E :: am.modrm (regLow dst) ::
      am.tail).length = 5 + am.tail.length := by simp; omega
  unfold encodeSseMemW
  rw [hl]
  exact this

theorem movq_xmm_m64_rexw_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple
      (fun s => Sse2LoadNPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeMovqXmmM64Rexw dst am).length)) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: encodeMovqXmmM64Rexw dst am))
      (Effect.post (movqXmmM64RexwSegEffect p (r.prefixByte :: encodeMovqXmmM64Rexw dst am).length base
        (dst.setWidth 5) am)) := by
  unfold encodeMovqXmmM64Rexw
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := movq_xmm_m64_rexw_rex_seg_triple_of_bytes p r base _ hrex (regLow dst) am hv hx hb
  rw [hr, gprNumber_reg] at this
  have hl : (r.prefixByte :: 0x66 :: am.rexByte true dst :: 0x0F :: 0x6E ::
      am.modrm (regLow dst) :: am.tail).length = 6 + am.tail.length := by simp; omega
  unfold encodeSseMemW
  rw [hl]
  exact this

attribute [x86_compose] movqXmmM64RexwEffect

@[x86_local] theorem movqXmmM64RexwEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (movqXmmM64RexwEffect p len dst am) := by
  effect_local [movqXmmM64RexwEffect]

attribute [x86_compose] movqXmmM64RexwSegEffect

@[x86_local] theorem movqXmmM64RexwSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (movqXmmM64RexwSegEffect p len base dst am) := by
  effect_local [movqXmmM64RexwSegEffect]

theorem movq_xmm_m64_rexw_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (Sse2LoadNPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeMovqXmmM64Rexw dst am).length)) 8)
      (codeRange p (0x67 :: encodeMovqXmmM64Rexw dst am))
      (Effect.post (movqXmmM64RexwA32Effect p (0x67 :: encodeMovqXmmM64Rexw dst am).length
        (dst.setWidth 5) am)) := by
  unfold encodeMovqXmmM64Rexw
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := movq_xmm_m64_rexw_rex_a32_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
  rw [hr, gprNumber_reg] at this
  have hl : (0x67 :: 0x66 :: am.rexByte true dst :: 0x0F :: 0x6E ::
      am.modrm (regLow dst) :: am.tail).length = 6 + am.tail.length := by simp; omega
  unfold encodeSseMemW
  rw [hl]
  exact this

attribute [x86_compose] movqXmmM64RexwA32Effect

@[x86_local] theorem movqXmmM64RexwA32Effect_local {p : BitVec 64} {len : Nat}
    {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (movqXmmM64RexwA32Effect p len dst am) := by
  effect_local [movqXmmM64RexwA32Effect]

end X86Proofs
