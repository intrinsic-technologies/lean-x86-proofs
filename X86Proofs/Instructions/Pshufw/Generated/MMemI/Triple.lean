import X86Proofs.Instructions.Pshufw.Generated.MMemI.Step
import X86Proofs.Instructions.Pshufw.Generated.MMemI.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def pshufwMmM64Imm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  mmxEffect s (p + BitVec.ofNat 64 len) dst (pshufwSpec b imm)

@[simp] theorem pshufwMmM64Imm8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    (pshufwMmM64Imm8Effect p len dst am imm s).components = [.fpr dst, .fsw, .ftw, .rip] := rfl

def pshufwMmM64Imm8SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 3)
    (am : AddrMode) (imm : BitVec 8) (s : RamState) : Effect :=
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  mmxEffect s (p + BitVec.ofNat 64 len) dst (pshufwSpec b imm)

@[simp] theorem pshufwMmM64Imm8SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 3) (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    (pshufwMmM64Imm8SegEffect p len base dst am imm s).components =
      [.fpr dst, .fsw, .ftw, .rip] := rfl

def pshufwMmM64Imm8A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  mmxEffect s (p + BitVec.ofNat 64 len) dst (pshufwSpec b imm)

@[simp] theorem pshufwMmM64Imm8A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    (pshufwMmM64Imm8A32Effect p len dst am imm s).components = [.fpr dst, .fsw, .ftw, .rip] := rfl

theorem pshufw_mm_m64_imm8_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) :
    StepEffect
      (MmxLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (0x0F :: 0x70 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (pshufwMmM64Imm8Effect p (4 + am.tail.length) reg am imm) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hmmx⟩, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := pshufw_mm_m64_imm8_step s h hcr0 hes hmmx []
    (by simp) (by simp)
    rfl rfl rfl rfl rfl
    reg am hv (AddrContext.legacy _ am hx hb).toSeg imm
    hcode.bytesAt hlow hread
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds_load h _ _ _ _ rfl

theorem pshufw_mm_m64_imm8_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) :
    Triple
      (MmxLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (0x0F :: 0x70 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (pshufwMmM64Imm8Effect p (4 + am.tail.length) reg am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [pshufwMmM64Imm8Effect_components]; simp [Component.Covers]) _)
    (pshufw_mm_m64_imm8_effect_step p reg am hv hx hb imm)

theorem pshufw_mm_m64_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    StepEffect
      (MmxLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (rex :: 0x0F :: 0x70 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (pshufwMmM64Imm8Effect p (5 + am.tail.length) reg am imm) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hmmx⟩, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := pshufw_mm_m64_imm8_step s h hcr0 hes hmmx [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    reg am hv (by rw [hc]; exact (AddrContext.rex _ _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by rw [hc]; exact hread)
  simp only [hc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds_load h _ _ _ _ rfl

theorem pshufw_mm_m64_imm8_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    Triple
      (MmxLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (rex :: 0x0F :: 0x70 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (pshufwMmM64Imm8Effect p (5 + am.tail.length) reg am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [pshufwMmM64Imm8Effect_components]; simp [Component.Covers]) _)
    (pshufw_mm_m64_imm8_rex_effect_step p rex hr reg am hv hx hb imm)

theorem pshufw_mm_m64_imm8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) :
    StepEffect
      (fun s => MmxLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x0F :: 0x70 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (pshufwMmM64Imm8SegEffect p (5 + am.tail.length) base reg am imm) := by
  rintro s h hcode ⟨⟨⟨hp, hcr0, hes, hmmx⟩, hread⟩, hseg, hbase⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := pshufw_mm_m64_imm8_step s h hcr0 hes hmmx [r.prefixByte]
    (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds_load h _ _ _ _ rfl

theorem pshufw_mm_m64_imm8_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) :
    Triple
      (fun s => MmxLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x0F :: 0x70 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (pshufwMmM64Imm8SegEffect p (5 + am.tail.length) base reg am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [pshufwMmM64Imm8SegEffect_components]; simp [Component.Covers]) _)
    (pshufw_mm_m64_imm8_seg_effect_step p r base reg am hv hx hb imm)

theorem pshufw_mm_m64_imm8_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    StepEffect
      (fun s => MmxLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (6 + am.tail.length))) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x70 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (pshufwMmM64Imm8SegEffect p (6 + am.tail.length) base reg am imm) := by
  rintro s h hcode ⟨⟨⟨hp, hcr0, hes, hmmx⟩, hread⟩, hseg, hbase⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex s.DS (PrefixSegments.ofState s) hr]
  have hstep := pshufw_mm_m64_imm8_step s h hcr0 hes hmmx [r.prefixByte, rex]
    (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds_load h _ _ _ _ rfl

theorem pshufw_mm_m64_imm8_rex_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    Triple
      (fun s => MmxLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (6 + am.tail.length))) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x70 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (pshufwMmM64Imm8SegEffect p (6 + am.tail.length) base reg am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [pshufwMmM64Imm8SegEffect_components]; simp [Component.Covers]) _)
    (pshufw_mm_m64_imm8_rex_seg_effect_step p r base rex hr reg am hv hx hb imm)

theorem pshufw_mm_m64_imm8_a32_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) :
    StepEffect
      (MmxLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (0x67 :: 0x0F :: 0x70 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (pshufwMmM64Imm8A32Effect p (5 + am.tail.length) reg am imm) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hmmx⟩, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := pshufw_mm_m64_imm8_a32_step s h hcr0 hes hmmx [0x67]
    (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds_load h _ _ _ _ rfl

theorem pshufw_mm_m64_imm8_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) :
    Triple
      (MmxLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (0x67 :: 0x0F :: 0x70 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (pshufwMmM64Imm8A32Effect p (5 + am.tail.length) reg am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [pshufwMmM64Imm8A32Effect_components]; simp [Component.Covers]) _)
    (pshufw_mm_m64_imm8_a32_effect_step p reg am hv hx hb imm)

theorem pshufw_mm_m64_imm8_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    StepEffect
      (MmxLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0x0F :: 0x70 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (pshufwMmM64Imm8A32Effect p (6 + am.tail.length) reg am imm) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hmmx⟩, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex s.DS (PrefixSegments.ofState s) hr]
  have hstep := pshufw_mm_m64_imm8_a32_step s h hcr0 hes hmmx [0x67, rex]
    (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load_mmx h _ _ _ _, ?_⟩
  exact mmxEffect_holds_load h _ _ _ _ rfl

theorem pshufw_mm_m64_imm8_rex_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    Triple
      (MmxLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0x0F :: 0x70 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (pshufwMmM64Imm8A32Effect p (6 + am.tail.length) reg am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [pshufwMmM64Imm8A32Effect_components]; simp [Component.Covers]) _)
    (pshufw_mm_m64_imm8_rex_a32_effect_step p rex hr reg am hv hx hb imm)

theorem pshufw_mm_m64_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (imm : BitVec 8) :
    Triple
      (MmxLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodePshufwMmM64Imm8 dst am imm).length)) 8)
      (codeRange p (encodePshufwMmM64Imm8 dst am imm))
      (Effect.post (pshufwMmM64Imm8Effect p (encodePshufwMmM64Imm8 dst am imm).length dst am
        imm)) := by
  unfold encodePshufwMmM64Imm8
  rcases encodeMmxMem_spec 0x70 dst am with ⟨hbytes, hx, hb⟩ | ⟨hbytes, hrex, hx, hb⟩
  · have hl : ((0x0F :: 0x70 :: am.modrm dst :: am.tail) ++ immBytes 8 imm :
        List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact pshufw_mm_m64_imm8_triple_of_bytes p dst am hv hx hb imm
  · have hl : ((am.rexByte false 0 :: 0x0F :: 0x70 :: am.modrm dst :: am.tail) ++
        immBytes 8 imm).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact pshufw_mm_m64_imm8_rex_triple_of_bytes p _ hrex.rexPrefix dst am hv hx hb imm

theorem pshufw_mm_m64_imm8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 3) (am : AddrMode) (hv : am.Valid) (imm : BitVec 8) :
    Triple
      (fun s => MmxLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodePshufwMmM64Imm8 dst am imm).length)) 8 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: encodePshufwMmM64Imm8 dst am imm))
      (Effect.post (pshufwMmM64Imm8SegEffect p (r.prefixByte :: encodePshufwMmM64Imm8 dst am imm).length base dst am
        imm)) := by
  unfold encodePshufwMmM64Imm8
  rcases encodeMmxMem_spec 0x70 dst am with ⟨hbytes, hx, hb⟩ | ⟨hbytes, hrex, hx, hb⟩
  · have hl : (r.prefixByte :: ((0x0F :: 0x70 :: am.modrm dst :: am.tail) ++
        immBytes 8 imm) : List UInt8).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact pshufw_mm_m64_imm8_seg_triple_of_bytes p r base dst am hv hx hb imm
  · have hl : (r.prefixByte :: ((am.rexByte false 0 :: 0x0F :: 0x70 :: am.modrm dst ::
        am.tail) ++ immBytes 8 imm)).length = 6 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact pshufw_mm_m64_imm8_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix dst am hv hx hb
      imm

theorem pshufw_mm_m64_imm8_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (imm : BitVec 8) :
    Triple
      (MmxLoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodePshufwMmM64Imm8 dst am imm).length)) 8)
      (codeRange p (0x67 :: encodePshufwMmM64Imm8 dst am imm))
      (Effect.post (pshufwMmM64Imm8A32Effect p (0x67 :: encodePshufwMmM64Imm8 dst am imm).length dst am
        imm)) := by
  unfold encodePshufwMmM64Imm8
  rcases encodeMmxMem_spec 0x70 dst am with ⟨hbytes, hx, hb⟩ | ⟨hbytes, hrex, hx, hb⟩
  · have hl : (0x67 :: ((0x0F :: 0x70 :: am.modrm dst :: am.tail) ++
        immBytes 8 imm) : List UInt8).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact pshufw_mm_m64_imm8_a32_triple_of_bytes p dst am hv hx hb imm
  · have hl : (0x67 :: ((am.rexByte false 0 :: 0x0F :: 0x70 :: am.modrm dst ::
        am.tail) ++ immBytes 8 imm)).length = 6 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact pshufw_mm_m64_imm8_rex_a32_triple_of_bytes p _ hrex.rexPrefix dst am hv hx hb imm

attribute [x86_compose] pshufwMmM64Imm8Effect

@[x86_local] theorem pshufwMmM64Imm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (pshufwMmM64Imm8Effect p len dst am imm) := by
  effect_local [pshufwMmM64Imm8Effect, mmxEffect]

attribute [x86_compose] pshufwMmM64Imm8SegEffect

@[x86_local] theorem pshufwMmM64Imm8SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 3} {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (pshufwMmM64Imm8SegEffect p len base dst am imm) := by
  effect_local [pshufwMmM64Imm8SegEffect, mmxEffect]

attribute [x86_compose] pshufwMmM64Imm8A32Effect

@[x86_local] theorem pshufwMmM64Imm8A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (pshufwMmM64Imm8A32Effect p len dst am imm) := by
  effect_local [pshufwMmM64Imm8A32Effect, mmxEffect]

end X86Proofs
