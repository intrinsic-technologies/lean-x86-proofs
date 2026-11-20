import X86Proofs.Instructions.Fldcw.Generated.M16.Step
import X86Proofs.Instructions.Fldcw.Generated.M16.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fldcwM16Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Effect :=
  x87LdcwEffect p len
      (fldcwWord ((Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s))

@[simp] theorem fldcwM16Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (s : RamState) : (fldcwM16Effect p len am s).components =
      [.fcw, .fcc, .rip] := rfl

def fldcwM16SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode)
    (s : RamState) : Effect :=
  x87LdcwEffect p len
      (fldcwWord ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s))

@[simp] theorem fldcwM16SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (s : RamState) :
    (fldcwM16SegEffect p len base am s).components = [.fcw, .fcc, .rip] := rfl

def fldcwM16A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) :
    Effect :=
  x87LdcwEffect p len
      (fldcwWord ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 16).read s))

@[simp] theorem fldcwM16A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (s : RamState) : (fldcwM16A32Effect p len am s).components =
      [.fcw, .fcc, .rip] := rfl

theorem fldcw_m16_effect_step [Bindings] (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => LoadPre p (fun t => am.addr t (p + BitVec.ofNat 64 (2 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswES s.FP87_Status = 0 ∧
        FcwMasked
            (fldcwWord
            ((Operand.mem (am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) : Operand 16).read
            s)))
      (codeRange p (0xD9 :: am.modrm 5 :: am.tail))
      (fldcwM16Effect p (2 + am.tail.length) am) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hcr0, hes, hfm⟩
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := fldcw_m16_step s h hcr0 hes []
    (by simp) (by simp) (by rfl) (by rfl) (by rfl) am hv
        (by exact (AddrContext.legacy _ am hx hb).toSeg)
    (by exact hfm)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine (fun hh => ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩) ?_
  refine x87LdcwEffect_holds h _ s.RIP rfl _ (OnlyTrace.dataAccess _) _ _ _ _ ?_ ?_
  · rfl
  · exact fswRest_fswCCOracle _ _

theorem fldcw_m16_triple_of_bytes [Bindings] (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => LoadPre p (fun t => am.addr t (p + BitVec.ofNat 64 (2 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswES s.FP87_Status = 0 ∧
        FcwMasked
            (fldcwWord
            ((Operand.mem (am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) : Operand 16).read
            s)))
      (codeRange p (0xD9 :: am.modrm 5 :: am.tail))
      (Effect.post (fldcwM16Effect p (2 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fldcwM16Effect_components]; simp [Component.Covers]) _)
    (fldcw_m16_effect_step p am hv hx hb)

theorem fldcw_m16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => LoadPre p (fun t => am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswES s.FP87_Status = 0 ∧
        FcwMasked
            (fldcwWord
            ((Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand 16).read
            s)))
      (codeRange p (rex :: 0xD9 :: am.modrm 5 :: am.tail))
      (fldcwM16Effect p (3 + am.tail.length) am) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hcr0, hes, hfm⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := fldcw_m16_step s h hcr0 hes [rex]
    (by simpa using hr.scanPrefix) (by simp) (by rw [scanContext_rex _ _ hr]; rfl)
        (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) am hv
        (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    (by rw [scanContext_rex _ _ hr]; exact hfm)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine (fun hh => ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩) ?_
  refine x87LdcwEffect_holds h _ s.RIP rfl _ (OnlyTrace.dataAccess _) _ _ _ _ ?_ ?_
  · rfl
  · exact fswRest_fswCCOracle _ _

theorem fldcw_m16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => LoadPre p (fun t => am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswES s.FP87_Status = 0 ∧
        FcwMasked
            (fldcwWord
            ((Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand 16).read
            s)))
      (codeRange p (rex :: 0xD9 :: am.modrm 5 :: am.tail))
      (Effect.post (fldcwM16Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fldcwM16Effect_components]; simp [Component.Covers]) _)
    (fldcw_m16_rex_effect_step p rex hr am hv hx hb)

theorem fldcw_m16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => SegLoadPre p r base (fun t => am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length)))
          2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswES s.FP87_Status = 0 ∧
        FcwMasked
            (fldcwWord
            ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand
            16).read s)))
      (codeRange p (r.prefixByte :: 0xD9 :: am.modrm 5 :: am.tail))
      (fldcwM16SegEffect p (3 + am.tail.length) base am) := by
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, hcr0, hes, hfm⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [])
          (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := fldcw_m16_step s h hcr0 hes [r.prefixByte]
    (scanPrefix_seg_cons r (by simp)) (by simp) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    (by rw [hsc, segAddr_withSeg]; exact hfm)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine (fun hh => ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩) ?_
  refine x87LdcwEffect_holds h _ s.RIP rfl _ (OnlyTrace.dataAccess _) _ _ _ _ ?_ ?_
  · rfl
  · exact fswRest_fswCCOracle _ _

theorem fldcw_m16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => SegLoadPre p r base (fun t => am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length)))
          2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswES s.FP87_Status = 0 ∧
        FcwMasked
            (fldcwWord
            ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand
            16).read s)))
      (codeRange p (r.prefixByte :: 0xD9 :: am.modrm 5 :: am.tail))
      (Effect.post (fldcwM16SegEffect p (3 + am.tail.length) base am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fldcwM16SegEffect_components]; simp [Component.Covers]) _)
    (fldcw_m16_seg_effect_step p r base am hv hx hb)

theorem fldcw_m16_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => SegLoadPre p r base (fun t => am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length)))
          2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswES s.FP87_Status = 0 ∧
        FcwMasked
            (fldcwWord
            ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand
            16).read s)))
      (codeRange p (r.prefixByte :: rex :: 0xD9 :: am.modrm 5 :: am.tail))
      (fldcwM16SegEffect p (4 + am.tail.length) base am) := by
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, hcr0, hes, hfm⟩
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
  have hstep := fldcw_m16_step s h hcr0 hes [r.prefixByte, rex]
    (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl) am hv
        (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    (by rw [hsc, segAddr_withSeg]; exact hfm)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine (fun hh => ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩) ?_
  refine x87LdcwEffect_holds h _ s.RIP rfl _ (OnlyTrace.dataAccess _) _ _ _ _ ?_ ?_
  · rfl
  · exact fswRest_fswCCOracle _ _

theorem fldcw_m16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => SegLoadPre p r base (fun t => am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length)))
          2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswES s.FP87_Status = 0 ∧
        FcwMasked
            (fldcwWord
            ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand
            16).read s)))
      (codeRange p (r.prefixByte :: rex :: 0xD9 :: am.modrm 5 :: am.tail))
      (Effect.post (fldcwM16SegEffect p (4 + am.tail.length) base am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fldcwM16SegEffect_components]; simp [Component.Covers]) _)
    (fldcw_m16_rex_seg_effect_step p r base rex hr am hv hx hb)

theorem fldcw_m16_a32_effect_step [Bindings] (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => LoadPre p (fun t => am.addr32 t (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswES s.FP87_Status = 0 ∧
        FcwMasked
            (fldcwWord
            ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand
            16).read s)))
      (codeRange p (0x67 :: 0xD9 :: am.modrm 5 :: am.tail))
      (fldcwM16A32Effect p (3 + am.tail.length) am) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hcr0, hes, hfm⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := fldcw_m16_a32_step s h hcr0 hes [0x67]
    (scanPrefix_asz_cons (by simp)) (by simp) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    (by rw [hsc]; exact hfm)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine (fun hh => ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩) ?_
  refine x87LdcwEffect_holds h _ s.RIP rfl _ (OnlyTrace.dataAccess _) _ _ _ _ ?_ ?_
  · rfl
  · exact fswRest_fswCCOracle _ _

theorem fldcw_m16_a32_triple_of_bytes [Bindings] (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => LoadPre p (fun t => am.addr32 t (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswES s.FP87_Status = 0 ∧
        FcwMasked
            (fldcwWord
            ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand
            16).read s)))
      (codeRange p (0x67 :: 0xD9 :: am.modrm 5 :: am.tail))
      (Effect.post (fldcwM16A32Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fldcwM16A32Effect_components]; simp [Component.Covers]) _)
    (fldcw_m16_a32_effect_step p am hv hx hb)

theorem fldcw_m16_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => LoadPre p (fun t => am.addr32 t (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswES s.FP87_Status = 0 ∧
        FcwMasked
            (fldcwWord
            ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand
            16).read s)))
      (codeRange p (0x67 :: rex :: 0xD9 :: am.modrm 5 :: am.tail))
      (fldcwM16A32Effect p (4 + am.tail.length) am) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hcr0, hes, hfm⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := fldcw_m16_a32_step s h hcr0 hes [0x67, rex]
    (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl) am hv
        (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    (by rw [hsc]; exact hfm)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine (fun hh => ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩) ?_
  refine x87LdcwEffect_holds h _ s.RIP rfl _ (OnlyTrace.dataAccess _) _ _ _ _ ?_ ?_
  · rfl
  · exact fswRest_fswCCOracle _ _

theorem fldcw_m16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => LoadPre p (fun t => am.addr32 t (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswES s.FP87_Status = 0 ∧
        FcwMasked
            (fldcwWord
            ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand
            16).read s)))
      (codeRange p (0x67 :: rex :: 0xD9 :: am.modrm 5 :: am.tail))
      (Effect.post (fldcwM16A32Effect p (4 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fldcwM16A32Effect_components]; simp [Component.Covers]) _)
    (fldcw_m16_rex_a32_effect_step p rex hr am hv hx hb)

theorem fldcw_m16_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple
      (fun s => LoadPre p (fun t => am.addr t (p + BitVec.ofNat 64 (encodeFldcwM16 am).length)) 2 s
          ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswES s.FP87_Status = 0 ∧
        FcwMasked
            (fldcwWord
            ((Operand.mem (am.addr s (p + BitVec.ofNat 64 (encodeFldcwM16 am).length)) : Operand
            16).read s)))
      (codeRange p (encodeFldcwM16 am))
      (Effect.post (fldcwM16Effect p (encodeFldcwM16 am).length am)) := by
  unfold encodeFldcwM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := fldcw_m16_triple_of_bytes p am hv hx hb
    rwa [show (0xD9 :: am.modrm 5 :: am.tail : List UInt8).length =
      2 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := fldcw_m16_rex_triple_of_bytes p _ hrex.rexPrefix am hv hx hb
    rwa [show (am.rexByte false 0 :: 0xD9 :: am.modrm 5 :: am.tail).length =
      3 + am.tail.length by simp; omega]

theorem fldcw_m16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple
      (fun s => SegLoadPre p r base
          (fun t => am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeFldcwM16 am).length)) 2 s
          ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswES s.FP87_Status = 0 ∧
        FcwMasked
            (fldcwWord
            ((Operand.mem
            (base + am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeFldcwM16 am).length)) :
            Operand 16).read s)))
      (codeRange p (r.prefixByte :: encodeFldcwM16 am))
      (Effect.post (fldcwM16SegEffect p (r.prefixByte :: encodeFldcwM16 am).length base am)) := by
  unfold encodeFldcwM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := fldcw_m16_seg_triple_of_bytes p r base am hv hx hb
    rwa [show (r.prefixByte :: 0xD9 :: am.modrm 5 :: am.tail : List UInt8).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := fldcw_m16_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix am hv hx hb
    rwa [show (r.prefixByte :: am.rexByte false 0 :: 0xD9 :: am.modrm 5 ::
      am.tail).length = 4 + am.tail.length by simp; omega]

theorem fldcw_m16_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple
      (fun s => LoadPre p
          (fun t => am.addr32 t (p + BitVec.ofNat 64 (0x67 :: encodeFldcwM16 am).length)) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswES s.FP87_Status = 0 ∧
        FcwMasked
            (fldcwWord
            ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeFldcwM16 am).length)) :
            Operand 16).read s)))
      (codeRange p (0x67 :: encodeFldcwM16 am))
      (Effect.post (fldcwM16A32Effect p (0x67 :: encodeFldcwM16 am).length am)) := by
  unfold encodeFldcwM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := fldcw_m16_a32_triple_of_bytes p am hv hx hb
    rwa [show (0x67 :: 0xD9 :: am.modrm 5 :: am.tail : List UInt8).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := fldcw_m16_rex_a32_triple_of_bytes p _ hrex.rexPrefix am hv hx hb
    rwa [show (0x67 :: am.rexByte false 0 :: 0xD9 :: am.modrm 5 ::
      am.tail).length = 4 + am.tail.length by simp; omega]

attribute [x86_compose] fldcwM16Effect fldcwM16SegEffect fldcwM16A32Effect

@[x86_local] theorem fldcwM16Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (fldcwM16Effect p len am) := by
  effect_local [fldcwM16Effect, x87LdcwEffect]

@[x86_local] theorem fldcwM16SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} : Effect.Local (fldcwM16SegEffect p len base am) := by
  effect_local [fldcwM16SegEffect, x87LdcwEffect]

@[x86_local] theorem fldcwM16A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (fldcwM16A32Effect p len am) := by
  effect_local [fldcwM16A32Effect, x87LdcwEffect]

end X86Proofs
