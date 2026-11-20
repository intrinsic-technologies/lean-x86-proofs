import X86Proofs.Instructions.Fnstcw.Generated.M16.Step
import X86Proofs.Instructions.Fnstcw.Generated.M16.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fnstcwM16Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Effect :=
  x87CtlStoreEffect p len (am.addr s (p + BitVec.ofNat 64 len)) ((Operand.fcw : Operand 16).read s)

@[simp] theorem fnstcwM16Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (s : RamState) : (fnstcwM16Effect p len am s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) 2, .fcc, .rip] := by
  simp only [fnstcwM16Effect, x87CtlStoreEffect_components]

def fnstcwM16SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode)
    (s : RamState) : Effect :=
  x87CtlStoreEffect p len (base + am.addr s (p + BitVec.ofNat 64 len))
      ((Operand.fcw : Operand 16).read s)

@[simp] theorem fnstcwM16SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (s : RamState) :
    (fnstcwM16SegEffect p len base am s).components =
        [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) 2, .fcc, .rip] := by
  simp only [fnstcwM16SegEffect, x87CtlStoreEffect_components]

def fnstcwM16A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) :
    Effect :=
  x87CtlStoreEffect p len (am.addr32 s (p + BitVec.ofNat 64 len))
      ((Operand.fcw : Operand 16).read s)

@[simp] theorem fnstcwM16A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (s : RamState) : (fnstcwM16A32Effect p len am s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) 2, .fcc, .rip] := by
  simp only [fnstcwM16A32Effect, x87CtlStoreEffect_components]

theorem fnstcw_m16_effect_step [Bindings] (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => StorePre p (2 + am.tail.length)
          (fun t => am.addr t (p + BitVec.ofNat 64 (2 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0)
      (codeRange p (0xD9 :: am.modrm 7 :: am.tail))
      (fnstcwM16Effect p (2 + am.tail.length) am) := by
  rintro s h hcode ⟨⟨hp, hwrite, -⟩, hcr0⟩
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := fnstcw_m16_step s h hcr0 []
    (by simp) (by simp) (by rfl) (by rfl) (by rfl) am hv
        (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hwrite)
  dsimp only at hstep
  refine
      (fun hh =>
      ⟨_, hstep, ReadyToStep.of_x87Store h hh rfl (by exact hwrite.low) (by exact hwrite.tables),
      hh⟩) ?_
  refine x87CtlStoreEffect_holds h _ s.RIP _ _ _ ?_ _ ?_
  · rfl
  · exact fswRest_fswCCOracle _ _

theorem fnstcw_m16_triple_of_bytes [Bindings] (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => StorePre p (2 + am.tail.length)
          (fun t => am.addr t (p + BitVec.ofNat 64 (2 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0)
      (codeRange p (0xD9 :: am.modrm 7 :: am.tail))
      (Effect.post (fnstcwM16Effect p (2 + am.tail.length) am)) :=
  Triple.of_effect (fun _ hpre => x87CtlStoreEffect_avoids hpre.1.code
    (by simp; omega))
    (fnstcw_m16_effect_step p am hv hx hb)

theorem fnstcw_m16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => StorePre p (3 + am.tail.length)
          (fun t => am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0)
      (codeRange p (rex :: 0xD9 :: am.modrm 7 :: am.tail))
      (fnstcwM16Effect p (3 + am.tail.length) am) := by
  rintro s h hcode ⟨⟨hp, hwrite, -⟩, hcr0⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := fnstcw_m16_step s h hcr0 [rex]
    (by simpa using hr.scanPrefix) (by simp) (by rw [scanContext_rex _ _ hr]; rfl)
        (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) am hv
        (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hwrite)
  simp only [scanContext_rex _ _ hr] at hstep
  refine
      (fun hh =>
      ⟨_, hstep, ReadyToStep.of_x87Store h hh rfl (by exact hwrite.low) (by exact hwrite.tables),
      hh⟩) ?_
  refine x87CtlStoreEffect_holds h _ s.RIP _ _ _ ?_ _ ?_
  · rfl
  · exact fswRest_fswCCOracle _ _

theorem fnstcw_m16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => StorePre p (3 + am.tail.length)
          (fun t => am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0)
      (codeRange p (rex :: 0xD9 :: am.modrm 7 :: am.tail))
      (Effect.post (fnstcwM16Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect (fun _ hpre => x87CtlStoreEffect_avoids hpre.1.code
    (by simp; omega))
    (fnstcw_m16_rex_effect_step p rex hr am hv hx hb)

theorem fnstcw_m16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => SegStorePre p (3 + am.tail.length) r base
          (fun t => am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0)
      (codeRange p (r.prefixByte :: 0xD9 :: am.modrm 7 :: am.tail))
      (fnstcwM16SegEffect p (3 + am.tail.length) base am) := by
  rintro s h hcode ⟨⟨⟨hp, hwrite, -⟩, ⟨hseg, hbase⟩⟩, hcr0⟩
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
  have hstep := fnstcw_m16_step s h hcr0 [r.prefixByte]
    (scanPrefix_seg_cons r (by simp)) (by simp) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hwrite)
  simp only [hsc, segAddr_withSeg] at hstep
  refine
      (fun hh =>
      ⟨_, hstep, ReadyToStep.of_x87Store h hh rfl (by exact hwrite.low) (by exact hwrite.tables),
      hh⟩) ?_
  refine x87CtlStoreEffect_holds h _ s.RIP _ _ _ ?_ _ ?_
  · rfl
  · exact fswRest_fswCCOracle _ _

theorem fnstcw_m16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => SegStorePre p (3 + am.tail.length) r base
          (fun t => am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0)
      (codeRange p (r.prefixByte :: 0xD9 :: am.modrm 7 :: am.tail))
      (Effect.post (fnstcwM16SegEffect p (3 + am.tail.length) base am)) :=
  Triple.of_effect (fun _ hpre => x87CtlStoreEffect_avoids hpre.1.store.code
    (by simp; omega))
    (fnstcw_m16_seg_effect_step p r base am hv hx hb)

theorem fnstcw_m16_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => SegStorePre p (4 + am.tail.length) r base
          (fun t => am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0)
      (codeRange p (r.prefixByte :: rex :: 0xD9 :: am.modrm 7 :: am.tail))
      (fnstcwM16SegEffect p (4 + am.tail.length) base am) := by
  rintro s h hcode ⟨⟨⟨hp, hwrite, -⟩, ⟨hseg, hbase⟩⟩, hcr0⟩
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
  have hstep := fnstcw_m16_step s h hcr0 [r.prefixByte, rex]
    (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl) am hv
        (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hwrite)
  simp only [hsc, segAddr_withSeg] at hstep
  refine
      (fun hh =>
      ⟨_, hstep, ReadyToStep.of_x87Store h hh rfl (by exact hwrite.low) (by exact hwrite.tables),
      hh⟩) ?_
  refine x87CtlStoreEffect_holds h _ s.RIP _ _ _ ?_ _ ?_
  · rfl
  · exact fswRest_fswCCOracle _ _

theorem fnstcw_m16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => SegStorePre p (4 + am.tail.length) r base
          (fun t => am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0)
      (codeRange p (r.prefixByte :: rex :: 0xD9 :: am.modrm 7 :: am.tail))
      (Effect.post (fnstcwM16SegEffect p (4 + am.tail.length) base am)) :=
  Triple.of_effect (fun _ hpre => x87CtlStoreEffect_avoids hpre.1.store.code
    (by simp; omega))
    (fnstcw_m16_rex_seg_effect_step p r base rex hr am hv hx hb)

theorem fnstcw_m16_a32_effect_step [Bindings] (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => StorePre p (3 + am.tail.length)
          (fun t => am.addr32 t (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0)
      (codeRange p (0x67 :: 0xD9 :: am.modrm 7 :: am.tail))
      (fnstcwM16A32Effect p (3 + am.tail.length) am) := by
  rintro s h hcode ⟨⟨hp, hwrite, -⟩, hcr0⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := fnstcw_m16_a32_step s h hcr0 [0x67]
    (scanPrefix_asz_cons (by simp)) (by simp) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hwrite)
  simp only [hsc] at hstep
  refine
      (fun hh =>
      ⟨_, hstep, ReadyToStep.of_x87Store h hh rfl (by exact hwrite.low) (by exact hwrite.tables),
      hh⟩) ?_
  refine x87CtlStoreEffect_holds h _ s.RIP _ _ _ ?_ _ ?_
  · rfl
  · exact fswRest_fswCCOracle _ _

theorem fnstcw_m16_a32_triple_of_bytes [Bindings] (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => StorePre p (3 + am.tail.length)
          (fun t => am.addr32 t (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0)
      (codeRange p (0x67 :: 0xD9 :: am.modrm 7 :: am.tail))
      (Effect.post (fnstcwM16A32Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect (fun _ hpre => x87CtlStoreEffect_avoids hpre.1.code
    (by simp; omega))
    (fnstcw_m16_a32_effect_step p am hv hx hb)

theorem fnstcw_m16_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => StorePre p (4 + am.tail.length)
          (fun t => am.addr32 t (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0)
      (codeRange p (0x67 :: rex :: 0xD9 :: am.modrm 7 :: am.tail))
      (fnstcwM16A32Effect p (4 + am.tail.length) am) := by
  rintro s h hcode ⟨⟨hp, hwrite, -⟩, hcr0⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := fnstcw_m16_a32_step s h hcr0 [0x67, rex]
    (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl) am hv
        (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hwrite)
  simp only [hsc] at hstep
  refine
      (fun hh =>
      ⟨_, hstep, ReadyToStep.of_x87Store h hh rfl (by exact hwrite.low) (by exact hwrite.tables),
      hh⟩) ?_
  refine x87CtlStoreEffect_holds h _ s.RIP _ _ _ ?_ _ ?_
  · rfl
  · exact fswRest_fswCCOracle _ _

theorem fnstcw_m16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => StorePre p (4 + am.tail.length)
          (fun t => am.addr32 t (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0)
      (codeRange p (0x67 :: rex :: 0xD9 :: am.modrm 7 :: am.tail))
      (Effect.post (fnstcwM16A32Effect p (4 + am.tail.length) am)) :=
  Triple.of_effect (fun _ hpre => x87CtlStoreEffect_avoids hpre.1.code
    (by simp; omega))
    (fnstcw_m16_rex_a32_effect_step p rex hr am hv hx hb)

theorem fnstcw_m16_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple
      (fun s => StorePre p (encodeFnstcwM16 am).length
          (fun t => am.addr t (p + BitVec.ofNat 64 (encodeFnstcwM16 am).length)) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0)
      (codeRange p (encodeFnstcwM16 am))
      (Effect.post (fnstcwM16Effect p (encodeFnstcwM16 am).length am)) := by
  unfold encodeFnstcwM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := fnstcw_m16_triple_of_bytes p am hv hx hb
    rwa [show (0xD9 :: am.modrm 7 :: am.tail : List UInt8).length =
      2 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := fnstcw_m16_rex_triple_of_bytes p _ hrex.rexPrefix am hv hx hb
    rwa [show (am.rexByte false 0 :: 0xD9 :: am.modrm 7 :: am.tail).length =
      3 + am.tail.length by simp; omega]

theorem fnstcw_m16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple
      (fun s => SegStorePre p (r.prefixByte :: encodeFnstcwM16 am).length r base
          (fun t => am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeFnstcwM16 am).length)) 2 s
          ∧
        Prelude.CR0.SSEEnabled s.CR0)
      (codeRange p (r.prefixByte :: encodeFnstcwM16 am))
      (Effect.post (fnstcwM16SegEffect p (r.prefixByte :: encodeFnstcwM16 am).length base am)) := by
  unfold encodeFnstcwM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := fnstcw_m16_seg_triple_of_bytes p r base am hv hx hb
    rwa [show (r.prefixByte :: 0xD9 :: am.modrm 7 :: am.tail : List UInt8).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := fnstcw_m16_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix am hv hx hb
    rwa [show (r.prefixByte :: am.rexByte false 0 :: 0xD9 :: am.modrm 7 ::
      am.tail).length = 4 + am.tail.length by simp; omega]

theorem fnstcw_m16_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple
      (fun s => StorePre p (0x67 :: encodeFnstcwM16 am).length
          (fun t => am.addr32 t (p + BitVec.ofNat 64 (0x67 :: encodeFnstcwM16 am).length)) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0)
      (codeRange p (0x67 :: encodeFnstcwM16 am))
      (Effect.post (fnstcwM16A32Effect p (0x67 :: encodeFnstcwM16 am).length am)) := by
  unfold encodeFnstcwM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := fnstcw_m16_a32_triple_of_bytes p am hv hx hb
    rwa [show (0x67 :: 0xD9 :: am.modrm 7 :: am.tail : List UInt8).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := fnstcw_m16_rex_a32_triple_of_bytes p _ hrex.rexPrefix am hv hx hb
    rwa [show (0x67 :: am.rexByte false 0 :: 0xD9 :: am.modrm 7 ::
      am.tail).length = 4 + am.tail.length by simp; omega]

attribute [x86_compose] fnstcwM16Effect fnstcwM16SegEffect fnstcwM16A32Effect

@[x86_local] theorem fnstcwM16Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (fnstcwM16Effect p len am) := by
  effect_local [fnstcwM16Effect, x87CtlStoreEffect]

@[x86_local] theorem fnstcwM16SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} : Effect.Local (fnstcwM16SegEffect p len base am) := by
  effect_local [fnstcwM16SegEffect, x87CtlStoreEffect]

@[x86_local] theorem fnstcwM16A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (fnstcwM16A32Effect p len am) := by
  effect_local [fnstcwM16A32Effect, x87CtlStoreEffect]

end X86Proofs
