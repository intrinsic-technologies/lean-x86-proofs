import X86Proofs.Instructions.Fnstsw.Generated.M16.Step
import X86Proofs.Instructions.Fnstsw.Generated.M16.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fnstswM16Effect (p : BitVec 64) (len : Nat) (cc : BitVec 4) (am : AddrMode) (s : RamState) :
    Effect :=
  x87CtlStoreEffect p len (am.addr s (p + BitVec.ofNat 64 len))
      (((Operand.fsw : Operand 16).read s) ||| ccWord cc)

@[simp] theorem fnstswM16Effect_components (p : BitVec 64) (len : Nat) (cc : BitVec 4)
    (am : AddrMode)
    (s : RamState) : (fnstswM16Effect p len cc am s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) 2, .fcc, .rip] := by
  simp only [fnstswM16Effect, x87CtlStoreEffect_components]

def fnstswM16SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (cc : BitVec 4)
    (am : AddrMode)
    (s : RamState) : Effect :=
  x87CtlStoreEffect p len (base + am.addr s (p + BitVec.ofNat 64 len))
      (((Operand.fsw : Operand 16).read s) ||| ccWord cc)

@[simp] theorem fnstswM16SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (cc : BitVec 4) (am : AddrMode) (s : RamState) :
    (fnstswM16SegEffect p len base cc am s).components =
        [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) 2, .fcc, .rip] := by
  simp only [fnstswM16SegEffect, x87CtlStoreEffect_components]

def fnstswM16A32Effect (p : BitVec 64) (len : Nat) (cc : BitVec 4) (am : AddrMode) (s : RamState) :
    Effect :=
  x87CtlStoreEffect p len (am.addr32 s (p + BitVec.ofNat 64 len))
      (((Operand.fsw : Operand 16).read s) ||| ccWord cc)

@[simp] theorem fnstswM16A32Effect_components (p : BitVec 64) (len : Nat) (cc : BitVec 4)
    (am : AddrMode)
    (s : RamState) : (fnstswM16A32Effect p len cc am s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) 2, .fcc, .rip] := by
  simp only [fnstswM16A32Effect, x87CtlStoreEffect_components]

theorem fnstsw_m16_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => StorePre p (2 + am.tail.length)
          (fun t => am.addr t (p + BitVec.ofNat 64 (2 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswCC s.FP87_Status = cc)
      (codeRange p (0xDD :: am.modrm 7 :: am.tail))
      (fnstswM16Effect p (2 + am.tail.length) cc am) := by
  rintro s h hcode ⟨⟨hp, hwrite, -⟩, hcr0, hcc⟩
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := fnstsw_m16_step s h hcr0 []
    (by simp) (by simp) (by rfl) (by rfl) (by rfl) am hv
        (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hwrite)
  dsimp only at hstep
  refine
      (fun hh =>
      ⟨_, hstep, ReadyToStep.of_x87Store h hh rfl (by exact hwrite.low) (by exact hwrite.tables),
      hh⟩) ?_
  refine x87CtlStoreEffect_holds h _ s.RIP _ _ _ ?_ _ ?_
  · rw [← hcc, Operand.read_fsw, fswRest_or_ccWord]
    rfl
  · exact fswRest_fswCCOracle _ _

theorem fnstsw_m16_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => StorePre p (2 + am.tail.length)
          (fun t => am.addr t (p + BitVec.ofNat 64 (2 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswCC s.FP87_Status = cc)
      (codeRange p (0xDD :: am.modrm 7 :: am.tail))
      (Effect.post (fnstswM16Effect p (2 + am.tail.length) cc am)) :=
  Triple.of_effect (fun _ hpre => x87CtlStoreEffect_avoids hpre.1.code
    (by simp; omega))
    (fnstsw_m16_effect_step p cc am hv hx hb)

theorem fnstsw_m16_rex_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => StorePre p (3 + am.tail.length)
          (fun t => am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswCC s.FP87_Status = cc)
      (codeRange p (rex :: 0xDD :: am.modrm 7 :: am.tail))
      (fnstswM16Effect p (3 + am.tail.length) cc am) := by
  rintro s h hcode ⟨⟨hp, hwrite, -⟩, hcr0, hcc⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := fnstsw_m16_step s h hcr0 [rex]
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
  · rw [← hcc, Operand.read_fsw, fswRest_or_ccWord]
    rfl
  · exact fswRest_fswCCOracle _ _

theorem fnstsw_m16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => StorePre p (3 + am.tail.length)
          (fun t => am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswCC s.FP87_Status = cc)
      (codeRange p (rex :: 0xDD :: am.modrm 7 :: am.tail))
      (Effect.post (fnstswM16Effect p (3 + am.tail.length) cc am)) :=
  Triple.of_effect (fun _ hpre => x87CtlStoreEffect_avoids hpre.1.code
    (by simp; omega))
    (fnstsw_m16_rex_effect_step p cc rex hr am hv hx hb)

theorem fnstsw_m16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (cc : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => SegStorePre p (3 + am.tail.length) r base
          (fun t => am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswCC s.FP87_Status = cc)
      (codeRange p (r.prefixByte :: 0xDD :: am.modrm 7 :: am.tail))
      (fnstswM16SegEffect p (3 + am.tail.length) base cc am) := by
  rintro s h hcode ⟨⟨⟨hp, hwrite, -⟩, ⟨hseg, hbase⟩⟩, hcr0, hcc⟩
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
  have hstep := fnstsw_m16_step s h hcr0 [r.prefixByte]
    (scanPrefix_seg_cons r (by simp)) (by simp) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hwrite)
  simp only [hsc, segAddr_withSeg] at hstep
  refine
      (fun hh =>
      ⟨_, hstep, ReadyToStep.of_x87Store h hh rfl (by exact hwrite.low) (by exact hwrite.tables),
      hh⟩) ?_
  refine x87CtlStoreEffect_holds h _ s.RIP _ _ _ ?_ _ ?_
  · rw [← hcc, Operand.read_fsw, fswRest_or_ccWord]
    rfl
  · exact fswRest_fswCCOracle _ _

theorem fnstsw_m16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (cc : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => SegStorePre p (3 + am.tail.length) r base
          (fun t => am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswCC s.FP87_Status = cc)
      (codeRange p (r.prefixByte :: 0xDD :: am.modrm 7 :: am.tail))
      (Effect.post (fnstswM16SegEffect p (3 + am.tail.length) base cc am)) :=
  Triple.of_effect (fun _ hpre => x87CtlStoreEffect_avoids hpre.1.store.code
    (by simp; omega))
    (fnstsw_m16_seg_effect_step p r base cc am hv hx hb)

theorem fnstsw_m16_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => SegStorePre p (4 + am.tail.length) r base
          (fun t => am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswCC s.FP87_Status = cc)
      (codeRange p (r.prefixByte :: rex :: 0xDD :: am.modrm 7 :: am.tail))
      (fnstswM16SegEffect p (4 + am.tail.length) base cc am) := by
  rintro s h hcode ⟨⟨⟨hp, hwrite, -⟩, ⟨hseg, hbase⟩⟩, hcr0, hcc⟩
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
  have hstep := fnstsw_m16_step s h hcr0 [r.prefixByte, rex]
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
  · rw [← hcc, Operand.read_fsw, fswRest_or_ccWord]
    rfl
  · exact fswRest_fswCCOracle _ _

theorem fnstsw_m16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => SegStorePre p (4 + am.tail.length) r base
          (fun t => am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswCC s.FP87_Status = cc)
      (codeRange p (r.prefixByte :: rex :: 0xDD :: am.modrm 7 :: am.tail))
      (Effect.post (fnstswM16SegEffect p (4 + am.tail.length) base cc am)) :=
  Triple.of_effect (fun _ hpre => x87CtlStoreEffect_avoids hpre.1.store.code
    (by simp; omega))
    (fnstsw_m16_rex_seg_effect_step p r base cc rex hr am hv hx hb)

theorem fnstsw_m16_a32_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => StorePre p (3 + am.tail.length)
          (fun t => am.addr32 t (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswCC s.FP87_Status = cc)
      (codeRange p (0x67 :: 0xDD :: am.modrm 7 :: am.tail))
      (fnstswM16A32Effect p (3 + am.tail.length) cc am) := by
  rintro s h hcode ⟨⟨hp, hwrite, -⟩, hcr0, hcc⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := fnstsw_m16_a32_step s h hcr0 [0x67]
    (scanPrefix_asz_cons (by simp)) (by simp) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hwrite)
  simp only [hsc] at hstep
  refine
      (fun hh =>
      ⟨_, hstep, ReadyToStep.of_x87Store h hh rfl (by exact hwrite.low) (by exact hwrite.tables),
      hh⟩) ?_
  refine x87CtlStoreEffect_holds h _ s.RIP _ _ _ ?_ _ ?_
  · rw [← hcc, Operand.read_fsw, fswRest_or_ccWord]
    rfl
  · exact fswRest_fswCCOracle _ _

theorem fnstsw_m16_a32_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => StorePre p (3 + am.tail.length)
          (fun t => am.addr32 t (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswCC s.FP87_Status = cc)
      (codeRange p (0x67 :: 0xDD :: am.modrm 7 :: am.tail))
      (Effect.post (fnstswM16A32Effect p (3 + am.tail.length) cc am)) :=
  Triple.of_effect (fun _ hpre => x87CtlStoreEffect_avoids hpre.1.code
    (by simp; omega))
    (fnstsw_m16_a32_effect_step p cc am hv hx hb)

theorem fnstsw_m16_rex_a32_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => StorePre p (4 + am.tail.length)
          (fun t => am.addr32 t (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswCC s.FP87_Status = cc)
      (codeRange p (0x67 :: rex :: 0xDD :: am.modrm 7 :: am.tail))
      (fnstswM16A32Effect p (4 + am.tail.length) cc am) := by
  rintro s h hcode ⟨⟨hp, hwrite, -⟩, hcr0, hcc⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := fnstsw_m16_a32_step s h hcr0 [0x67, rex]
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
  · rw [← hcc, Operand.read_fsw, fswRest_or_ccWord]
    rfl
  · exact fswRest_fswCCOracle _ _

theorem fnstsw_m16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => StorePre p (4 + am.tail.length)
          (fun t => am.addr32 t (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswCC s.FP87_Status = cc)
      (codeRange p (0x67 :: rex :: 0xDD :: am.modrm 7 :: am.tail))
      (Effect.post (fnstswM16A32Effect p (4 + am.tail.length) cc am)) :=
  Triple.of_effect (fun _ hpre => x87CtlStoreEffect_avoids hpre.1.code
    (by simp; omega))
    (fnstsw_m16_rex_a32_effect_step p cc rex hr am hv hx hb)

theorem fnstsw_m16_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (am : AddrMode) (hv : am.Valid)
    :
    Triple
      (fun s => StorePre p (encodeFnstswM16 am).length
          (fun t => am.addr t (p + BitVec.ofNat 64 (encodeFnstswM16 am).length)) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswCC s.FP87_Status = cc)
      (codeRange p (encodeFnstswM16 am))
      (Effect.post (fnstswM16Effect p (encodeFnstswM16 am).length cc am)) := by
  unfold encodeFnstswM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := fnstsw_m16_triple_of_bytes p cc am hv hx hb
    rwa [show (0xDD :: am.modrm 7 :: am.tail : List UInt8).length =
      2 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := fnstsw_m16_rex_triple_of_bytes p cc _ hrex.rexPrefix am hv hx hb
    rwa [show (am.rexByte false 0 :: 0xDD :: am.modrm 7 :: am.tail).length =
      3 + am.tail.length by simp; omega]

theorem fnstsw_m16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (cc : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple
      (fun s => SegStorePre p (r.prefixByte :: encodeFnstswM16 am).length r base
          (fun t => am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeFnstswM16 am).length)) 2 s
          ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswCC s.FP87_Status = cc)
      (codeRange p (r.prefixByte :: encodeFnstswM16 am))
      (Effect.post (fnstswM16SegEffect p (r.prefixByte :: encodeFnstswM16 am).length base cc am)) :=
          by
  unfold encodeFnstswM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := fnstsw_m16_seg_triple_of_bytes p r base cc am hv hx hb
    rwa [show (r.prefixByte :: 0xDD :: am.modrm 7 :: am.tail : List UInt8).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := fnstsw_m16_rex_seg_triple_of_bytes p r base cc _ hrex.rexPrefix am hv hx hb
    rwa [show (r.prefixByte :: am.rexByte false 0 :: 0xDD :: am.modrm 7 ::
      am.tail).length = 4 + am.tail.length by simp; omega]

theorem fnstsw_m16_a32_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (fun s => StorePre p (0x67 :: encodeFnstswM16 am).length
          (fun t => am.addr32 t (p + BitVec.ofNat 64 (0x67 :: encodeFnstswM16 am).length)) 2 s ∧
        Prelude.CR0.SSEEnabled s.CR0 ∧
        fswCC s.FP87_Status = cc)
      (codeRange p (0x67 :: encodeFnstswM16 am))
      (Effect.post (fnstswM16A32Effect p (0x67 :: encodeFnstswM16 am).length cc am)) := by
  unfold encodeFnstswM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := fnstsw_m16_a32_triple_of_bytes p cc am hv hx hb
    rwa [show (0x67 :: 0xDD :: am.modrm 7 :: am.tail : List UInt8).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := fnstsw_m16_rex_a32_triple_of_bytes p cc _ hrex.rexPrefix am hv hx hb
    rwa [show (0x67 :: am.rexByte false 0 :: 0xDD :: am.modrm 7 ::
      am.tail).length = 4 + am.tail.length by simp; omega]

attribute [x86_compose] fnstswM16Effect fnstswM16SegEffect fnstswM16A32Effect

@[x86_local] theorem fnstswM16Effect_local {p : BitVec 64} {len : Nat} {cc : BitVec 4}
    {am : AddrMode} :
    Effect.Local (fnstswM16Effect p len cc am) := by
  effect_local [fnstswM16Effect, x87CtlStoreEffect]

@[x86_local] theorem fnstswM16SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {cc : BitVec 4} {am : AddrMode} : Effect.Local (fnstswM16SegEffect p len base cc am) := by
  effect_local [fnstswM16SegEffect, x87CtlStoreEffect]

@[x86_local] theorem fnstswM16A32Effect_local {p : BitVec 64} {len : Nat} {cc : BitVec 4}
    {am : AddrMode} :
    Effect.Local (fnstswM16A32Effect p len cc am) := by
  effect_local [fnstswM16A32Effect, x87CtlStoreEffect]

end X86Proofs
