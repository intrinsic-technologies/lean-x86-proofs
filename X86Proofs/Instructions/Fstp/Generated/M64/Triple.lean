import X86Proofs.Instructions.Fstp.Generated.M64.Step
import X86Proofs.Instructions.Fstp.Generated.M64.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fstpM64Effect (p : BitVec 64) (len : Nat) (top : BitVec 3) (am : AddrMode) (s : RamState) :
    Effect :=
  let r := x87ToFloat 64 ((Operand.fcw : Operand 16).read s)
      ((Operand.fpr (top) : Operand 80).read s)
  x87StoreEffect p len (am.addr s (p + BitVec.ofNat 64 len)) r.1 []
    (ftwSet ((Operand.ftw : Operand 16).read s) top 3)
    (fswSetTop (fswOrFlags ((Operand.fsw : Operand 16).read s) r.2.2) (top + 1)) (2) (ccC1 r.2.1) s

@[simp] theorem fstpM64Effect_components (p : BitVec 64) (len : Nat) (top : BitVec 3)
    (am : AddrMode) (s : RamState) :
    (fstpM64Effect p len top am s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) 8, .ftw, .fsw, .fcc, .fpuPtr, .rip] := by
  simp only [fstpM64Effect, x87StoreEffect_components, Nat.reduceDiv, List.map_nil, List.nil_append]

def fstpM64SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (top : BitVec 3)
    (am : AddrMode) (s : RamState) : Effect :=
  let r := x87ToFloat 64 ((Operand.fcw : Operand 16).read s)
      ((Operand.fpr (top) : Operand 80).read s)
  x87StoreEffect p len (base + am.addr s (p + BitVec.ofNat 64 len)) r.1 []
    (ftwSet ((Operand.ftw : Operand 16).read s) top 3)
    (fswSetTop (fswOrFlags ((Operand.fsw : Operand 16).read s) r.2.2) (top + 1)) (2) (ccC1 r.2.1) s

@[simp] theorem fstpM64SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (top : BitVec 3) (am : AddrMode) (s : RamState) :
    (fstpM64SegEffect p len base top am s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) 8, .ftw, .fsw, .fcc, .fpuPtr, .rip] := by
  simp only [fstpM64SegEffect, x87StoreEffect_components, Nat.reduceDiv, List.map_nil,
    List.nil_append]

def fstpM64A32Effect (p : BitVec 64) (len : Nat) (top : BitVec 3) (am : AddrMode) (s : RamState) :
    Effect :=
  let r := x87ToFloat 64 ((Operand.fcw : Operand 16).read s)
      ((Operand.fpr (top) : Operand 80).read s)
  x87StoreEffect p len (am.addr32 s (p + BitVec.ofNat 64 len)) r.1 []
    (ftwSet ((Operand.ftw : Operand 16).read s) top 3)
    (fswSetTop (fswOrFlags ((Operand.fsw : Operand 16).read s) r.2.2) (top + 1)) (2) (ccC1 r.2.1) s

@[simp] theorem fstpM64A32Effect_components (p : BitVec 64) (len : Nat) (top : BitVec 3)
    (am : AddrMode) (s : RamState) :
    (fstpM64A32Effect p len top am s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) 8, .ftw, .fsw, .fcc, .fpuPtr, .rip] := by
  simp only [fstpM64A32Effect, x87StoreEffect_components, Nat.reduceDiv, List.map_nil,
    List.nil_append]

theorem fstp_m64_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => X87StorePre p top (2 + am.tail.length)
        (fun t => am.addr t (p + BitVec.ofNat 64 (2 + am.tail.length))) 8 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToFloatOk 64 s.FP87_Control s.FP87[fprIndex (top)])
      (codeRange p (0xDD :: am.modrm 3 :: am.tail))
      (fstpM64Effect p (2 + am.tail.length) top am) := by
  rintro s h hcode ⟨⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, hwrite, -⟩, h0, hok⟩
  subst hp htop
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := fstp_m64_step s h hcr0 hes hm hfdp []
    (by simp) (by simp) (by rfl) (by rfl) (by rfl) am hv
        (by exact (AddrContext.legacy _ am hx hb).toSeg)
    h0
    hok
    hcode.bytesAt hlow (by exact hwrite)
  dsimp only at hstep
  refine
      (fun hh =>
      ⟨_, hstep, ReadyToStep.of_x87Store h hh rfl (by exact hwrite.low) (by exact hwrite.tables),
      hh⟩) ?_
  refine x87StoreEffect_holds h _ s.RIP rfl (by decide) (by decide) _ _ _ (fun _ => rfl) _ _ _ _ _ _
      _ _ _ _ rfl ?_ ?_ ?_ ?_ ?_
  · exact fun _ h => absurd h List.not_mem_nil
  · exact fun _ _ => rfl
  · x87_simp
  · simp only [Operand.read_fsw, fswRest_fswSetTop, fswRest_x87StoreStatus]
    rfl
  · simp only [fswCC_fswSetTop]
    exact fswCC_x87StoreStatus _ _ _ _

theorem fstp_m64_triple_of_bytes [Bindings] (p : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => X87StorePre p top (2 + am.tail.length)
        (fun t => am.addr t (p + BitVec.ofNat 64 (2 + am.tail.length))) 8 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToFloatOk 64 s.FP87_Control s.FP87[fprIndex (top)])
      (codeRange p (0xDD :: am.modrm 3 :: am.tail))
      (Effect.post (fstpM64Effect p (2 + am.tail.length) top am)) :=
  Triple.of_effect (fun _ hpre => x87StoreEffect_avoids hpre.1.code (by simp; omega))
    (fstp_m64_effect_step p top am hv hx hb)

theorem fstp_m64_rex_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => X87StorePre p top (3 + am.tail.length)
        (fun t => am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length))) 8 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToFloatOk 64 s.FP87_Control s.FP87[fprIndex (top)])
      (codeRange p (rex :: 0xDD :: am.modrm 3 :: am.tail))
      (fstpM64Effect p (3 + am.tail.length) top am) := by
  rintro s h hcode ⟨⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, hwrite, -⟩, h0, hok⟩
  subst hp htop
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := fstp_m64_step s h hcr0 hes hm hfdp [rex]
    (by simpa using hr.scanPrefix) (by simp) (by rw [scanContext_rex _ _ hr]; rfl)
        (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) am hv
        (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    h0
    hok
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hwrite)
  simp only [scanContext_rex _ _ hr] at hstep
  refine
      (fun hh =>
      ⟨_, hstep, ReadyToStep.of_x87Store h hh rfl (by exact hwrite.low) (by exact hwrite.tables),
      hh⟩) ?_
  refine x87StoreEffect_holds h _ s.RIP rfl (by decide) (by decide) _ _ _ (fun _ => rfl) _ _ _ _ _ _
      _ _ _ _ rfl ?_ ?_ ?_ ?_ ?_
  · exact fun _ h => absurd h List.not_mem_nil
  · exact fun _ _ => rfl
  · x87_simp
  · simp only [Operand.read_fsw, fswRest_fswSetTop, fswRest_x87StoreStatus]
    rfl
  · simp only [fswCC_fswSetTop]
    exact fswCC_x87StoreStatus _ _ _ _

theorem fstp_m64_rex_triple_of_bytes [Bindings] (p : BitVec 64) (top : BitVec 3) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => X87StorePre p top (3 + am.tail.length)
        (fun t => am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length))) 8 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToFloatOk 64 s.FP87_Control s.FP87[fprIndex (top)])
      (codeRange p (rex :: 0xDD :: am.modrm 3 :: am.tail))
      (Effect.post (fstpM64Effect p (3 + am.tail.length) top am)) :=
  Triple.of_effect (fun _ hpre => x87StoreEffect_avoids hpre.1.code (by simp; omega))
    (fstp_m64_rex_effect_step p top rex hr am hv hx hb)

theorem fstp_m64_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => X87StorePre p top (3 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length))) 8 s ∧ r.Ready base s
            ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToFloatOk 64 s.FP87_Control s.FP87[fprIndex (top)])
      (codeRange p (r.prefixByte :: 0xDD :: am.modrm 3 :: am.tail))
      (fstpM64SegEffect p (3 + am.tail.length) base top am) := by
  rintro s h hcode ⟨⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, hwrite, -⟩, ⟨hseg, hbase⟩, h0, hok⟩
  subst hp htop hbase
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
  have hstep := fstp_m64_step s h hcr0 hes hm hfdp [r.prefixByte]
    (scanPrefix_seg_cons r (by simp)) (by simp) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    h0
    hok
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hwrite)
  simp only [hsc, segAddr_withSeg] at hstep
  refine
      (fun hh =>
      ⟨_, hstep, ReadyToStep.of_x87Store h hh rfl (by exact hwrite.low) (by exact hwrite.tables),
      hh⟩) ?_
  refine x87StoreEffect_holds h _ s.RIP rfl (by decide) (by decide) _ _ _ (fun _ => rfl) _ _ _ _ _ _
      _ _ _ _ rfl ?_ ?_ ?_ ?_ ?_
  · exact fun _ h => absurd h List.not_mem_nil
  · exact fun _ _ => rfl
  · x87_simp
  · simp only [Operand.read_fsw, fswRest_fswSetTop, fswRest_x87StoreStatus]
    rfl
  · simp only [fswCC_fswSetTop]
    exact fswCC_x87StoreStatus _ _ _ _

theorem fstp_m64_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => X87StorePre p top (3 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length))) 8 s ∧ r.Ready base s
            ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToFloatOk 64 s.FP87_Control s.FP87[fprIndex (top)])
      (codeRange p (r.prefixByte :: 0xDD :: am.modrm 3 :: am.tail))
      (Effect.post (fstpM64SegEffect p (3 + am.tail.length) base top am)) :=
  Triple.of_effect (fun _ hpre => x87StoreEffect_avoids hpre.1.code (by simp; omega))
    (fstp_m64_seg_effect_step p r base top am hv hx hb)

theorem fstp_m64_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (top : BitVec 3) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => X87StorePre p top (4 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧ r.Ready base s
            ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToFloatOk 64 s.FP87_Control s.FP87[fprIndex (top)])
      (codeRange p (r.prefixByte :: rex :: 0xDD :: am.modrm 3 :: am.tail))
      (fstpM64SegEffect p (4 + am.tail.length) base top am) := by
  rintro s h hcode ⟨⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, hwrite, -⟩, ⟨hseg, hbase⟩, h0, hok⟩
  subst hp htop hbase
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := fstp_m64_step s h hcr0 hes hm hfdp [r.prefixByte, rex]
    (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl) am hv
        (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    h0
    hok
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hwrite)
  simp only [hsc, segAddr_withSeg] at hstep
  refine
      (fun hh =>
      ⟨_, hstep, ReadyToStep.of_x87Store h hh rfl (by exact hwrite.low) (by exact hwrite.tables),
      hh⟩) ?_
  refine x87StoreEffect_holds h _ s.RIP rfl (by decide) (by decide) _ _ _ (fun _ => rfl) _ _ _ _ _ _
      _ _ _ _ rfl ?_ ?_ ?_ ?_ ?_
  · exact fun _ h => absurd h List.not_mem_nil
  · exact fun _ _ => rfl
  · x87_simp
  · simp only [Operand.read_fsw, fswRest_fswSetTop, fswRest_x87StoreStatus]
    rfl
  · simp only [fswCC_fswSetTop]
    exact fswCC_x87StoreStatus _ _ _ _

theorem fstp_m64_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (top : BitVec 3) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => X87StorePre p top (4 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧ r.Ready base s
            ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToFloatOk 64 s.FP87_Control s.FP87[fprIndex (top)])
      (codeRange p (r.prefixByte :: rex :: 0xDD :: am.modrm 3 :: am.tail))
      (Effect.post (fstpM64SegEffect p (4 + am.tail.length) base top am)) :=
  Triple.of_effect (fun _ hpre => x87StoreEffect_avoids hpre.1.code (by simp; omega))
    (fstp_m64_rex_seg_effect_step p r base top rex hr am hv hx hb)

theorem fstp_m64_a32_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => X87StorePre p top (3 + am.tail.length)
        (fun t => am.addr32 t (p + BitVec.ofNat 64 (3 + am.tail.length))) 8 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToFloatOk 64 s.FP87_Control s.FP87[fprIndex (top)])
      (codeRange p (0x67 :: 0xDD :: am.modrm 3 :: am.tail))
      (fstpM64A32Effect p (3 + am.tail.length) top am) := by
  rintro s h hcode ⟨⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, hwrite, -⟩, h0, hok⟩
  subst hp htop
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := fstp_m64_a32_step s h hcr0 hes hm hfdp [0x67]
    (scanPrefix_asz_cons (by simp)) (by simp) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    h0
    hok
    hcode.bytesAt hlow (by rw [hsc]; exact hwrite)
  simp only [hsc] at hstep
  refine
      (fun hh =>
      ⟨_, hstep, ReadyToStep.of_x87Store h hh rfl (by exact hwrite.low) (by exact hwrite.tables),
      hh⟩) ?_
  refine x87StoreEffect_holds h _ s.RIP rfl (by decide) (by decide) _ _ _ (fun _ => rfl) _ _ _ _ _ _
      _ _ _ _ rfl ?_ ?_ ?_ ?_ ?_
  · exact fun _ h => absurd h List.not_mem_nil
  · exact fun _ _ => rfl
  · x87_simp
  · simp only [Operand.read_fsw, fswRest_fswSetTop, fswRest_x87StoreStatus]
    rfl
  · simp only [fswCC_fswSetTop]
    exact fswCC_x87StoreStatus _ _ _ _

theorem fstp_m64_a32_triple_of_bytes [Bindings] (p : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => X87StorePre p top (3 + am.tail.length)
        (fun t => am.addr32 t (p + BitVec.ofNat 64 (3 + am.tail.length))) 8 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToFloatOk 64 s.FP87_Control s.FP87[fprIndex (top)])
      (codeRange p (0x67 :: 0xDD :: am.modrm 3 :: am.tail))
      (Effect.post (fstpM64A32Effect p (3 + am.tail.length) top am)) :=
  Triple.of_effect (fun _ hpre => x87StoreEffect_avoids hpre.1.code (by simp; omega))
    (fstp_m64_a32_effect_step p top am hv hx hb)

theorem fstp_m64_rex_a32_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => X87StorePre p top (4 + am.tail.length)
        (fun t => am.addr32 t (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToFloatOk 64 s.FP87_Control s.FP87[fprIndex (top)])
      (codeRange p (0x67 :: rex :: 0xDD :: am.modrm 3 :: am.tail))
      (fstpM64A32Effect p (4 + am.tail.length) top am) := by
  rintro s h hcode ⟨⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, hwrite, -⟩, h0, hok⟩
  subst hp htop
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := fstp_m64_a32_step s h hcr0 hes hm hfdp [0x67, rex]
    (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl) am hv
        (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    h0
    hok
    hcode.bytesAt hlow (by rw [hsc]; exact hwrite)
  simp only [hsc] at hstep
  refine
      (fun hh =>
      ⟨_, hstep, ReadyToStep.of_x87Store h hh rfl (by exact hwrite.low) (by exact hwrite.tables),
      hh⟩) ?_
  refine x87StoreEffect_holds h _ s.RIP rfl (by decide) (by decide) _ _ _ (fun _ => rfl) _ _ _ _ _ _
      _ _ _ _ rfl ?_ ?_ ?_ ?_ ?_
  · exact fun _ h => absurd h List.not_mem_nil
  · exact fun _ _ => rfl
  · x87_simp
  · simp only [Operand.read_fsw, fswRest_fswSetTop, fswRest_x87StoreStatus]
    rfl
  · simp only [fswCC_fswSetTop]
    exact fswCC_x87StoreStatus _ _ _ _

theorem fstp_m64_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (top : BitVec 3) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => X87StorePre p top (4 + am.tail.length)
        (fun t => am.addr32 t (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToFloatOk 64 s.FP87_Control s.FP87[fprIndex (top)])
      (codeRange p (0x67 :: rex :: 0xDD :: am.modrm 3 :: am.tail))
      (Effect.post (fstpM64A32Effect p (4 + am.tail.length) top am)) :=
  Triple.of_effect (fun _ hpre => x87StoreEffect_avoids hpre.1.code (by simp; omega))
    (fstp_m64_rex_a32_effect_step p top rex hr am hv hx hb)

theorem fstp_m64_triple [Bindings] (p : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (fun s => X87StorePre p top (encodeFstpM64 am).length
        (fun t => am.addr t (p + BitVec.ofNat 64 (encodeFstpM64 am).length)) 8 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToFloatOk 64 s.FP87_Control s.FP87[fprIndex (top)])
      (codeRange p (encodeFstpM64 am))
      (Effect.post (fstpM64Effect p (encodeFstpM64 am).length top am)) := by
  unfold encodeFstpM64
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := fstp_m64_triple_of_bytes p top am hv hx hb
    rwa [show (0xDD :: am.modrm 3 :: am.tail : List UInt8).length =
      2 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := fstp_m64_rex_triple_of_bytes p top _ hrex.rexPrefix am hv hx hb
    rwa [show (am.rexByte false 0 :: 0xDD :: am.modrm 3 :: am.tail).length =
      3 + am.tail.length by simp; omega]

theorem fstp_m64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (top : BitVec 3) (am : AddrMode) (hv : am.Valid) :
    Triple
      (fun s => X87StorePre p top (r.prefixByte :: encodeFstpM64 am).length
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeFstpM64 am).length))
            8 s ∧ r.Ready base s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToFloatOk 64 s.FP87_Control s.FP87[fprIndex (top)])
      (codeRange p (r.prefixByte :: encodeFstpM64 am))
      (Effect.post (fstpM64SegEffect p (r.prefixByte :: encodeFstpM64 am).length base top am)) := by
  unfold encodeFstpM64
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := fstp_m64_seg_triple_of_bytes p r base top am hv hx hb
    rwa [show (r.prefixByte :: 0xDD :: am.modrm 3 :: am.tail : List UInt8).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := fstp_m64_rex_seg_triple_of_bytes p r base top _ hrex.rexPrefix am hv hx hb
    rwa [show (r.prefixByte :: am.rexByte false 0 :: 0xDD :: am.modrm 3 ::
      am.tail).length = 4 + am.tail.length by simp; omega]

theorem fstp_m64_a32_triple [Bindings] (p : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (fun s => X87StorePre p top (0x67 :: encodeFstpM64 am).length
        (fun t => am.addr32 t (p + BitVec.ofNat 64 (0x67 :: encodeFstpM64 am).length)) 8 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToFloatOk 64 s.FP87_Control s.FP87[fprIndex (top)])
      (codeRange p (0x67 :: encodeFstpM64 am))
      (Effect.post (fstpM64A32Effect p (0x67 :: encodeFstpM64 am).length top am)) := by
  unfold encodeFstpM64
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := fstp_m64_a32_triple_of_bytes p top am hv hx hb
    rwa [show (0x67 :: 0xDD :: am.modrm 3 :: am.tail : List UInt8).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := fstp_m64_rex_a32_triple_of_bytes p top _ hrex.rexPrefix am hv hx hb
    rwa [show (0x67 :: am.rexByte false 0 :: 0xDD :: am.modrm 3 ::
      am.tail).length = 4 + am.tail.length by simp; omega]

attribute [x86_compose] fstpM64Effect fstpM64SegEffect fstpM64A32Effect

@[x86_local] theorem fstpM64Effect_local {p : BitVec 64} {len : Nat} {top : BitVec 3}
    {am : AddrMode} : Effect.Local (fstpM64Effect p len top am) := by
  effect_local [fstpM64Effect, x87StoreEffect, x87Effect]

@[x86_local] theorem fstpM64SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {top : BitVec 3} {am : AddrMode} : Effect.Local (fstpM64SegEffect p len base top am) := by
  effect_local [fstpM64SegEffect, x87StoreEffect, x87Effect]

@[x86_local] theorem fstpM64A32Effect_local {p : BitVec 64} {len : Nat} {top : BitVec 3}
    {am : AddrMode} : Effect.Local (fstpM64A32Effect p len top am) := by
  effect_local [fstpM64A32Effect, x87StoreEffect, x87Effect]

end X86Proofs
