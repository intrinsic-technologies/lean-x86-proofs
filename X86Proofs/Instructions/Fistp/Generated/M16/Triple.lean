import X86Proofs.Instructions.Fistp.Generated.M16.Step
import X86Proofs.Instructions.Fistp.Generated.M16.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fistpM16Effect (p : BitVec 64) (len : Nat) (top : BitVec 3) (am : AddrMode) (s : RamState) :
    Effect :=
  let r := x87ToInt (fcwRC ((Operand.fcw : Operand 16).read s)) 16
      ((Operand.fpr (top) : Operand 80).read s)
  x87StoreEffect p len (am.addr s (p + BitVec.ofNat 64 len)) r.1 []
    (ftwSet ((Operand.ftw : Operand 16).read s) top 3)
    (fswSetTop (fswOrFlags ((Operand.fsw : Operand 16).read s) (fistFlags r.2.2)) (top + 1)) (2)
        (ccC1 r.2.1) s

@[simp] theorem fistpM16Effect_components (p : BitVec 64) (len : Nat) (top : BitVec 3)
    (am : AddrMode) (s : RamState) :
    (fistpM16Effect p len top am s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) 2, .ftw, .fsw, .fcc, .fpuPtr, .rip] := by
  simp only
      [fistpM16Effect, x87StoreEffect_components, Nat.reduceDiv, List.map_nil, List.nil_append]

def fistpM16SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (top : BitVec 3)
    (am : AddrMode) (s : RamState) : Effect :=
  let r := x87ToInt (fcwRC ((Operand.fcw : Operand 16).read s)) 16
      ((Operand.fpr (top) : Operand 80).read s)
  x87StoreEffect p len (base + am.addr s (p + BitVec.ofNat 64 len)) r.1 []
    (ftwSet ((Operand.ftw : Operand 16).read s) top 3)
    (fswSetTop (fswOrFlags ((Operand.fsw : Operand 16).read s) (fistFlags r.2.2)) (top + 1)) (2)
        (ccC1 r.2.1) s

@[simp] theorem fistpM16SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (top : BitVec 3) (am : AddrMode) (s : RamState) :
    (fistpM16SegEffect p len base top am s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) 2, .ftw, .fsw, .fcc, .fpuPtr, .rip] := by
  simp only [fistpM16SegEffect, x87StoreEffect_components, Nat.reduceDiv, List.map_nil,
    List.nil_append]

def fistpM16A32Effect (p : BitVec 64) (len : Nat) (top : BitVec 3) (am : AddrMode) (s : RamState) :
    Effect :=
  let r := x87ToInt (fcwRC ((Operand.fcw : Operand 16).read s)) 16
      ((Operand.fpr (top) : Operand 80).read s)
  x87StoreEffect p len (am.addr32 s (p + BitVec.ofNat 64 len)) r.1 []
    (ftwSet ((Operand.ftw : Operand 16).read s) top 3)
    (fswSetTop (fswOrFlags ((Operand.fsw : Operand 16).read s) (fistFlags r.2.2)) (top + 1)) (2)
        (ccC1 r.2.1) s

@[simp] theorem fistpM16A32Effect_components (p : BitVec 64) (len : Nat) (top : BitVec 3)
    (am : AddrMode) (s : RamState) :
    (fistpM16A32Effect p len top am s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) 2, .ftw, .fsw, .fcc, .fpuPtr, .rip] := by
  simp only [fistpM16A32Effect, x87StoreEffect_components, Nat.reduceDiv, List.map_nil,
    List.nil_append]

theorem fistp_m16_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => X87StorePre p top (2 + am.tail.length)
        (fun t => am.addr t (p + BitVec.ofNat 64 (2 + am.tail.length))) 2 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToIntOk (fcwRC s.FP87_Control) 16 s.FP87[fprIndex (top)])
      (codeRange p (0xDF :: am.modrm 3 :: am.tail))
      (fistpM16Effect p (2 + am.tail.length) top am) := by
  rintro s h hcode ⟨⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, hwrite, -⟩, h0, hok⟩
  subst hp htop
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := fistp_m16_step s h hcr0 hes hm hfdp []
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

theorem fistp_m16_triple_of_bytes [Bindings] (p : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => X87StorePre p top (2 + am.tail.length)
        (fun t => am.addr t (p + BitVec.ofNat 64 (2 + am.tail.length))) 2 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToIntOk (fcwRC s.FP87_Control) 16 s.FP87[fprIndex (top)])
      (codeRange p (0xDF :: am.modrm 3 :: am.tail))
      (Effect.post (fistpM16Effect p (2 + am.tail.length) top am)) :=
  Triple.of_effect (fun _ hpre => x87StoreEffect_avoids hpre.1.code (by simp; omega))
    (fistp_m16_effect_step p top am hv hx hb)

theorem fistp_m16_rex_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => X87StorePre p top (3 + am.tail.length)
        (fun t => am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToIntOk (fcwRC s.FP87_Control) 16 s.FP87[fprIndex (top)])
      (codeRange p (rex :: 0xDF :: am.modrm 3 :: am.tail))
      (fistpM16Effect p (3 + am.tail.length) top am) := by
  rintro s h hcode ⟨⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, hwrite, -⟩, h0, hok⟩
  subst hp htop
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := fistp_m16_step s h hcr0 hes hm hfdp [rex]
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

theorem fistp_m16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (top : BitVec 3) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => X87StorePre p top (3 + am.tail.length)
        (fun t => am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToIntOk (fcwRC s.FP87_Control) 16 s.FP87[fprIndex (top)])
      (codeRange p (rex :: 0xDF :: am.modrm 3 :: am.tail))
      (Effect.post (fistpM16Effect p (3 + am.tail.length) top am)) :=
  Triple.of_effect (fun _ hpre => x87StoreEffect_avoids hpre.1.code (by simp; omega))
    (fistp_m16_rex_effect_step p top rex hr am hv hx hb)

theorem fistp_m16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => X87StorePre p top (3 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧ r.Ready base s
            ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToIntOk (fcwRC s.FP87_Control) 16 s.FP87[fprIndex (top)])
      (codeRange p (r.prefixByte :: 0xDF :: am.modrm 3 :: am.tail))
      (fistpM16SegEffect p (3 + am.tail.length) base top am) := by
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
  have hstep := fistp_m16_step s h hcr0 hes hm hfdp [r.prefixByte]
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

theorem fistp_m16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => X87StorePre p top (3 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧ r.Ready base s
            ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToIntOk (fcwRC s.FP87_Control) 16 s.FP87[fprIndex (top)])
      (codeRange p (r.prefixByte :: 0xDF :: am.modrm 3 :: am.tail))
      (Effect.post (fistpM16SegEffect p (3 + am.tail.length) base top am)) :=
  Triple.of_effect (fun _ hpre => x87StoreEffect_avoids hpre.1.code (by simp; omega))
    (fistp_m16_seg_effect_step p r base top am hv hx hb)

theorem fistp_m16_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (top : BitVec 3) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => X87StorePre p top (4 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧ r.Ready base s
            ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToIntOk (fcwRC s.FP87_Control) 16 s.FP87[fprIndex (top)])
      (codeRange p (r.prefixByte :: rex :: 0xDF :: am.modrm 3 :: am.tail))
      (fistpM16SegEffect p (4 + am.tail.length) base top am) := by
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
  have hstep := fistp_m16_step s h hcr0 hes hm hfdp [r.prefixByte, rex]
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

theorem fistp_m16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (top : BitVec 3) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => X87StorePre p top (4 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧ r.Ready base s
            ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToIntOk (fcwRC s.FP87_Control) 16 s.FP87[fprIndex (top)])
      (codeRange p (r.prefixByte :: rex :: 0xDF :: am.modrm 3 :: am.tail))
      (Effect.post (fistpM16SegEffect p (4 + am.tail.length) base top am)) :=
  Triple.of_effect (fun _ hpre => x87StoreEffect_avoids hpre.1.code (by simp; omega))
    (fistp_m16_rex_seg_effect_step p r base top rex hr am hv hx hb)

theorem fistp_m16_a32_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => X87StorePre p top (3 + am.tail.length)
        (fun t => am.addr32 t (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToIntOk (fcwRC s.FP87_Control) 16 s.FP87[fprIndex (top)])
      (codeRange p (0x67 :: 0xDF :: am.modrm 3 :: am.tail))
      (fistpM16A32Effect p (3 + am.tail.length) top am) := by
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
  have hstep := fistp_m16_a32_step s h hcr0 hes hm hfdp [0x67]
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

theorem fistp_m16_a32_triple_of_bytes [Bindings] (p : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => X87StorePre p top (3 + am.tail.length)
        (fun t => am.addr32 t (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToIntOk (fcwRC s.FP87_Control) 16 s.FP87[fprIndex (top)])
      (codeRange p (0x67 :: 0xDF :: am.modrm 3 :: am.tail))
      (Effect.post (fistpM16A32Effect p (3 + am.tail.length) top am)) :=
  Triple.of_effect (fun _ hpre => x87StoreEffect_avoids hpre.1.code (by simp; omega))
    (fistp_m16_a32_effect_step p top am hv hx hb)

theorem fistp_m16_rex_a32_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => X87StorePre p top (4 + am.tail.length)
        (fun t => am.addr32 t (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToIntOk (fcwRC s.FP87_Control) 16 s.FP87[fprIndex (top)])
      (codeRange p (0x67 :: rex :: 0xDF :: am.modrm 3 :: am.tail))
      (fistpM16A32Effect p (4 + am.tail.length) top am) := by
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
  have hstep := fistp_m16_a32_step s h hcr0 hes hm hfdp [0x67, rex]
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

theorem fistp_m16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (top : BitVec 3) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => X87StorePre p top (4 + am.tail.length)
        (fun t => am.addr32 t (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToIntOk (fcwRC s.FP87_Control) 16 s.FP87[fprIndex (top)])
      (codeRange p (0x67 :: rex :: 0xDF :: am.modrm 3 :: am.tail))
      (Effect.post (fistpM16A32Effect p (4 + am.tail.length) top am)) :=
  Triple.of_effect (fun _ hpre => x87StoreEffect_avoids hpre.1.code (by simp; omega))
    (fistp_m16_rex_a32_effect_step p top rex hr am hv hx hb)

theorem fistp_m16_triple [Bindings] (p : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (fun s => X87StorePre p top (encodeFistpM16 am).length
        (fun t => am.addr t (p + BitVec.ofNat 64 (encodeFistpM16 am).length)) 2 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToIntOk (fcwRC s.FP87_Control) 16 s.FP87[fprIndex (top)])
      (codeRange p (encodeFistpM16 am))
      (Effect.post (fistpM16Effect p (encodeFistpM16 am).length top am)) := by
  unfold encodeFistpM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := fistp_m16_triple_of_bytes p top am hv hx hb
    rwa [show (0xDF :: am.modrm 3 :: am.tail : List UInt8).length =
      2 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := fistp_m16_rex_triple_of_bytes p top _ hrex.rexPrefix am hv hx hb
    rwa [show (am.rexByte false 0 :: 0xDF :: am.modrm 3 :: am.tail).length =
      3 + am.tail.length by simp; omega]

theorem fistp_m16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (top : BitVec 3) (am : AddrMode) (hv : am.Valid) :
    Triple
      (fun s => X87StorePre p top (r.prefixByte :: encodeFistpM16 am).length
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeFistpM16 am).length))
            2 s ∧ r.Ready base s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToIntOk (fcwRC s.FP87_Control) 16 s.FP87[fprIndex (top)])
      (codeRange p (r.prefixByte :: encodeFistpM16 am))
      (Effect.post (fistpM16SegEffect p (r.prefixByte :: encodeFistpM16 am).length base top am)) :=
          by
  unfold encodeFistpM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := fistp_m16_seg_triple_of_bytes p r base top am hv hx hb
    rwa [show (r.prefixByte :: 0xDF :: am.modrm 3 :: am.tail : List UInt8).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := fistp_m16_rex_seg_triple_of_bytes p r base top _ hrex.rexPrefix am hv hx hb
    rwa [show (r.prefixByte :: am.rexByte false 0 :: 0xDF :: am.modrm 3 ::
      am.tail).length = 4 + am.tail.length by simp; omega]

theorem fistp_m16_a32_triple [Bindings] (p : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (fun s => X87StorePre p top (0x67 :: encodeFistpM16 am).length
        (fun t => am.addr32 t (p + BitVec.ofNat 64 (0x67 :: encodeFistpM16 am).length)) 2 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ToIntOk (fcwRC s.FP87_Control) 16 s.FP87[fprIndex (top)])
      (codeRange p (0x67 :: encodeFistpM16 am))
      (Effect.post (fistpM16A32Effect p (0x67 :: encodeFistpM16 am).length top am)) := by
  unfold encodeFistpM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := fistp_m16_a32_triple_of_bytes p top am hv hx hb
    rwa [show (0x67 :: 0xDF :: am.modrm 3 :: am.tail : List UInt8).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := fistp_m16_rex_a32_triple_of_bytes p top _ hrex.rexPrefix am hv hx hb
    rwa [show (0x67 :: am.rexByte false 0 :: 0xDF :: am.modrm 3 ::
      am.tail).length = 4 + am.tail.length by simp; omega]

attribute [x86_compose] fistpM16Effect fistpM16SegEffect fistpM16A32Effect

@[x86_local] theorem fistpM16Effect_local {p : BitVec 64} {len : Nat} {top : BitVec 3}
    {am : AddrMode} : Effect.Local (fistpM16Effect p len top am) := by
  effect_local [fistpM16Effect, x87StoreEffect, x87Effect]

@[x86_local] theorem fistpM16SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {top : BitVec 3} {am : AddrMode} : Effect.Local (fistpM16SegEffect p len base top am) := by
  effect_local [fistpM16SegEffect, x87StoreEffect, x87Effect]

@[x86_local] theorem fistpM16A32Effect_local {p : BitVec 64} {len : Nat} {top : BitVec 3}
    {am : AddrMode} : Effect.Local (fistpM16A32Effect p len top am) := by
  effect_local [fistpM16A32Effect, x87StoreEffect, x87Effect]

end X86Proofs
