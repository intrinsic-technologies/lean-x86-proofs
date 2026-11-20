import X86Proofs.Instructions.Fmul.Generated.M32.Step
import X86Proofs.Instructions.Fmul.Generated.M32.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fmulM32Effect (p : BitVec 64) (len : Nat) (top : BitVec 3) (am : AddrMode) (s : RamState) :
    Effect :=
  let x := x87FromFloat (size := 32)
      ((Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s)
  let r := x87ArithD .mul ((Operand.fcw : Operand 16).read s) false x.2
      ((Operand.fpr (top) : Operand 80).read s) x.1
  x87Effect p len [(top, r.1)]
    (ftwSet ((Operand.ftw : Operand 16).read s) top (x87Tag r.1))
    (fswOrFlags ((Operand.fsw : Operand 16).read s) r.2.2) (2) (ccC1 r.2.1) s

@[simp] theorem fmulM32Effect_components (p : BitVec 64) (len : Nat) (top : BitVec 3)
    (am : AddrMode) (s : RamState) :
    (fmulM32Effect p len top am s).components =
      [.fpr (top), .ftw, .fsw, .fcc, .fpuPtr, .rip] := rfl

def fmulM32SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (top : BitVec 3)
    (am : AddrMode) (s : RamState) : Effect :=
  let x := x87FromFloat (size := 32)
      ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s)
  let r := x87ArithD .mul ((Operand.fcw : Operand 16).read s) false x.2
      ((Operand.fpr (top) : Operand 80).read s) x.1
  x87Effect p len [(top, r.1)]
    (ftwSet ((Operand.ftw : Operand 16).read s) top (x87Tag r.1))
    (fswOrFlags ((Operand.fsw : Operand 16).read s) r.2.2) (2) (ccC1 r.2.1) s

@[simp] theorem fmulM32SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (top : BitVec 3) (am : AddrMode) (s : RamState) :
    (fmulM32SegEffect p len base top am s).components =
      [.fpr (top), .ftw, .fsw, .fcc, .fpuPtr, .rip] := rfl

def fmulM32A32Effect (p : BitVec 64) (len : Nat) (top : BitVec 3) (am : AddrMode) (s : RamState) :
    Effect :=
  let x := x87FromFloat (size := 32)
      ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 32).read s)
  let r := x87ArithD .mul ((Operand.fcw : Operand 16).read s) false x.2
      ((Operand.fpr (top) : Operand 80).read s) x.1
  x87Effect p len [(top, r.1)]
    (ftwSet ((Operand.ftw : Operand 16).read s) top (x87Tag r.1))
    (fswOrFlags ((Operand.fsw : Operand 16).read s) r.2.2) (2) (ccC1 r.2.1) s

@[simp] theorem fmulM32A32Effect_components (p : BitVec 64) (len : Nat) (top : BitVec 3)
    (am : AddrMode) (s : RamState) :
    (fmulM32A32Effect p len top am s).components =
      [.fpr (top), .ftw, .fsw, .fcc, .fpuPtr, .rip] := rfl

theorem fmul_m32_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => X87LoadPre p top
        (fun t => am.addr t (p + BitVec.ofNat 64 (2 + am.tail.length))) 4 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ArithDOk .mul s.FP87_Control false
            (x87FromFloat (size := 32)
            ((Operand.mem (am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) : Operand 32).read
            s)).2 s.FP87[fprIndex (top)]
            (x87FromFloat (size := 32)
            ((Operand.mem (am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) : Operand 32).read
            s)).1)
      (codeRange p (0xD8 :: am.modrm 1 :: am.tail))
      (fmulM32Effect p (2 + am.tail.length) top am) := by
  rintro s h hcode ⟨⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, hread⟩, h0, hok⟩
  subst hp htop
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := fmul_m32_step s h hcr0 hes hm hfdp []
    (by simp) (by simp) (by rfl) (by rfl) (by rfl) am hv
        (by exact (AddrContext.legacy _ am hx hb).toSeg)
    h0
    (by exact hok)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine (fun hh => ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩) ?_
  refine x87Effect_holds_trace h _ s.RIP rfl _ (OnlyTrace.dataAccess _) _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      ?_ ?_
  · intro rv hrv
    simp only [List.mem_singleton] at hrv
    subst hrv
    exact fprSet_get_self _ _ _
  · intro r hr
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
    exact fprSet_get_of_ne _ (Ne.symm hr) _
  · x87_simp
    rfl
  · simp only [Operand.read_fsw, fswRest_x87ArithFsw]
    rfl
  · exact fswCC_x87ArithFsw _ _ _ _ _

theorem fmul_m32_triple_of_bytes [Bindings] (p : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => X87LoadPre p top
        (fun t => am.addr t (p + BitVec.ofNat 64 (2 + am.tail.length))) 4 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ArithDOk .mul s.FP87_Control false
            (x87FromFloat (size := 32)
            ((Operand.mem (am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) : Operand 32).read
            s)).2 s.FP87[fprIndex (top)]
            (x87FromFloat (size := 32)
            ((Operand.mem (am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) : Operand 32).read
            s)).1)
      (codeRange p (0xD8 :: am.modrm 1 :: am.tail))
      (Effect.post (fmulM32Effect p (2 + am.tail.length) top am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fmulM32Effect_components]; simp [Component.Covers]) _)
    (fmul_m32_effect_step p top am hv hx hb)

theorem fmul_m32_rex_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => X87LoadPre p top
        (fun t => am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length))) 4 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ArithDOk .mul s.FP87_Control false
            (x87FromFloat (size := 32)
            ((Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand 32).read
            s)).2 s.FP87[fprIndex (top)]
            (x87FromFloat (size := 32)
            ((Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand 32).read
            s)).1)
      (codeRange p (rex :: 0xD8 :: am.modrm 1 :: am.tail))
      (fmulM32Effect p (3 + am.tail.length) top am) := by
  rintro s h hcode ⟨⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, hread⟩, h0, hok⟩
  subst hp htop
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := fmul_m32_step s h hcr0 hes hm hfdp [rex]
    (by simpa using hr.scanPrefix) (by simp) (by rw [scanContext_rex _ _ hr]; rfl)
        (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) am hv
        (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    h0
    (by rw [scanContext_rex _ _ hr]; exact hok)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine (fun hh => ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩) ?_
  refine x87Effect_holds_trace h _ s.RIP rfl _ (OnlyTrace.dataAccess _) _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      ?_ ?_
  · intro rv hrv
    simp only [List.mem_singleton] at hrv
    subst hrv
    exact fprSet_get_self _ _ _
  · intro r hr
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
    exact fprSet_get_of_ne _ (Ne.symm hr) _
  · x87_simp
    rfl
  · simp only [Operand.read_fsw, fswRest_x87ArithFsw]
    rfl
  · exact fswCC_x87ArithFsw _ _ _ _ _

theorem fmul_m32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (top : BitVec 3) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => X87LoadPre p top
        (fun t => am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length))) 4 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ArithDOk .mul s.FP87_Control false
            (x87FromFloat (size := 32)
            ((Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand 32).read
            s)).2 s.FP87[fprIndex (top)]
            (x87FromFloat (size := 32)
            ((Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand 32).read
            s)).1)
      (codeRange p (rex :: 0xD8 :: am.modrm 1 :: am.tail))
      (Effect.post (fmulM32Effect p (3 + am.tail.length) top am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fmulM32Effect_components]; simp [Component.Covers]) _)
    (fmul_m32_rex_effect_step p top rex hr am hv hx hb)

theorem fmul_m32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => X87LoadPre p top
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length))) 4 s ∧ r.Ready base s
            ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ArithDOk .mul s.FP87_Control false
            (x87FromFloat (size := 32)
            ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand
            32).read s)).2 s.FP87[fprIndex (top)]
            (x87FromFloat (size := 32)
            ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand
            32).read s)).1)
      (codeRange p (r.prefixByte :: 0xD8 :: am.modrm 1 :: am.tail))
      (fmulM32SegEffect p (3 + am.tail.length) base top am) := by
  rintro s h hcode ⟨⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, hread⟩, ⟨hseg, hbase⟩, h0, hok⟩
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
  have hstep := fmul_m32_step s h hcr0 hes hm hfdp [r.prefixByte]
    (scanPrefix_seg_cons r (by simp)) (by simp) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    h0
    (by rw [hsc, segAddr_withSeg]; exact hok)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine (fun hh => ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩) ?_
  refine x87Effect_holds_trace h _ s.RIP rfl _ (OnlyTrace.dataAccess _) _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      ?_ ?_
  · intro rv hrv
    simp only [List.mem_singleton] at hrv
    subst hrv
    exact fprSet_get_self _ _ _
  · intro r hr
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
    exact fprSet_get_of_ne _ (Ne.symm hr) _
  · x87_simp
    rfl
  · simp only [Operand.read_fsw, fswRest_x87ArithFsw]
    rfl
  · exact fswCC_x87ArithFsw _ _ _ _ _

theorem fmul_m32_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => X87LoadPre p top
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (3 + am.tail.length))) 4 s ∧ r.Ready base s
            ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ArithDOk .mul s.FP87_Control false
            (x87FromFloat (size := 32)
            ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand
            32).read s)).2 s.FP87[fprIndex (top)]
            (x87FromFloat (size := 32)
            ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand
            32).read s)).1)
      (codeRange p (r.prefixByte :: 0xD8 :: am.modrm 1 :: am.tail))
      (Effect.post (fmulM32SegEffect p (3 + am.tail.length) base top am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fmulM32SegEffect_components]; simp [Component.Covers]) _)
    (fmul_m32_seg_effect_step p r base top am hv hx hb)

theorem fmul_m32_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (top : BitVec 3) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => X87LoadPre p top
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧ r.Ready base s
            ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ArithDOk .mul s.FP87_Control false
            (x87FromFloat (size := 32)
            ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand
            32).read s)).2 s.FP87[fprIndex (top)]
            (x87FromFloat (size := 32)
            ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand
            32).read s)).1)
      (codeRange p (r.prefixByte :: rex :: 0xD8 :: am.modrm 1 :: am.tail))
      (fmulM32SegEffect p (4 + am.tail.length) base top am) := by
  rintro s h hcode ⟨⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, hread⟩, ⟨hseg, hbase⟩, h0, hok⟩
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
  have hstep := fmul_m32_step s h hcr0 hes hm hfdp [r.prefixByte, rex]
    (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl) am hv
        (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    h0
    (by rw [hsc, segAddr_withSeg]; exact hok)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine (fun hh => ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩) ?_
  refine x87Effect_holds_trace h _ s.RIP rfl _ (OnlyTrace.dataAccess _) _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      ?_ ?_
  · intro rv hrv
    simp only [List.mem_singleton] at hrv
    subst hrv
    exact fprSet_get_self _ _ _
  · intro r hr
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
    exact fprSet_get_of_ne _ (Ne.symm hr) _
  · x87_simp
    rfl
  · simp only [Operand.read_fsw, fswRest_x87ArithFsw]
    rfl
  · exact fswCC_x87ArithFsw _ _ _ _ _

theorem fmul_m32_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (top : BitVec 3) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => X87LoadPre p top
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧ r.Ready base s
            ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ArithDOk .mul s.FP87_Control false
            (x87FromFloat (size := 32)
            ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand
            32).read s)).2 s.FP87[fprIndex (top)]
            (x87FromFloat (size := 32)
            ((Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand
            32).read s)).1)
      (codeRange p (r.prefixByte :: rex :: 0xD8 :: am.modrm 1 :: am.tail))
      (Effect.post (fmulM32SegEffect p (4 + am.tail.length) base top am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fmulM32SegEffect_components]; simp [Component.Covers]) _)
    (fmul_m32_rex_seg_effect_step p r base top rex hr am hv hx hb)

theorem fmul_m32_a32_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => X87LoadPre p top
        (fun t => am.addr32 t (p + BitVec.ofNat 64 (3 + am.tail.length))) 4 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ArithDOk .mul s.FP87_Control false
            (x87FromFloat (size := 32)
            ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand
            32).read s)).2 s.FP87[fprIndex (top)]
            (x87FromFloat (size := 32)
            ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand
            32).read s)).1)
      (codeRange p (0x67 :: 0xD8 :: am.modrm 1 :: am.tail))
      (fmulM32A32Effect p (3 + am.tail.length) top am) := by
  rintro s h hcode ⟨⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, hread⟩, h0, hok⟩
  subst hp htop
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := fmul_m32_a32_step s h hcr0 hes hm hfdp [0x67]
    (scanPrefix_asz_cons (by simp)) (by simp) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    h0
    (by rw [hsc]; exact hok)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine (fun hh => ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩) ?_
  refine x87Effect_holds_trace h _ s.RIP rfl _ (OnlyTrace.dataAccess _) _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      ?_ ?_
  · intro rv hrv
    simp only [List.mem_singleton] at hrv
    subst hrv
    exact fprSet_get_self _ _ _
  · intro r hr
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
    exact fprSet_get_of_ne _ (Ne.symm hr) _
  · x87_simp
    rfl
  · simp only [Operand.read_fsw, fswRest_x87ArithFsw]
    rfl
  · exact fswCC_x87ArithFsw _ _ _ _ _

theorem fmul_m32_a32_triple_of_bytes [Bindings] (p : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => X87LoadPre p top
        (fun t => am.addr32 t (p + BitVec.ofNat 64 (3 + am.tail.length))) 4 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ArithDOk .mul s.FP87_Control false
            (x87FromFloat (size := 32)
            ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand
            32).read s)).2 s.FP87[fprIndex (top)]
            (x87FromFloat (size := 32)
            ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand
            32).read s)).1)
      (codeRange p (0x67 :: 0xD8 :: am.modrm 1 :: am.tail))
      (Effect.post (fmulM32A32Effect p (3 + am.tail.length) top am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fmulM32A32Effect_components]; simp [Component.Covers]) _)
    (fmul_m32_a32_effect_step p top am hv hx hb)

theorem fmul_m32_rex_a32_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => X87LoadPre p top
        (fun t => am.addr32 t (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ArithDOk .mul s.FP87_Control false
            (x87FromFloat (size := 32)
            ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand
            32).read s)).2 s.FP87[fprIndex (top)]
            (x87FromFloat (size := 32)
            ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand
            32).read s)).1)
      (codeRange p (0x67 :: rex :: 0xD8 :: am.modrm 1 :: am.tail))
      (fmulM32A32Effect p (4 + am.tail.length) top am) := by
  rintro s h hcode ⟨⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, hread⟩, h0, hok⟩
  subst hp htop
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := fmul_m32_a32_step s h hcr0 hes hm hfdp [0x67, rex]
    (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl) am hv
        (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    h0
    (by rw [hsc]; exact hok)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine (fun hh => ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩) ?_
  refine x87Effect_holds_trace h _ s.RIP rfl _ (OnlyTrace.dataAccess _) _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      ?_ ?_
  · intro rv hrv
    simp only [List.mem_singleton] at hrv
    subst hrv
    exact fprSet_get_self _ _ _
  · intro r hr
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
    exact fprSet_get_of_ne _ (Ne.symm hr) _
  · x87_simp
    rfl
  · simp only [Operand.read_fsw, fswRest_x87ArithFsw]
    rfl
  · exact fswCC_x87ArithFsw _ _ _ _ _

theorem fmul_m32_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (top : BitVec 3) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => X87LoadPre p top
        (fun t => am.addr32 t (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ArithDOk .mul s.FP87_Control false
            (x87FromFloat (size := 32)
            ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand
            32).read s)).2 s.FP87[fprIndex (top)]
            (x87FromFloat (size := 32)
            ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand
            32).read s)).1)
      (codeRange p (0x67 :: rex :: 0xD8 :: am.modrm 1 :: am.tail))
      (Effect.post (fmulM32A32Effect p (4 + am.tail.length) top am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fmulM32A32Effect_components]; simp [Component.Covers]) _)
    (fmul_m32_rex_a32_effect_step p top rex hr am hv hx hb)

theorem fmul_m32_triple [Bindings] (p : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (fun s => X87LoadPre p top
        (fun t => am.addr t (p + BitVec.ofNat 64 (encodeFmulM32 am).length)) 4 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ArithDOk .mul s.FP87_Control false
            (x87FromFloat (size := 32)
            ((Operand.mem (am.addr s (p + BitVec.ofNat 64 (encodeFmulM32 am).length)) : Operand
            32).read s)).2 s.FP87[fprIndex (top)]
            (x87FromFloat (size := 32)
            ((Operand.mem (am.addr s (p + BitVec.ofNat 64 (encodeFmulM32 am).length)) : Operand
            32).read s)).1)
      (codeRange p (encodeFmulM32 am))
      (Effect.post (fmulM32Effect p (encodeFmulM32 am).length top am)) := by
  unfold encodeFmulM32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := fmul_m32_triple_of_bytes p top am hv hx hb
    rwa [show (0xD8 :: am.modrm 1 :: am.tail : List UInt8).length =
      2 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := fmul_m32_rex_triple_of_bytes p top _ hrex.rexPrefix am hv hx hb
    rwa [show (am.rexByte false 0 :: 0xD8 :: am.modrm 1 :: am.tail).length =
      3 + am.tail.length by simp; omega]

theorem fmul_m32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (top : BitVec 3) (am : AddrMode) (hv : am.Valid) :
    Triple
      (fun s => X87LoadPre p top
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeFmulM32 am).length))
            4 s ∧ r.Ready base s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ArithDOk .mul s.FP87_Control false
            (x87FromFloat (size := 32)
            ((Operand.mem
            (base + am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeFmulM32 am).length)) :
            Operand 32).read s)).2 s.FP87[fprIndex (top)]
            (x87FromFloat (size := 32)
            ((Operand.mem
            (base + am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeFmulM32 am).length)) :
            Operand 32).read s)).1)
      (codeRange p (r.prefixByte :: encodeFmulM32 am))
      (Effect.post (fmulM32SegEffect p (r.prefixByte :: encodeFmulM32 am).length base top am)) := by
  unfold encodeFmulM32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := fmul_m32_seg_triple_of_bytes p r base top am hv hx hb
    rwa [show (r.prefixByte :: 0xD8 :: am.modrm 1 :: am.tail : List UInt8).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := fmul_m32_rex_seg_triple_of_bytes p r base top _ hrex.rexPrefix am hv hx hb
    rwa [show (r.prefixByte :: am.rexByte false 0 :: 0xD8 :: am.modrm 1 ::
      am.tail).length = 4 + am.tail.length by simp; omega]

theorem fmul_m32_a32_triple [Bindings] (p : BitVec 64) (top : BitVec 3) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (fun s => X87LoadPre p top
        (fun t => am.addr32 t (p + BitVec.ofNat 64 (0x67 :: encodeFmulM32 am).length)) 4 s ∧
        ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧
        X87ArithDOk .mul s.FP87_Control false
            (x87FromFloat (size := 32)
            ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeFmulM32 am).length)) :
            Operand 32).read s)).2 s.FP87[fprIndex (top)]
            (x87FromFloat (size := 32)
            ((Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeFmulM32 am).length)) :
            Operand 32).read s)).1)
      (codeRange p (0x67 :: encodeFmulM32 am))
      (Effect.post (fmulM32A32Effect p (0x67 :: encodeFmulM32 am).length top am)) := by
  unfold encodeFmulM32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := fmul_m32_a32_triple_of_bytes p top am hv hx hb
    rwa [show (0x67 :: 0xD8 :: am.modrm 1 :: am.tail : List UInt8).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := fmul_m32_rex_a32_triple_of_bytes p top _ hrex.rexPrefix am hv hx hb
    rwa [show (0x67 :: am.rexByte false 0 :: 0xD8 :: am.modrm 1 ::
      am.tail).length = 4 + am.tail.length by simp; omega]

attribute [x86_compose] fmulM32Effect fmulM32SegEffect fmulM32A32Effect

@[x86_local] theorem fmulM32Effect_local {p : BitVec 64} {len : Nat} {top : BitVec 3}
    {am : AddrMode} : Effect.Local (fmulM32Effect p len top am) := by
  effect_local [fmulM32Effect, x87Effect]

@[x86_local] theorem fmulM32SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {top : BitVec 3} {am : AddrMode} : Effect.Local (fmulM32SegEffect p len base top am) := by
  effect_local [fmulM32SegEffect, x87Effect]

@[x86_local] theorem fmulM32A32Effect_local {p : BitVec 64} {len : Nat} {top : BitVec 3}
    {am : AddrMode} : Effect.Local (fmulM32A32Effect p len top am) := by
  effect_local [fmulM32A32Effect, x87Effect]

end X86Proofs
