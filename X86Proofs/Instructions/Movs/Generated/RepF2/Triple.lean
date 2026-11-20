
import X86Proofs.Instructions.Movs.Generated.RepF2.Step
import X86Proofs.Instructions.Movs.Generated.Rep.Triple
import X86Proofs.Program.Effect

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

structure RepMovsqF2Loop [Bindings] (rex : UInt8) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF2, rex, 0xA5]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 8 * count ≤ 2^32
  dstLow : (rdi.read s).toNat + 8 * count ≤ 2^32
  srcMem : ∀ i < 8 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 8 * count ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 8 * count ≤ (rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (8 * count)
  dstCode : RangeApart (rdi.read s) (8 * count) s.RIP 3

theorem RepMovsqF2Loop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepMovsqF2Loop rex s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovsqF2Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState}
    {count : Nat} (h : RepMovsqF2Loop rex s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repMovsAfter 64 3 s)) := by
  have hr := hrex.rexPrefix
  have := h.dstLow
  have := h.srcLow
  exact rep_movsq_f2_step hstride s h.ready [0xF2, rex] (by simp [scanPrefix_f2, hr.scanPrefix]) (by simp)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    h.df h.code h.codeLow (h.rcx_ne hpos)
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩

theorem RepMovsqF2Loop.rcx_after [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepMovsqF2Loop rex s (count + 1)) : rcx.read (repMovsAfter 64 3 s) = BitVec.ofNat 64 count := by
  rw [repMovsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepMovsqF2Loop.source_frame [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepMovsqF2Loop rex s count) (j : Nat) (hj : j < 8 * count) :
    (repMovsAfter 64 3 s).external[rsi.read s + BitVec.ofNat 64 j]? =
      s.external[rsi.read s + BitVec.ofNat 64 j]? := by
  rw [repMovsAfter_external]
  apply memStore_getElem?_of_ne
  intro i hi he
  have hn := congrArg BitVec.toNat he
  have := h.srcLow
  have := h.dstLow
  have := h.disjoint
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
  omega

theorem RepMovsqF2Loop.next [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepMovsqF2Loop rex s (count + 2)) : RepMovsqF2Loop rex (repMovsAfter 64 3 s) (count + 1) := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hrip : (repMovsAfter 64 3 s).RIP = s.RIP := by
    rw [repMovsAfter_rip 64 3 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : rsi.read (repMovsAfter 64 3 s) = rsi.read s + BitVec.ofNat 64 8 := repMovsAfter_rsi 64 3 s
  have hd : rdi.read (repMovsAfter 64 3 s) = rdi.read s + BitVec.ofNat 64 8 := repMovsAfter_rdi 64 3 s
  have hsn : (rsi.read (repMovsAfter 64 3 s)).toNat = (rsi.read s).toNat + 8 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repMovsAfter 64 3 s)).toNat = (rdi.read s).toNat + 8 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repMovs 64 3 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repMovsAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by omega) i (by simpa using hi) he
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, h.source_frame (8 + i) (by omega)]
    exact h.srcMem (8 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repMovsAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (8 + i) (by omega))
  · rw [hsn, hdn]; have := h.disjoint; omega
  · rw [hdn]; have := h.dstTables; omega
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, hrip]
    exact h.dstCode (8 + i) (by omega) j hj

theorem rep_movsq_f2_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (count : Nat)
    (s : RamState) (h : RepMovsqF2Loop rex s (count + 1)) :
    RepMovsqDone s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repMovsAfter 64 3 s) :=
      nextState_of_step (h.step hstride hrex (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repMovsAfter 64 3 s).Repeat_String_Operation = false := by
      rw [repMovsAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repMovs 64 3 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repMovsAfter_rip 64 3 s h.ready.msr, hc]; rfl
    · rw [repMovsAfter_rcx, hc]
    · exact repMovsAfter_rsi 64 3 s
    · exact repMovsAfter_rdi 64 3 s
    · intro i hi
      exact repMovsAfter_copy 64 3 s (by decide) i (by omega) (h.srcMem i (by omega))
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repMovs 64 3 s
  | succ m ih =>
    have hnext : nextState s = (repMovsAfter 64 3 s) :=
      nextState_of_step (h.step hstride hrex (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hs : rsi.read (repMovsAfter 64 3 s) = rsi.read s + BitVec.ofNat 64 8 := repMovsAfter_rsi 64 3 s
    have hd : rdi.read (repMovsAfter 64 3 s) = rdi.read s + BitVec.ofNat 64 8 := repMovsAfter_rdi 64 3 s
    have hfirst (i : Nat) (hi : i < 8) :
        (repMovsAfter 64 3 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[rsi.read s + BitVec.ofNat 64 i]? :=
      repMovsAfter_copy 64 3 s (by decide) i hi (h.srcMem i (by omega))
    have ih' := ih (repMovsAfter 64 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repMovsAfter 64 3 s).RIP = s.RIP := by
      rw [repMovsAfter_rip 64 3 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 8
      · refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst i hsmall)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [hd, add_ofNat_add_ofNat] at he
        have hn := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
        omega
      · have hc := ih'.copy (i - 8) (by omega)
        rw [hd, hs, add_ofNat_add_ofNat, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega),
          h.source_frame i (by omega)] at hc
        exact hc
    · refine (AgreesExcept.repMovs 64 3 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (8 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hd, add_ofNat_add_ofNat] at he
          exact ⟨8 + j, by omega, he⟩

theorem repMovsqEffect_avoids_f2 {p : BitVec 64} {s : RamState} (rex : UInt8) 
    (h : RangeApart (rdi.read s) (8 * (rcx.read s).toNat) p 3) :
    (repMovsqEffect p s).Avoids (codeRange p [0xF2, rex, 0xA5]) :=
  Effect.avoids_of_mem (by rw [repMovsqEffect_components]; simp [Component.isMem]) h rfl

theorem rep_movsq_f2_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, rex, 0xA5]) s) (hpre : RepMovsqPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, rex, 0xA5]) t ∧ (repMovsqEffect p s).Holds s t := by
  intro t
  have hr := hrex.rexPrefix
  have hcodeS : BytesAt s s.RIP [0xF2, rex, 0xA5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovsqEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovsqEffect_avoids_f2 rex hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsq_f2_step_zero s h.midRep [0xF2, rex] (by simp [scanPrefix_f2, hr.scanPrefix]) (by simp)
        (by rw [scanContext_f2_rex _ _ hr]; rfl)
        (by rw [scanContext_f2_rex _ _ hr]; exact hrex.rex_w s.DS)
        (by rw [scanContext_f2_rex _ _ hr]; rfl)
        (by rw [scanContext_f2_rex _ _ hr]; rfl)
        (by rw [scanContext_f2_rex _ _ hr]; rfl)
        hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repZeroAfter 3 s) :=
      (AgreesExcept.repZero 3 s).of_clearRep hrep (repZeroAfter_repeat 3 s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables, ?_, ?_, trivial, ?_⟩
    · rw [repZeroAfter_rip _ s h.ready.msr, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hz]
      · apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have hi' : i < 64 * (rcx.read s).toNat := hi
        omega
    · exact hag.mono (by simp)
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.dstLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hready : RepMovsqF2Loop rex s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_movsq_f2_loop hstride hrex c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, ?_, ?_, trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hd.rsiAfter, hn]
      · rw [hd.rdiAfter, hn]
      · exact hd.rcxZero
      · simp only [Operand.read]
        apply memLoad_congr
        intro i hi
        have hi' : i < 64 * (rcx.read s).toNat / 8 := hi
        exact memByte_congr (hd.copy i (by omega))
    · rw [repMovsqEffect_components, hn]
      exact hag.mono (by simp)

theorem rep_movsq_f2_triple_of_bytes [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepMovsqPre p) (codeRange p [0xF2, rex, 0xA5]) (Effect.post (repMovsqEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_movsq_f2_steps hstride p rex hrex s h hcode hpre⟩

theorem rep_movsq_f2_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) :
    Triple (RepMovsqPre p) (codeRange p [0xF2, 0x48, 0xA5]) (Effect.post (repMovsqEffect p)) :=
  rep_movsq_f2_triple_of_bytes hstride p 0x48 (by unfold RexWPrefix; decide)

structure RepMovsqF2SegLoop [Bindings] (r : SegReg) (base : BitVec 64) (rex : UInt8) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF2, rex, 0xA5]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (base + rsi.read s).toNat + 8 * count ≤ 2^32
  dstLow : (rdi.read s).toNat + 8 * count ≤ 2^32
  srcMem : ∀ i < 8 * count, (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (base + rsi.read s).toNat + 8 * count ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 8 * count ≤ (base + rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (8 * count)
  dstCode : RangeApart (rdi.read s) (8 * count) s.RIP 4
  seg : r.Ready base s

theorem RepMovsqF2SegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepMovsqF2SegLoop r base rex s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovsqF2SegLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {r : SegReg} {base : BitVec 64} {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState}
    {count : Nat} (h : RepMovsqF2SegLoop r base rex s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repMovsSegAfter base 64 4 s)) := by
  have hr := hrex.rexPrefix
  have := h.dstLow
  have := h.srcLow
  have hsrc : MemReadable s (base + rsi.read s) 8 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2, rex] =
      withSeg (repneRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF2, rex] (noSegPrefix_cons noSegPrefix_f2 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_f2_rex _ _ hr]
  have hstep := rep_movsq_f2_seg_step hstride s h.ready [r.prefixByte, 0xF2, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_f2, hr.scanPrefix])) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hrex.rex_w s.DS)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    h.df h.code h.codeLow (h.rcx_ne hpos) (by rw [hsc]; exact hsrc)
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩
  rw [hsc] at hstep
  exact hstep

theorem RepMovsqF2SegLoop.rcx_after [Bindings] {r : SegReg} {base : BitVec 64} {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepMovsqF2SegLoop r base rex s (count + 1)) : rcx.read (repMovsSegAfter base 64 4 s) = BitVec.ofNat 64 count := by
  rw [repMovsSegAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepMovsqF2SegLoop.source_frame [Bindings] {r : SegReg} {base : BitVec 64} {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepMovsqF2SegLoop r base rex s count) (j : Nat) (hj : j < 8 * count) :
    (repMovsSegAfter base 64 4 s).external[base + rsi.read s + BitVec.ofNat 64 j]? =
      s.external[base + rsi.read s + BitVec.ofNat 64 j]? := by
  rw [repMovsSegAfter_external]
  apply memStore_getElem?_of_ne
  intro i hi he
  have hn := congrArg BitVec.toNat he
  have := h.srcLow
  have := h.dstLow
  have := h.disjoint
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
  omega

theorem RepMovsqF2SegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepMovsqF2SegLoop r base rex s (count + 2)) : RepMovsqF2SegLoop r base rex (repMovsSegAfter base 64 4 s) (count + 1) := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hrip : (repMovsSegAfter base 64 4 s).RIP = s.RIP := by
    rw [repMovsSegAfter_rip base 64 4 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : base + rsi.read (repMovsSegAfter base 64 4 s) = base + rsi.read s + BitVec.ofNat 64 8 := by
    rw [repMovsSegAfter_rsi base 64 4 s, BitVec.add_assoc]
  have hd : rdi.read (repMovsSegAfter base 64 4 s) = rdi.read s + BitVec.ofNat 64 8 := repMovsSegAfter_rdi base 64 4 s
  have hsn : (base + rsi.read (repMovsSegAfter base 64 4 s)).toNat = (base + rsi.read s).toNat + 8 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repMovsSegAfter base 64 4 s)).toNat = (rdi.read s).toNat + 8 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repMovsSeg base 64 4 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_, ?_, ?_, ?_, repMovsSegAfter_segReady base 64 4 s h.seg⟩
  · intro i hi
    rw [hrip, repMovsSegAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by omega) i (by simpa using hi) he
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, h.source_frame (8 + i) (by omega)]
    exact h.srcMem (8 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repMovsSegAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (8 + i) (by omega))
  · rw [hsn, hdn]; have := h.disjoint; omega
  · rw [hdn]; have := h.dstTables; omega
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, hrip]
    exact h.dstCode (8 + i) (by omega) j hj

theorem rep_movsq_f2_seg_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {r : SegReg} {base : BitVec 64} {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (count : Nat)
    (s : RamState) (h : RepMovsqF2SegLoop r base rex s (count + 1)) :
    RepMovsqSegDone base s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repMovsSegAfter base 64 4 s) :=
      nextState_of_step (h.step hstride hrex (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repMovsSegAfter base 64 4 s).Repeat_String_Operation = false := by
      rw [repMovsSegAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repMovsSeg base 64 4 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repMovsSegAfter_rip base 64 4 s h.ready.msr, hc]; rfl
    · rw [repMovsSegAfter_rcx, hc]
    · exact repMovsSegAfter_rsi base 64 4 s
    · exact repMovsSegAfter_rdi base 64 4 s
    · intro i hi
      exact repMovsSegAfter_copy base 64 4 s (by decide) i (by omega) (h.srcMem i (by omega))
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repMovsSeg base 64 4 s
  | succ m ih =>
    have hnext : nextState s = (repMovsSegAfter base 64 4 s) :=
      nextState_of_step (h.step hstride hrex (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hsreg : rsi.read (repMovsSegAfter base 64 4 s) = rsi.read s + BitVec.ofNat 64 8 :=
      repMovsSegAfter_rsi base 64 4 s
    have hs : base + rsi.read (repMovsSegAfter base 64 4 s) = base + rsi.read s + BitVec.ofNat 64 8 := by
      rw [hsreg, BitVec.add_assoc]
    have hd : rdi.read (repMovsSegAfter base 64 4 s) = rdi.read s + BitVec.ofNat 64 8 := repMovsSegAfter_rdi base 64 4 s
    have hfirst (i : Nat) (hi : i < 8) :
        (repMovsSegAfter base 64 4 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[base + rsi.read s + BitVec.ofNat 64 i]? :=
      repMovsSegAfter_copy base 64 4 s (by decide) i hi (h.srcMem i (by omega))
    have ih' := ih (repMovsSegAfter base 64 4 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repMovsSegAfter base 64 4 s).RIP = s.RIP := by
      rw [repMovsSegAfter_rip base 64 4 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hsreg, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 8
      · refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst i hsmall)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [hd, add_ofNat_add_ofNat] at he
        have hn := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
        omega
      · have hc := ih'.copy (i - 8) (by omega)
        rw [hd, hs, add_ofNat_add_ofNat, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega),
          h.source_frame i (by omega)] at hc
        exact hc
    · refine (AgreesExcept.repMovsSeg base 64 4 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (8 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hd, add_ofNat_add_ofNat] at he
          exact ⟨8 + j, by omega, he⟩

theorem repMovsqSegEffect_avoids_f2 {p base : BitVec 64} {r : SegReg} {s : RamState} (rex : UInt8) 
    (h : RangeApart (rdi.read s) (8 * (rcx.read s).toNat) p 4) :
    (repMovsqSegEffect p base s).Avoids (codeRange p [r.prefixByte, 0xF2, rex, 0xA5]) :=
  Effect.avoids_of_mem (by rw [repMovsqSegEffect_components]; simp [Component.isMem]) h rfl

theorem rep_movsq_f2_seg_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF2, rex, 0xA5]) s) (hpre : RepMovsqSegPre p r base s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF2, rex, 0xA5]) t ∧ (repMovsqSegEffect p base s).Holds s t := by
  intro t
  have hr := hrex.rexPrefix
  have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF2, rex, 0xA5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovsqSegEffect p base s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovsqSegEffect_avoids_f2 (base := base) (r := r) rex hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2, rex] =
      withSeg (repneRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF2, rex] (noSegPrefix_cons noSegPrefix_f2 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_f2_rex _ _ hr]
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 4 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsq_f2_step_zero s h.midRep [r.prefixByte, 0xF2, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_f2, hr.scanPrefix])) (by simp)
        (by rw [hsc]; rfl)
        (by rw [hsc]; exact hrex.rex_w s.DS)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repZeroAfter 4 s) :=
      (AgreesExcept.repZero 4 s).of_clearRep hrep (repZeroAfter_repeat 4 s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables, ?_, ?_, trivial, ?_⟩
    · rw [repZeroAfter_rip _ s h.ready.msr, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hz]
      · apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have hi' : i < 64 * (rcx.read s).toNat := hi
        omega
    · exact hag.mono (by simp)
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.dstLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hready : RepMovsqF2SegLoop r base rex s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode,
        hpre.seg⟩
    have hd := rep_movsq_f2_seg_loop hstride hrex c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, ?_, ?_, trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hd.rsiAfter, hn]
      · rw [hd.rdiAfter, hn]
      · exact hd.rcxZero
      · simp only [Operand.read]
        apply memLoad_congr
        intro i hi
        have hi' : i < 64 * (rcx.read s).toNat / 8 := hi
        exact memByte_congr (hd.copy i (by omega))
    · rw [repMovsqSegEffect_components, hn]
      exact hag.mono (by simp)

theorem rep_movsq_f2_seg_triple_of_bytes [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepMovsqSegPre p r base) (codeRange p [r.prefixByte, 0xF2, rex, 0xA5]) (Effect.post (repMovsqSegEffect p base)) :=
  fun s h hcode hpre => ⟨_, rep_movsq_f2_seg_steps hstride p r base rex hrex s h hcode hpre⟩

theorem rep_movsq_f2_seg_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (RepMovsqSegPre p r base) (codeRange p [r.prefixByte, 0xF2, 0x48, 0xA5]) (Effect.post (repMovsqSegEffect p base)) :=
  rep_movsq_f2_seg_triple_of_bytes hstride p r base 0x48 (by unfold RexWPrefix; decide)

structure RepMovsdF2Loop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF2, 0xA5]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 4 * count ≤ 2^32
  dstLow : (rdi.read s).toNat + 4 * count ≤ 2^32
  srcMem : ∀ i < 4 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 4 * count ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 4 * count ≤ (rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (4 * count)
  dstCode : RangeApart (rdi.read s) (4 * count) s.RIP 2

theorem RepMovsdF2Loop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsdF2Loop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovsdF2Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {count : Nat} (h : RepMovsdF2Loop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repMovsAfter 32 2 s)) := by
  have := h.dstLow
  have := h.srcLow
  exact rep_movsd_f2_step hstride s h.ready [0xF2] (by simpa using scanPrefix_f2) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne hpos)
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩

theorem RepMovsdF2Loop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsdF2Loop s (count + 1)) : rcx.read (repMovsAfter 32 2 s) = BitVec.ofNat 64 count := by
  rw [repMovsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepMovsdF2Loop.source_frame [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsdF2Loop s count) (j : Nat) (hj : j < 4 * count) :
    (repMovsAfter 32 2 s).external[rsi.read s + BitVec.ofNat 64 j]? =
      s.external[rsi.read s + BitVec.ofNat 64 j]? := by
  rw [repMovsAfter_external]
  apply memStore_getElem?_of_ne
  intro i hi he
  have hn := congrArg BitVec.toNat he
  have := h.srcLow
  have := h.dstLow
  have := h.disjoint
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
  omega

theorem RepMovsdF2Loop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsdF2Loop s (count + 2)) : RepMovsdF2Loop (repMovsAfter 32 2 s) (count + 1) := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hrip : (repMovsAfter 32 2 s).RIP = s.RIP := by
    rw [repMovsAfter_rip 32 2 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : rsi.read (repMovsAfter 32 2 s) = rsi.read s + BitVec.ofNat 64 4 := repMovsAfter_rsi 32 2 s
  have hd : rdi.read (repMovsAfter 32 2 s) = rdi.read s + BitVec.ofNat 64 4 := repMovsAfter_rdi 32 2 s
  have hsn : (rsi.read (repMovsAfter 32 2 s)).toNat = (rsi.read s).toNat + 4 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repMovsAfter 32 2 s)).toNat = (rdi.read s).toNat + 4 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repMovs 32 2 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repMovsAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by omega) i (by simpa using hi) he
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, h.source_frame (4 + i) (by omega)]
    exact h.srcMem (4 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repMovsAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (4 + i) (by omega))
  · rw [hsn, hdn]; have := h.disjoint; omega
  · rw [hdn]; have := h.dstTables; omega
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, hrip]
    exact h.dstCode (4 + i) (by omega) j hj

theorem rep_movsd_f2_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (h : RepMovsdF2Loop s (count + 1)) :
    RepMovsdDone s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repMovsAfter 32 2 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repMovsAfter 32 2 s).Repeat_String_Operation = false := by
      rw [repMovsAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repMovs 32 2 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repMovsAfter_rip 32 2 s h.ready.msr, hc]; rfl
    · rw [repMovsAfter_rcx, hc]
    · exact repMovsAfter_rsi 32 2 s
    · exact repMovsAfter_rdi 32 2 s
    · intro i hi
      exact repMovsAfter_copy 32 2 s (by decide) i (by omega) (h.srcMem i (by omega))
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repMovs 32 2 s
  | succ m ih =>
    have hnext : nextState s = (repMovsAfter 32 2 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hs : rsi.read (repMovsAfter 32 2 s) = rsi.read s + BitVec.ofNat 64 4 := repMovsAfter_rsi 32 2 s
    have hd : rdi.read (repMovsAfter 32 2 s) = rdi.read s + BitVec.ofNat 64 4 := repMovsAfter_rdi 32 2 s
    have hfirst (i : Nat) (hi : i < 4) :
        (repMovsAfter 32 2 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[rsi.read s + BitVec.ofNat 64 i]? :=
      repMovsAfter_copy 32 2 s (by decide) i hi (h.srcMem i (by omega))
    have ih' := ih (repMovsAfter 32 2 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repMovsAfter 32 2 s).RIP = s.RIP := by
      rw [repMovsAfter_rip 32 2 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 4
      · refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst i hsmall)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [hd, add_ofNat_add_ofNat] at he
        have hn := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
        omega
      · have hc := ih'.copy (i - 4) (by omega)
        rw [hd, hs, add_ofNat_add_ofNat, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega),
          h.source_frame i (by omega)] at hc
        exact hc
    · refine (AgreesExcept.repMovs 32 2 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (4 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hd, add_ofNat_add_ofNat] at he
          exact ⟨4 + j, by omega, he⟩

theorem repMovsdEffect_avoids_f2 {p : BitVec 64} {s : RamState} 
    (h : RangeApart (rdi.read s) (4 * (rcx.read s).toNat) p 2) :
    (repMovsdEffect p s).Avoids (codeRange p [0xF2, 0xA5]) :=
  Effect.avoids_of_mem (by rw [repMovsdEffect_components]; simp [Component.isMem]) h rfl

theorem rep_movsd_f2_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, 0xA5]) s) (hpre : RepMovsdPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, 0xA5]) t ∧ (repMovsdEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF2, 0xA5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovsdEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovsdEffect_avoids_f2 hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 2 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsd_f2_step_zero s h.midRep [0xF2] (by simpa using scanPrefix_f2) (by simp)
        rfl
        rfl
        rfl
        rfl
        rfl
        rfl
        hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repZeroAfter 2 s) :=
      (AgreesExcept.repZero 2 s).of_clearRep hrep (repZeroAfter_repeat 2 s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables, ?_, ?_, trivial, ?_⟩
    · rw [repZeroAfter_rip _ s h.ready.msr, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hz]
      · apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have hi' : i < 32 * (rcx.read s).toNat := hi
        omega
    · exact hag.mono (by simp)
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.dstLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hready : RepMovsdF2Loop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_movsd_f2_loop hstride c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, ?_, ?_, trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hd.rsiAfter, hn]
      · rw [hd.rdiAfter, hn]
      · exact hd.rcxZero
      · simp only [Operand.read]
        apply memLoad_congr
        intro i hi
        have hi' : i < 32 * (rcx.read s).toNat / 8 := hi
        exact memByte_congr (hd.copy i (by omega))
    · rw [repMovsdEffect_components, hn]
      exact hag.mono (by simp)

theorem rep_movsd_f2_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepMovsdPre p) (codeRange p [0xF2, 0xA5]) (Effect.post (repMovsdEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_movsd_f2_steps hstride p s h hcode hpre⟩

structure RepMovsdF2SegLoop [Bindings] (r : SegReg) (base : BitVec 64) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF2, 0xA5]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (base + rsi.read s).toNat + 4 * count ≤ 2^32
  dstLow : (rdi.read s).toNat + 4 * count ≤ 2^32
  srcMem : ∀ i < 4 * count, (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (base + rsi.read s).toNat + 4 * count ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 4 * count ≤ (base + rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (4 * count)
  dstCode : RangeApart (rdi.read s) (4 * count) s.RIP 3
  seg : r.Ready base s

theorem RepMovsdF2SegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovsdF2SegLoop r base s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovsdF2SegLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {r : SegReg} {base : BitVec 64} {s : RamState}
    {count : Nat} (h : RepMovsdF2SegLoop r base s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repMovsSegAfter base 32 3 s)) := by
  have := h.dstLow
  have := h.srcLow
  have hsrc : MemReadable s (base + rsi.read s) 4 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF2]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF2] (noSegPrefix_cons noSegPrefix_f2 noSegPrefix_nil)]
  have hstep := rep_movsd_f2_seg_step hstride s h.ready [r.prefixByte, 0xF2] (scanPrefix_seg_cons r (by simpa using scanPrefix_f2)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    h.df h.code h.codeLow (h.rcx_ne hpos) (by rw [hsc]; exact hsrc)
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩
  rw [hsc] at hstep
  exact hstep

theorem RepMovsdF2SegLoop.rcx_after [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovsdF2SegLoop r base s (count + 1)) : rcx.read (repMovsSegAfter base 32 3 s) = BitVec.ofNat 64 count := by
  rw [repMovsSegAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepMovsdF2SegLoop.source_frame [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovsdF2SegLoop r base s count) (j : Nat) (hj : j < 4 * count) :
    (repMovsSegAfter base 32 3 s).external[base + rsi.read s + BitVec.ofNat 64 j]? =
      s.external[base + rsi.read s + BitVec.ofNat 64 j]? := by
  rw [repMovsSegAfter_external]
  apply memStore_getElem?_of_ne
  intro i hi he
  have hn := congrArg BitVec.toNat he
  have := h.srcLow
  have := h.dstLow
  have := h.disjoint
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
  omega

theorem RepMovsdF2SegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovsdF2SegLoop r base s (count + 2)) : RepMovsdF2SegLoop r base (repMovsSegAfter base 32 3 s) (count + 1) := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hrip : (repMovsSegAfter base 32 3 s).RIP = s.RIP := by
    rw [repMovsSegAfter_rip base 32 3 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : base + rsi.read (repMovsSegAfter base 32 3 s) = base + rsi.read s + BitVec.ofNat 64 4 := by
    rw [repMovsSegAfter_rsi base 32 3 s, BitVec.add_assoc]
  have hd : rdi.read (repMovsSegAfter base 32 3 s) = rdi.read s + BitVec.ofNat 64 4 := repMovsSegAfter_rdi base 32 3 s
  have hsn : (base + rsi.read (repMovsSegAfter base 32 3 s)).toNat = (base + rsi.read s).toNat + 4 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repMovsSegAfter base 32 3 s)).toNat = (rdi.read s).toNat + 4 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repMovsSeg base 32 3 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_, ?_, ?_, ?_, repMovsSegAfter_segReady base 32 3 s h.seg⟩
  · intro i hi
    rw [hrip, repMovsSegAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by omega) i (by simpa using hi) he
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, h.source_frame (4 + i) (by omega)]
    exact h.srcMem (4 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repMovsSegAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (4 + i) (by omega))
  · rw [hsn, hdn]; have := h.disjoint; omega
  · rw [hdn]; have := h.dstTables; omega
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, hrip]
    exact h.dstCode (4 + i) (by omega) j hj

theorem rep_movsd_f2_seg_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {r : SegReg} {base : BitVec 64} (count : Nat)
    (s : RamState) (h : RepMovsdF2SegLoop r base s (count + 1)) :
    RepMovsdSegDone base s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repMovsSegAfter base 32 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repMovsSegAfter base 32 3 s).Repeat_String_Operation = false := by
      rw [repMovsSegAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repMovsSeg base 32 3 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repMovsSegAfter_rip base 32 3 s h.ready.msr, hc]; rfl
    · rw [repMovsSegAfter_rcx, hc]
    · exact repMovsSegAfter_rsi base 32 3 s
    · exact repMovsSegAfter_rdi base 32 3 s
    · intro i hi
      exact repMovsSegAfter_copy base 32 3 s (by decide) i (by omega) (h.srcMem i (by omega))
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repMovsSeg base 32 3 s
  | succ m ih =>
    have hnext : nextState s = (repMovsSegAfter base 32 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hsreg : rsi.read (repMovsSegAfter base 32 3 s) = rsi.read s + BitVec.ofNat 64 4 :=
      repMovsSegAfter_rsi base 32 3 s
    have hs : base + rsi.read (repMovsSegAfter base 32 3 s) = base + rsi.read s + BitVec.ofNat 64 4 := by
      rw [hsreg, BitVec.add_assoc]
    have hd : rdi.read (repMovsSegAfter base 32 3 s) = rdi.read s + BitVec.ofNat 64 4 := repMovsSegAfter_rdi base 32 3 s
    have hfirst (i : Nat) (hi : i < 4) :
        (repMovsSegAfter base 32 3 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[base + rsi.read s + BitVec.ofNat 64 i]? :=
      repMovsSegAfter_copy base 32 3 s (by decide) i hi (h.srcMem i (by omega))
    have ih' := ih (repMovsSegAfter base 32 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repMovsSegAfter base 32 3 s).RIP = s.RIP := by
      rw [repMovsSegAfter_rip base 32 3 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hsreg, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 4
      · refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst i hsmall)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [hd, add_ofNat_add_ofNat] at he
        have hn := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
        omega
      · have hc := ih'.copy (i - 4) (by omega)
        rw [hd, hs, add_ofNat_add_ofNat, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega),
          h.source_frame i (by omega)] at hc
        exact hc
    · refine (AgreesExcept.repMovsSeg base 32 3 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (4 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hd, add_ofNat_add_ofNat] at he
          exact ⟨4 + j, by omega, he⟩

theorem repMovsdSegEffect_avoids_f2 {p base : BitVec 64} {r : SegReg} {s : RamState} 
    (h : RangeApart (rdi.read s) (4 * (rcx.read s).toNat) p 3) :
    (repMovsdSegEffect p base s).Avoids (codeRange p [r.prefixByte, 0xF2, 0xA5]) :=
  Effect.avoids_of_mem (by rw [repMovsdSegEffect_components]; simp [Component.isMem]) h rfl

theorem rep_movsd_f2_seg_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF2, 0xA5]) s) (hpre : RepMovsdSegPre p r base s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF2, 0xA5]) t ∧ (repMovsdSegEffect p base s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF2, 0xA5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovsdSegEffect p base s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovsdSegEffect_avoids_f2 (base := base) (r := r) hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF2]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF2] (noSegPrefix_cons noSegPrefix_f2 noSegPrefix_nil)]
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsd_f2_step_zero s h.midRep [r.prefixByte, 0xF2] (scanPrefix_seg_cons r (by simpa using scanPrefix_f2)) (by simp)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repZeroAfter 3 s) :=
      (AgreesExcept.repZero 3 s).of_clearRep hrep (repZeroAfter_repeat 3 s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables, ?_, ?_, trivial, ?_⟩
    · rw [repZeroAfter_rip _ s h.ready.msr, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hz]
      · apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have hi' : i < 32 * (rcx.read s).toNat := hi
        omega
    · exact hag.mono (by simp)
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.dstLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hready : RepMovsdF2SegLoop r base s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode,
        hpre.seg⟩
    have hd := rep_movsd_f2_seg_loop hstride c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, ?_, ?_, trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hd.rsiAfter, hn]
      · rw [hd.rdiAfter, hn]
      · exact hd.rcxZero
      · simp only [Operand.read]
        apply memLoad_congr
        intro i hi
        have hi' : i < 32 * (rcx.read s).toNat / 8 := hi
        exact memByte_congr (hd.copy i (by omega))
    · rw [repMovsdSegEffect_components, hn]
      exact hag.mono (by simp)

theorem rep_movsd_f2_seg_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (RepMovsdSegPre p r base) (codeRange p [r.prefixByte, 0xF2, 0xA5]) (Effect.post (repMovsdSegEffect p base)) :=
  fun s h hcode hpre => ⟨_, rep_movsd_f2_seg_steps hstride p r base s h hcode hpre⟩

structure RepMovswF2Loop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF2, 0x66, 0xA5]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 2 * count ≤ 2^32
  dstLow : (rdi.read s).toNat + 2 * count ≤ 2^32
  srcMem : ∀ i < 2 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 2 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 2 * count ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 2 * count ≤ (rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (2 * count)
  dstCode : RangeApart (rdi.read s) (2 * count) s.RIP 3

theorem RepMovswF2Loop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepMovswF2Loop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovswF2Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {count : Nat} (h : RepMovswF2Loop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repMovsAfter 16 3 s)) := by
  have := h.dstLow
  have := h.srcLow
  exact rep_movsw_f2_step hstride s h.ready [0xF2, 0x66] (by simp [scanPrefix_f2, scanPrefix_66]) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne hpos)
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩

theorem RepMovswF2Loop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepMovswF2Loop s (count + 1)) : rcx.read (repMovsAfter 16 3 s) = BitVec.ofNat 64 count := by
  rw [repMovsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepMovswF2Loop.source_frame [Bindings] {s : RamState} {count : Nat}
    (h : RepMovswF2Loop s count) (j : Nat) (hj : j < 2 * count) :
    (repMovsAfter 16 3 s).external[rsi.read s + BitVec.ofNat 64 j]? =
      s.external[rsi.read s + BitVec.ofNat 64 j]? := by
  rw [repMovsAfter_external]
  apply memStore_getElem?_of_ne
  intro i hi he
  have hn := congrArg BitVec.toNat he
  have := h.srcLow
  have := h.dstLow
  have := h.disjoint
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
  omega

theorem RepMovswF2Loop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepMovswF2Loop s (count + 2)) : RepMovswF2Loop (repMovsAfter 16 3 s) (count + 1) := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hrip : (repMovsAfter 16 3 s).RIP = s.RIP := by
    rw [repMovsAfter_rip 16 3 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : rsi.read (repMovsAfter 16 3 s) = rsi.read s + BitVec.ofNat 64 2 := repMovsAfter_rsi 16 3 s
  have hd : rdi.read (repMovsAfter 16 3 s) = rdi.read s + BitVec.ofNat 64 2 := repMovsAfter_rdi 16 3 s
  have hsn : (rsi.read (repMovsAfter 16 3 s)).toNat = (rsi.read s).toNat + 2 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repMovsAfter 16 3 s)).toNat = (rdi.read s).toNat + 2 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repMovs 16 3 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repMovsAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by omega) i (by simpa using hi) he
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, h.source_frame (2 + i) (by omega)]
    exact h.srcMem (2 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repMovsAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (2 + i) (by omega))
  · rw [hsn, hdn]; have := h.disjoint; omega
  · rw [hdn]; have := h.dstTables; omega
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, hrip]
    exact h.dstCode (2 + i) (by omega) j hj

theorem rep_movsw_f2_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (h : RepMovswF2Loop s (count + 1)) :
    RepMovswDone s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repMovsAfter 16 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repMovsAfter 16 3 s).Repeat_String_Operation = false := by
      rw [repMovsAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repMovs 16 3 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repMovsAfter_rip 16 3 s h.ready.msr, hc]; rfl
    · rw [repMovsAfter_rcx, hc]
    · exact repMovsAfter_rsi 16 3 s
    · exact repMovsAfter_rdi 16 3 s
    · intro i hi
      exact repMovsAfter_copy 16 3 s (by decide) i (by omega) (h.srcMem i (by omega))
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repMovs 16 3 s
  | succ m ih =>
    have hnext : nextState s = (repMovsAfter 16 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hs : rsi.read (repMovsAfter 16 3 s) = rsi.read s + BitVec.ofNat 64 2 := repMovsAfter_rsi 16 3 s
    have hd : rdi.read (repMovsAfter 16 3 s) = rdi.read s + BitVec.ofNat 64 2 := repMovsAfter_rdi 16 3 s
    have hfirst (i : Nat) (hi : i < 2) :
        (repMovsAfter 16 3 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[rsi.read s + BitVec.ofNat 64 i]? :=
      repMovsAfter_copy 16 3 s (by decide) i hi (h.srcMem i (by omega))
    have ih' := ih (repMovsAfter 16 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repMovsAfter 16 3 s).RIP = s.RIP := by
      rw [repMovsAfter_rip 16 3 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 2
      · refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst i hsmall)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [hd, add_ofNat_add_ofNat] at he
        have hn := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
        omega
      · have hc := ih'.copy (i - 2) (by omega)
        rw [hd, hs, add_ofNat_add_ofNat, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega),
          h.source_frame i (by omega)] at hc
        exact hc
    · refine (AgreesExcept.repMovs 16 3 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (2 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hd, add_ofNat_add_ofNat] at he
          exact ⟨2 + j, by omega, he⟩

theorem repMovswEffect_avoids_f2 {p : BitVec 64} {s : RamState} 
    (h : RangeApart (rdi.read s) (2 * (rcx.read s).toNat) p 3) :
    (repMovswEffect p s).Avoids (codeRange p [0xF2, 0x66, 0xA5]) :=
  Effect.avoids_of_mem (by rw [repMovswEffect_components]; simp [Component.isMem]) h rfl

theorem rep_movsw_f2_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, 0x66, 0xA5]) s) (hpre : RepMovswPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, 0x66, 0xA5]) t ∧ (repMovswEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF2, 0x66, 0xA5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovswEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovswEffect_avoids_f2 hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsw_f2_step_zero s h.midRep [0xF2, 0x66] (by simp [scanPrefix_f2, scanPrefix_66]) (by simp)
        rfl
        rfl
        rfl
        rfl
        rfl
        rfl
        hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repZeroAfter 3 s) :=
      (AgreesExcept.repZero 3 s).of_clearRep hrep (repZeroAfter_repeat 3 s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables, ?_, ?_, trivial, ?_⟩
    · rw [repZeroAfter_rip _ s h.ready.msr, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hz]
      · apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have hi' : i < 16 * (rcx.read s).toNat := hi
        omega
    · exact hag.mono (by simp)
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.dstLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hready : RepMovswF2Loop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_movsw_f2_loop hstride c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, ?_, ?_, trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hd.rsiAfter, hn]
      · rw [hd.rdiAfter, hn]
      · exact hd.rcxZero
      · simp only [Operand.read]
        apply memLoad_congr
        intro i hi
        have hi' : i < 16 * (rcx.read s).toNat / 8 := hi
        exact memByte_congr (hd.copy i (by omega))
    · rw [repMovswEffect_components, hn]
      exact hag.mono (by simp)

theorem rep_movsw_f2_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepMovswPre p) (codeRange p [0xF2, 0x66, 0xA5]) (Effect.post (repMovswEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_movsw_f2_steps hstride p s h hcode hpre⟩

structure RepMovswF2SegLoop [Bindings] (r : SegReg) (base : BitVec 64) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF2, 0x66, 0xA5]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (base + rsi.read s).toNat + 2 * count ≤ 2^32
  dstLow : (rdi.read s).toNat + 2 * count ≤ 2^32
  srcMem : ∀ i < 2 * count, (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 2 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (base + rsi.read s).toNat + 2 * count ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 2 * count ≤ (base + rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (2 * count)
  dstCode : RangeApart (rdi.read s) (2 * count) s.RIP 4
  seg : r.Ready base s

theorem RepMovswF2SegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovswF2SegLoop r base s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovswF2SegLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {r : SegReg} {base : BitVec 64} {s : RamState}
    {count : Nat} (h : RepMovswF2SegLoop r base s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repMovsSegAfter base 16 4 s)) := by
  have := h.dstLow
  have := h.srcLow
  have hsrc : MemReadable s (base + rsi.read s) 2 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF2, 0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF2, 0x66] (noSegPrefix_cons noSegPrefix_f2 (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil))]
  have hstep := rep_movsw_f2_seg_step hstride s h.ready [r.prefixByte, 0xF2, 0x66] (scanPrefix_seg_cons r (by simp [scanPrefix_f2, scanPrefix_66])) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    h.df h.code h.codeLow (h.rcx_ne hpos) (by rw [hsc]; exact hsrc)
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩
  rw [hsc] at hstep
  exact hstep

theorem RepMovswF2SegLoop.rcx_after [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovswF2SegLoop r base s (count + 1)) : rcx.read (repMovsSegAfter base 16 4 s) = BitVec.ofNat 64 count := by
  rw [repMovsSegAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepMovswF2SegLoop.source_frame [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovswF2SegLoop r base s count) (j : Nat) (hj : j < 2 * count) :
    (repMovsSegAfter base 16 4 s).external[base + rsi.read s + BitVec.ofNat 64 j]? =
      s.external[base + rsi.read s + BitVec.ofNat 64 j]? := by
  rw [repMovsSegAfter_external]
  apply memStore_getElem?_of_ne
  intro i hi he
  have hn := congrArg BitVec.toNat he
  have := h.srcLow
  have := h.dstLow
  have := h.disjoint
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
  omega

theorem RepMovswF2SegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovswF2SegLoop r base s (count + 2)) : RepMovswF2SegLoop r base (repMovsSegAfter base 16 4 s) (count + 1) := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hrip : (repMovsSegAfter base 16 4 s).RIP = s.RIP := by
    rw [repMovsSegAfter_rip base 16 4 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : base + rsi.read (repMovsSegAfter base 16 4 s) = base + rsi.read s + BitVec.ofNat 64 2 := by
    rw [repMovsSegAfter_rsi base 16 4 s, BitVec.add_assoc]
  have hd : rdi.read (repMovsSegAfter base 16 4 s) = rdi.read s + BitVec.ofNat 64 2 := repMovsSegAfter_rdi base 16 4 s
  have hsn : (base + rsi.read (repMovsSegAfter base 16 4 s)).toNat = (base + rsi.read s).toNat + 2 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repMovsSegAfter base 16 4 s)).toNat = (rdi.read s).toNat + 2 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repMovsSeg base 16 4 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_, ?_, ?_, ?_, repMovsSegAfter_segReady base 16 4 s h.seg⟩
  · intro i hi
    rw [hrip, repMovsSegAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by omega) i (by simpa using hi) he
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, h.source_frame (2 + i) (by omega)]
    exact h.srcMem (2 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repMovsSegAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (2 + i) (by omega))
  · rw [hsn, hdn]; have := h.disjoint; omega
  · rw [hdn]; have := h.dstTables; omega
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, hrip]
    exact h.dstCode (2 + i) (by omega) j hj

theorem rep_movsw_f2_seg_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {r : SegReg} {base : BitVec 64} (count : Nat)
    (s : RamState) (h : RepMovswF2SegLoop r base s (count + 1)) :
    RepMovswSegDone base s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repMovsSegAfter base 16 4 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repMovsSegAfter base 16 4 s).Repeat_String_Operation = false := by
      rw [repMovsSegAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repMovsSeg base 16 4 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repMovsSegAfter_rip base 16 4 s h.ready.msr, hc]; rfl
    · rw [repMovsSegAfter_rcx, hc]
    · exact repMovsSegAfter_rsi base 16 4 s
    · exact repMovsSegAfter_rdi base 16 4 s
    · intro i hi
      exact repMovsSegAfter_copy base 16 4 s (by decide) i (by omega) (h.srcMem i (by omega))
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repMovsSeg base 16 4 s
  | succ m ih =>
    have hnext : nextState s = (repMovsSegAfter base 16 4 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hsreg : rsi.read (repMovsSegAfter base 16 4 s) = rsi.read s + BitVec.ofNat 64 2 :=
      repMovsSegAfter_rsi base 16 4 s
    have hs : base + rsi.read (repMovsSegAfter base 16 4 s) = base + rsi.read s + BitVec.ofNat 64 2 := by
      rw [hsreg, BitVec.add_assoc]
    have hd : rdi.read (repMovsSegAfter base 16 4 s) = rdi.read s + BitVec.ofNat 64 2 := repMovsSegAfter_rdi base 16 4 s
    have hfirst (i : Nat) (hi : i < 2) :
        (repMovsSegAfter base 16 4 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[base + rsi.read s + BitVec.ofNat 64 i]? :=
      repMovsSegAfter_copy base 16 4 s (by decide) i hi (h.srcMem i (by omega))
    have ih' := ih (repMovsSegAfter base 16 4 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repMovsSegAfter base 16 4 s).RIP = s.RIP := by
      rw [repMovsSegAfter_rip base 16 4 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hsreg, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 2
      · refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst i hsmall)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [hd, add_ofNat_add_ofNat] at he
        have hn := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
        omega
      · have hc := ih'.copy (i - 2) (by omega)
        rw [hd, hs, add_ofNat_add_ofNat, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega),
          h.source_frame i (by omega)] at hc
        exact hc
    · refine (AgreesExcept.repMovsSeg base 16 4 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (2 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hd, add_ofNat_add_ofNat] at he
          exact ⟨2 + j, by omega, he⟩

theorem repMovswSegEffect_avoids_f2 {p base : BitVec 64} {r : SegReg} {s : RamState} 
    (h : RangeApart (rdi.read s) (2 * (rcx.read s).toNat) p 4) :
    (repMovswSegEffect p base s).Avoids (codeRange p [r.prefixByte, 0xF2, 0x66, 0xA5]) :=
  Effect.avoids_of_mem (by rw [repMovswSegEffect_components]; simp [Component.isMem]) h rfl

theorem rep_movsw_f2_seg_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF2, 0x66, 0xA5]) s) (hpre : RepMovswSegPre p r base s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF2, 0x66, 0xA5]) t ∧ (repMovswSegEffect p base s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF2, 0x66, 0xA5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovswSegEffect p base s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovswSegEffect_avoids_f2 (base := base) (r := r) hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF2, 0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF2, 0x66] (noSegPrefix_cons noSegPrefix_f2 (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil))]
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 4 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsw_f2_step_zero s h.midRep [r.prefixByte, 0xF2, 0x66] (scanPrefix_seg_cons r (by simp [scanPrefix_f2, scanPrefix_66])) (by simp)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repZeroAfter 4 s) :=
      (AgreesExcept.repZero 4 s).of_clearRep hrep (repZeroAfter_repeat 4 s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables, ?_, ?_, trivial, ?_⟩
    · rw [repZeroAfter_rip _ s h.ready.msr, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hz]
      · apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have hi' : i < 16 * (rcx.read s).toNat := hi
        omega
    · exact hag.mono (by simp)
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.dstLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hready : RepMovswF2SegLoop r base s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode,
        hpre.seg⟩
    have hd := rep_movsw_f2_seg_loop hstride c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, ?_, ?_, trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hd.rsiAfter, hn]
      · rw [hd.rdiAfter, hn]
      · exact hd.rcxZero
      · simp only [Operand.read]
        apply memLoad_congr
        intro i hi
        have hi' : i < 16 * (rcx.read s).toNat / 8 := hi
        exact memByte_congr (hd.copy i (by omega))
    · rw [repMovswSegEffect_components, hn]
      exact hag.mono (by simp)

theorem rep_movsw_f2_seg_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (RepMovswSegPre p r base) (codeRange p [r.prefixByte, 0xF2, 0x66, 0xA5]) (Effect.post (repMovswSegEffect p base)) :=
  fun s h hcode hpre => ⟨_, rep_movsw_f2_seg_steps hstride p r base s h hcode hpre⟩

structure RepMovsbF2Loop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF2, 0xA4]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 1 * count ≤ 2^32
  dstLow : (rdi.read s).toNat + 1 * count ≤ 2^32
  srcMem : ∀ i < 1 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 1 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 1 * count ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 1 * count ≤ (rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (1 * count)
  dstCode : RangeApart (rdi.read s) (1 * count) s.RIP 2

theorem RepMovsbF2Loop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsbF2Loop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovsbF2Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {count : Nat} (h : RepMovsbF2Loop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repMovsAfter 8 2 s)) := by
  have := h.dstLow
  have := h.srcLow
  exact rep_movsb_f2_step hstride s h.ready [0xF2] (by simpa using scanPrefix_f2) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne hpos)
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩

theorem RepMovsbF2Loop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsbF2Loop s (count + 1)) : rcx.read (repMovsAfter 8 2 s) = BitVec.ofNat 64 count := by
  rw [repMovsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepMovsbF2Loop.source_frame [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsbF2Loop s count) (j : Nat) (hj : j < 1 * count) :
    (repMovsAfter 8 2 s).external[rsi.read s + BitVec.ofNat 64 j]? =
      s.external[rsi.read s + BitVec.ofNat 64 j]? := by
  rw [repMovsAfter_external]
  apply memStore_getElem?_of_ne
  intro i hi he
  have hn := congrArg BitVec.toNat he
  have := h.srcLow
  have := h.dstLow
  have := h.disjoint
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
  omega

theorem RepMovsbF2Loop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsbF2Loop s (count + 2)) : RepMovsbF2Loop (repMovsAfter 8 2 s) (count + 1) := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hrip : (repMovsAfter 8 2 s).RIP = s.RIP := by
    rw [repMovsAfter_rip 8 2 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : rsi.read (repMovsAfter 8 2 s) = rsi.read s + BitVec.ofNat 64 1 := repMovsAfter_rsi 8 2 s
  have hd : rdi.read (repMovsAfter 8 2 s) = rdi.read s + BitVec.ofNat 64 1 := repMovsAfter_rdi 8 2 s
  have hsn : (rsi.read (repMovsAfter 8 2 s)).toNat = (rsi.read s).toNat + 1 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repMovsAfter 8 2 s)).toNat = (rdi.read s).toNat + 1 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repMovs 8 2 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repMovsAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by omega) i (by simpa using hi) he
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, h.source_frame (1 + i) (by omega)]
    exact h.srcMem (1 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repMovsAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (1 + i) (by omega))
  · rw [hsn, hdn]; have := h.disjoint; omega
  · rw [hdn]; have := h.dstTables; omega
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, hrip]
    exact h.dstCode (1 + i) (by omega) j hj

theorem rep_movsb_f2_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (h : RepMovsbF2Loop s (count + 1)) :
    RepMovsbDone s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repMovsAfter 8 2 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repMovsAfter 8 2 s).Repeat_String_Operation = false := by
      rw [repMovsAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repMovs 8 2 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repMovsAfter_rip 8 2 s h.ready.msr, hc]; rfl
    · rw [repMovsAfter_rcx, hc]
    · exact repMovsAfter_rsi 8 2 s
    · exact repMovsAfter_rdi 8 2 s
    · intro i hi
      exact repMovsAfter_copy 8 2 s (by decide) i (by omega) (h.srcMem i (by omega))
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repMovs 8 2 s
  | succ m ih =>
    have hnext : nextState s = (repMovsAfter 8 2 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hs : rsi.read (repMovsAfter 8 2 s) = rsi.read s + BitVec.ofNat 64 1 := repMovsAfter_rsi 8 2 s
    have hd : rdi.read (repMovsAfter 8 2 s) = rdi.read s + BitVec.ofNat 64 1 := repMovsAfter_rdi 8 2 s
    have hfirst (i : Nat) (hi : i < 1) :
        (repMovsAfter 8 2 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[rsi.read s + BitVec.ofNat 64 i]? :=
      repMovsAfter_copy 8 2 s (by decide) i hi (h.srcMem i (by omega))
    have ih' := ih (repMovsAfter 8 2 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repMovsAfter 8 2 s).RIP = s.RIP := by
      rw [repMovsAfter_rip 8 2 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 1
      · refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst i hsmall)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [hd, add_ofNat_add_ofNat] at he
        have hn := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
        omega
      · have hc := ih'.copy (i - 1) (by omega)
        rw [hd, hs, add_ofNat_add_ofNat, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega),
          h.source_frame i (by omega)] at hc
        exact hc
    · refine (AgreesExcept.repMovs 8 2 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (1 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hd, add_ofNat_add_ofNat] at he
          exact ⟨1 + j, by omega, he⟩

theorem repMovsbEffect_avoids_f2 {p : BitVec 64} {s : RamState} 
    (h : RangeApart (rdi.read s) (1 * (rcx.read s).toNat) p 2) :
    (repMovsbEffect p s).Avoids (codeRange p [0xF2, 0xA4]) :=
  Effect.avoids_of_mem (by rw [repMovsbEffect_components]; simp [Component.isMem]) h rfl

theorem rep_movsb_f2_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, 0xA4]) s) (hpre : RepMovsbPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, 0xA4]) t ∧ (repMovsbEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF2, 0xA4] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovsbEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovsbEffect_avoids_f2 hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 2 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsb_f2_step_zero s h.midRep [0xF2] (by simpa using scanPrefix_f2) (by simp)
        rfl
        rfl
        rfl
        rfl
        hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repZeroAfter 2 s) :=
      (AgreesExcept.repZero 2 s).of_clearRep hrep (repZeroAfter_repeat 2 s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables, ?_, ?_, trivial, ?_⟩
    · rw [repZeroAfter_rip _ s h.ready.msr, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hz]
      · apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have hi' : i < 8 * (rcx.read s).toNat := hi
        omega
    · exact hag.mono (by simp)
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.dstLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hready : RepMovsbF2Loop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_movsb_f2_loop hstride c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, ?_, ?_, trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hd.rsiAfter, hn]
      · rw [hd.rdiAfter, hn]
      · exact hd.rcxZero
      · simp only [Operand.read]
        apply memLoad_congr
        intro i hi
        have hi' : i < 8 * (rcx.read s).toNat / 8 := hi
        exact memByte_congr (hd.copy i (by omega))
    · rw [repMovsbEffect_components, hn]
      exact hag.mono (by simp)

theorem rep_movsb_f2_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepMovsbPre p) (codeRange p [0xF2, 0xA4]) (Effect.post (repMovsbEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_movsb_f2_steps hstride p s h hcode hpre⟩

structure RepMovsbF2SegLoop [Bindings] (r : SegReg) (base : BitVec 64) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF2, 0xA4]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (base + rsi.read s).toNat + 1 * count ≤ 2^32
  dstLow : (rdi.read s).toNat + 1 * count ≤ 2^32
  srcMem : ∀ i < 1 * count, (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 1 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (base + rsi.read s).toNat + 1 * count ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 1 * count ≤ (base + rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (1 * count)
  dstCode : RangeApart (rdi.read s) (1 * count) s.RIP 3
  seg : r.Ready base s

theorem RepMovsbF2SegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovsbF2SegLoop r base s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovsbF2SegLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {r : SegReg} {base : BitVec 64} {s : RamState}
    {count : Nat} (h : RepMovsbF2SegLoop r base s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repMovsSegAfter base 8 3 s)) := by
  have := h.dstLow
  have := h.srcLow
  have hsrc : MemReadable s (base + rsi.read s) 1 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF2]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF2] (noSegPrefix_cons noSegPrefix_f2 noSegPrefix_nil)]
  have hstep := rep_movsb_f2_seg_step hstride s h.ready [r.prefixByte, 0xF2] (scanPrefix_seg_cons r (by simpa using scanPrefix_f2)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    h.df h.code h.codeLow (h.rcx_ne hpos) (by rw [hsc]; exact hsrc)
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩
  rw [hsc] at hstep
  exact hstep

theorem RepMovsbF2SegLoop.rcx_after [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovsbF2SegLoop r base s (count + 1)) : rcx.read (repMovsSegAfter base 8 3 s) = BitVec.ofNat 64 count := by
  rw [repMovsSegAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepMovsbF2SegLoop.source_frame [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovsbF2SegLoop r base s count) (j : Nat) (hj : j < 1 * count) :
    (repMovsSegAfter base 8 3 s).external[base + rsi.read s + BitVec.ofNat 64 j]? =
      s.external[base + rsi.read s + BitVec.ofNat 64 j]? := by
  rw [repMovsSegAfter_external]
  apply memStore_getElem?_of_ne
  intro i hi he
  have hn := congrArg BitVec.toNat he
  have := h.srcLow
  have := h.dstLow
  have := h.disjoint
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
  omega

theorem RepMovsbF2SegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovsbF2SegLoop r base s (count + 2)) : RepMovsbF2SegLoop r base (repMovsSegAfter base 8 3 s) (count + 1) := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hrip : (repMovsSegAfter base 8 3 s).RIP = s.RIP := by
    rw [repMovsSegAfter_rip base 8 3 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : base + rsi.read (repMovsSegAfter base 8 3 s) = base + rsi.read s + BitVec.ofNat 64 1 := by
    rw [repMovsSegAfter_rsi base 8 3 s, BitVec.add_assoc]
  have hd : rdi.read (repMovsSegAfter base 8 3 s) = rdi.read s + BitVec.ofNat 64 1 := repMovsSegAfter_rdi base 8 3 s
  have hsn : (base + rsi.read (repMovsSegAfter base 8 3 s)).toNat = (base + rsi.read s).toNat + 1 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repMovsSegAfter base 8 3 s)).toNat = (rdi.read s).toNat + 1 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repMovsSeg base 8 3 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_, ?_, ?_, ?_, repMovsSegAfter_segReady base 8 3 s h.seg⟩
  · intro i hi
    rw [hrip, repMovsSegAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by omega) i (by simpa using hi) he
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, h.source_frame (1 + i) (by omega)]
    exact h.srcMem (1 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repMovsSegAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (1 + i) (by omega))
  · rw [hsn, hdn]; have := h.disjoint; omega
  · rw [hdn]; have := h.dstTables; omega
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, hrip]
    exact h.dstCode (1 + i) (by omega) j hj

theorem rep_movsb_f2_seg_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {r : SegReg} {base : BitVec 64} (count : Nat)
    (s : RamState) (h : RepMovsbF2SegLoop r base s (count + 1)) :
    RepMovsbSegDone base s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repMovsSegAfter base 8 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repMovsSegAfter base 8 3 s).Repeat_String_Operation = false := by
      rw [repMovsSegAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repMovsSeg base 8 3 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repMovsSegAfter_rip base 8 3 s h.ready.msr, hc]; rfl
    · rw [repMovsSegAfter_rcx, hc]
    · exact repMovsSegAfter_rsi base 8 3 s
    · exact repMovsSegAfter_rdi base 8 3 s
    · intro i hi
      exact repMovsSegAfter_copy base 8 3 s (by decide) i (by omega) (h.srcMem i (by omega))
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repMovsSeg base 8 3 s
  | succ m ih =>
    have hnext : nextState s = (repMovsSegAfter base 8 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hsreg : rsi.read (repMovsSegAfter base 8 3 s) = rsi.read s + BitVec.ofNat 64 1 :=
      repMovsSegAfter_rsi base 8 3 s
    have hs : base + rsi.read (repMovsSegAfter base 8 3 s) = base + rsi.read s + BitVec.ofNat 64 1 := by
      rw [hsreg, BitVec.add_assoc]
    have hd : rdi.read (repMovsSegAfter base 8 3 s) = rdi.read s + BitVec.ofNat 64 1 := repMovsSegAfter_rdi base 8 3 s
    have hfirst (i : Nat) (hi : i < 1) :
        (repMovsSegAfter base 8 3 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[base + rsi.read s + BitVec.ofNat 64 i]? :=
      repMovsSegAfter_copy base 8 3 s (by decide) i hi (h.srcMem i (by omega))
    have ih' := ih (repMovsSegAfter base 8 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repMovsSegAfter base 8 3 s).RIP = s.RIP := by
      rw [repMovsSegAfter_rip base 8 3 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hsreg, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 1
      · refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst i hsmall)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [hd, add_ofNat_add_ofNat] at he
        have hn := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
        omega
      · have hc := ih'.copy (i - 1) (by omega)
        rw [hd, hs, add_ofNat_add_ofNat, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega),
          h.source_frame i (by omega)] at hc
        exact hc
    · refine (AgreesExcept.repMovsSeg base 8 3 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (1 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hd, add_ofNat_add_ofNat] at he
          exact ⟨1 + j, by omega, he⟩

theorem repMovsbSegEffect_avoids_f2 {p base : BitVec 64} {r : SegReg} {s : RamState} 
    (h : RangeApart (rdi.read s) (1 * (rcx.read s).toNat) p 3) :
    (repMovsbSegEffect p base s).Avoids (codeRange p [r.prefixByte, 0xF2, 0xA4]) :=
  Effect.avoids_of_mem (by rw [repMovsbSegEffect_components]; simp [Component.isMem]) h rfl

theorem rep_movsb_f2_seg_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF2, 0xA4]) s) (hpre : RepMovsbSegPre p r base s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF2, 0xA4]) t ∧ (repMovsbSegEffect p base s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF2, 0xA4] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovsbSegEffect p base s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovsbSegEffect_avoids_f2 (base := base) (r := r) hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF2]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF2] (noSegPrefix_cons noSegPrefix_f2 noSegPrefix_nil)]
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsb_f2_step_zero s h.midRep [r.prefixByte, 0xF2] (scanPrefix_seg_cons r (by simpa using scanPrefix_f2)) (by simp)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repZeroAfter 3 s) :=
      (AgreesExcept.repZero 3 s).of_clearRep hrep (repZeroAfter_repeat 3 s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables, ?_, ?_, trivial, ?_⟩
    · rw [repZeroAfter_rip _ s h.ready.msr, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hz]
      · apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have hi' : i < 8 * (rcx.read s).toNat := hi
        omega
    · exact hag.mono (by simp)
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.dstLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hready : RepMovsbF2SegLoop r base s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode,
        hpre.seg⟩
    have hd := rep_movsb_f2_seg_loop hstride c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, ?_, ?_, trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hd.rsiAfter, hn]
      · rw [hd.rdiAfter, hn]
      · exact hd.rcxZero
      · simp only [Operand.read]
        apply memLoad_congr
        intro i hi
        have hi' : i < 8 * (rcx.read s).toNat / 8 := hi
        exact memByte_congr (hd.copy i (by omega))
    · rw [repMovsbSegEffect_components, hn]
      exact hag.mono (by simp)

theorem rep_movsb_f2_seg_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (RepMovsbSegPre p r base) (codeRange p [r.prefixByte, 0xF2, 0xA4]) (Effect.post (repMovsbSegEffect p base)) :=
  fun s h hcode hpre => ⟨_, rep_movsb_f2_seg_steps hstride p r base s h hcode hpre⟩

end X86Proofs
