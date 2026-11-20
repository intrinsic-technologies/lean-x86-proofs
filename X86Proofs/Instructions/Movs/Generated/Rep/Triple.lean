
import X86Proofs.Instructions.Movs.Generated.Rep.Step
import X86Proofs.Instructions.Movs.RepTriple
import X86Proofs.Program.Effect

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

structure RepMovsqDone [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (8 * count)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (8 * count)
  copy : ∀ i < 8 * count,
    t.external[rdi.read s + BitVec.ofNat 64 i]? = s.external[rsi.read s + BitVec.ofNat 64 i]?
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) (8 * count), .rip] (clearRep s) t

structure RepMovsqSegLoop [Bindings] (r : SegReg) (base : BitVec 64) (rex : UInt8) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF3, rex, 0xA5]
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

theorem RepMovsqSegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepMovsqSegLoop r base rex s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovsqSegLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {r : SegReg} {base : BitVec 64} {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState}
    {count : Nat} (h : RepMovsqSegLoop r base rex s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repMovsSegAfter base 64 4 s)) := by
  have hr := hrex.rexPrefix
  have := h.dstLow
  have := h.srcLow
  have hsrc : MemReadable s (base + rsi.read s) 8 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3, rex] =
      withSeg (repRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3, rex] (noSegPrefix_cons noSegPrefix_f3 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_f3_rex _ _ hr]
  have hstep := rep_movsq_seg_step hstride s h.ready [r.prefixByte, 0xF3, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp)
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

theorem RepMovsqSegLoop.rcx_after [Bindings] {r : SegReg} {base : BitVec 64} {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepMovsqSegLoop r base rex s (count + 1)) : rcx.read (repMovsSegAfter base 64 4 s) = BitVec.ofNat 64 count := by
  rw [repMovsSegAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepMovsqSegLoop.source_frame [Bindings] {r : SegReg} {base : BitVec 64} {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepMovsqSegLoop r base rex s count) (j : Nat) (hj : j < 8 * count) :
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

theorem RepMovsqSegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepMovsqSegLoop r base rex s (count + 2)) : RepMovsqSegLoop r base rex (repMovsSegAfter base 64 4 s) (count + 1) := by
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

structure RepMovsqSegDone [Bindings] (base : BitVec 64) (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 4)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (8 * count)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (8 * count)
  copy : ∀ i < 8 * count,
    t.external[rdi.read s + BitVec.ofNat 64 i]? = s.external[base + rsi.read s + BitVec.ofNat 64 i]?
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) (8 * count), .rip] (clearRep s) t

theorem rep_movsq_seg_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {r : SegReg} {base : BitVec 64} {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (count : Nat)
    (s : RamState) (h : RepMovsqSegLoop r base rex s (count + 1)) :
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

structure RepMovsqSegPre (p : BitVec 64) (r : SegReg) (base : BitVec 64) (s : RamState) :
    Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (base + rsi.read s).toNat + 8 * (rcx.read s).toNat ≤ 2^32
  dstLow : (rdi.read s).toNat + 8 * (rcx.read s).toNat ≤ 2^32
  srcMem : ∀ i < 8 * (rcx.read s).toNat, (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (base + rsi.read s).toNat + 8 * (rcx.read s).toNat ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 8 * (rcx.read s).toNat ≤ (base + rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (8 * (rcx.read s).toNat)
  dstCode : RangeApart (rdi.read s) (8 * (rcx.read s).toNat) p 4
  seg : r.Ready base s

def repMovsqSegEffect (p base : BitVec 64) (s : RamState) : Effect where
  rip := p + 4
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (8 * (rcx.read s).toNat)⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (8 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (rdi.read s) : Operand (64 * (rcx.read s).toNat)),
      (Operand.mem (base + rsi.read s) : Operand (64 * (rcx.read s).toNat)).read s⟩]

@[simp] theorem repMovsqSegEffect_components (p base : BitVec 64) (s : RamState) :
    (repMovsqSegEffect p base s).components =
      [.reg 6, .reg 7, .reg 1, .mem (rdi.read s) (8 * (rcx.read s).toNat), .rip] := by
  simp only [repMovsqSegEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 64 * (rcx.read s).toNat / 8 = 8 * (rcx.read s).toNat by omega]

theorem repMovsqSegEffect_avoids {p base : BitVec 64} {r : SegReg} {s : RamState} (rex : UInt8) 
    (h : RangeApart (rdi.read s) (8 * (rcx.read s).toNat) p 4) :
    (repMovsqSegEffect p base s).Avoids (codeRange p [r.prefixByte, 0xF3, rex, 0xA5]) :=
  Effect.avoids_of_mem (by rw [repMovsqSegEffect_components]; simp [Component.isMem]) h rfl

theorem rep_movsq_seg_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF3, rex, 0xA5]) s) (hpre : RepMovsqSegPre p r base s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF3, rex, 0xA5]) t ∧ (repMovsqSegEffect p base s).Holds s t := by
  intro t
  have hr := hrex.rexPrefix
  have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF3, rex, 0xA5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovsqSegEffect p base s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovsqSegEffect_avoids (base := base) (r := r) rex hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3, rex] =
      withSeg (repRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3, rex] (noSegPrefix_cons noSegPrefix_f3 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_f3_rex _ _ hr]
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 4 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsq_scan_step_zero s h.midRep [r.prefixByte, 0xF3, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp)
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
    have hready : RepMovsqSegLoop r base rex s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode,
        hpre.seg⟩
    have hd := rep_movsq_seg_loop hstride hrex c' s hready
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

theorem rep_movsq_seg_triple_of_bytes [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepMovsqSegPre p r base) (codeRange p [r.prefixByte, 0xF3, rex, 0xA5]) (Effect.post (repMovsqSegEffect p base)) :=
  fun s h hcode hpre => ⟨_, rep_movsq_seg_steps hstride p r base rex hrex s h hcode hpre⟩

theorem rep_movsq_seg_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (RepMovsqSegPre p r base) (codeRange p [r.prefixByte, 0xF3, 0x48, 0xA5]) (Effect.post (repMovsqSegEffect p base)) :=
  rep_movsq_seg_triple_of_bytes hstride p r base 0x48 (by unfold RexWPrefix; decide)

theorem repMovsqSegEffect_bytes {p base : BitVec 64} {s s' : RamState} (h : (repMovsqSegEffect p base s).Holds s s')
    (i : Nat) (hi : i < 8 * (rcx.read s).toNat) :
    memByte s'.external (rdi.read s + BitVec.ofNat 64 i) =
      memByte s.external (base + rsi.read s + BitVec.ofNat 64 i) :=
  memByte_of_memLoad_eq (n := 64 * (rcx.read s).toNat) h.writes.2.2.2 i (by omega)

structure RepMovsdLoop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0xA5]
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

theorem RepMovsdLoop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsdLoop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovsdLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {count : Nat} (h : RepMovsdLoop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repMovsAfter 32 2 s)) := by
  have := h.dstLow
  have := h.srcLow
  exact rep_movsd_step hstride s h.ready [0xF3] (by simpa using scanPrefix_f3) (by simp)
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

theorem RepMovsdLoop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsdLoop s (count + 1)) : rcx.read (repMovsAfter 32 2 s) = BitVec.ofNat 64 count := by
  rw [repMovsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepMovsdLoop.source_frame [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsdLoop s count) (j : Nat) (hj : j < 4 * count) :
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

theorem RepMovsdLoop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsdLoop s (count + 2)) : RepMovsdLoop (repMovsAfter 32 2 s) (count + 1) := by
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

structure RepMovsdDone [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (4 * count)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (4 * count)
  copy : ∀ i < 4 * count,
    t.external[rdi.read s + BitVec.ofNat 64 i]? = s.external[rsi.read s + BitVec.ofNat 64 i]?
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) (4 * count), .rip] (clearRep s) t

theorem rep_movsd_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (h : RepMovsdLoop s (count + 1)) :
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

structure RepMovsdPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (rsi.read s).toNat + 4 * (rcx.read s).toNat ≤ 2^32
  dstLow : (rdi.read s).toNat + 4 * (rcx.read s).toNat ≤ 2^32
  srcMem : ∀ i < 4 * (rcx.read s).toNat, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 4 * (rcx.read s).toNat ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 4 * (rcx.read s).toNat ≤ (rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (4 * (rcx.read s).toNat)
  dstCode : RangeApart (rdi.read s) (4 * (rcx.read s).toNat) p 2

def repMovsdEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (4 * (rcx.read s).toNat)⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (4 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (rdi.read s) : Operand (32 * (rcx.read s).toNat)),
      (Operand.mem (rsi.read s) : Operand (32 * (rcx.read s).toNat)).read s⟩]

@[simp] theorem repMovsdEffect_components (p : BitVec 64) (s : RamState) :
    (repMovsdEffect p s).components =
      [.reg 6, .reg 7, .reg 1, .mem (rdi.read s) (4 * (rcx.read s).toNat), .rip] := by
  simp only [repMovsdEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 32 * (rcx.read s).toNat / 8 = 4 * (rcx.read s).toNat by omega]

theorem repMovsdEffect_avoids {p : BitVec 64} {s : RamState} 
    (h : RangeApart (rdi.read s) (4 * (rcx.read s).toNat) p 2) :
    (repMovsdEffect p s).Avoids (codeRange p [0xF3, 0xA5]) :=
  Effect.avoids_of_mem (by rw [repMovsdEffect_components]; simp [Component.isMem]) h rfl

theorem rep_movsd_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0xA5]) s) (hpre : RepMovsdPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0xA5]) t ∧ (repMovsdEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF3, 0xA5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovsdEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovsdEffect_avoids hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 2 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsd_step_zero s h.midRep [0xF3] (by simpa using scanPrefix_f3) (by simp)
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
    have hready : RepMovsdLoop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_movsd_loop hstride c' s hready
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

theorem rep_movsd_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepMovsdPre p) (codeRange p [0xF3, 0xA5]) (Effect.post (repMovsdEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_movsd_steps hstride p s h hcode hpre⟩

theorem repMovsdEffect_bytes {p : BitVec 64} {s s' : RamState} (h : (repMovsdEffect p s).Holds s s')
    (i : Nat) (hi : i < 4 * (rcx.read s).toNat) :
    memByte s'.external (rdi.read s + BitVec.ofNat 64 i) =
      memByte s.external (rsi.read s + BitVec.ofNat 64 i) :=
  memByte_of_memLoad_eq (n := 32 * (rcx.read s).toNat) h.writes.2.2.2 i (by omega)

structure RepMovsdSegLoop [Bindings] (r : SegReg) (base : BitVec 64) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF3, 0xA5]
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

theorem RepMovsdSegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovsdSegLoop r base s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovsdSegLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {r : SegReg} {base : BitVec 64} {s : RamState}
    {count : Nat} (h : RepMovsdSegLoop r base s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repMovsSegAfter base 32 3 s)) := by
  have := h.dstLow
  have := h.srcLow
  have hsrc : MemReadable s (base + rsi.read s) 4 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3] (noSegPrefix_cons noSegPrefix_f3 noSegPrefix_nil)]
  have hstep := rep_movsd_seg_step hstride s h.ready [r.prefixByte, 0xF3] (scanPrefix_seg_cons r (by simpa using scanPrefix_f3)) (by simp)
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

theorem RepMovsdSegLoop.rcx_after [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovsdSegLoop r base s (count + 1)) : rcx.read (repMovsSegAfter base 32 3 s) = BitVec.ofNat 64 count := by
  rw [repMovsSegAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepMovsdSegLoop.source_frame [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovsdSegLoop r base s count) (j : Nat) (hj : j < 4 * count) :
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

theorem RepMovsdSegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovsdSegLoop r base s (count + 2)) : RepMovsdSegLoop r base (repMovsSegAfter base 32 3 s) (count + 1) := by
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

structure RepMovsdSegDone [Bindings] (base : BitVec 64) (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (4 * count)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (4 * count)
  copy : ∀ i < 4 * count,
    t.external[rdi.read s + BitVec.ofNat 64 i]? = s.external[base + rsi.read s + BitVec.ofNat 64 i]?
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) (4 * count), .rip] (clearRep s) t

theorem rep_movsd_seg_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {r : SegReg} {base : BitVec 64} (count : Nat)
    (s : RamState) (h : RepMovsdSegLoop r base s (count + 1)) :
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

structure RepMovsdSegPre (p : BitVec 64) (r : SegReg) (base : BitVec 64) (s : RamState) :
    Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (base + rsi.read s).toNat + 4 * (rcx.read s).toNat ≤ 2^32
  dstLow : (rdi.read s).toNat + 4 * (rcx.read s).toNat ≤ 2^32
  srcMem : ∀ i < 4 * (rcx.read s).toNat, (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (base + rsi.read s).toNat + 4 * (rcx.read s).toNat ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 4 * (rcx.read s).toNat ≤ (base + rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (4 * (rcx.read s).toNat)
  dstCode : RangeApart (rdi.read s) (4 * (rcx.read s).toNat) p 3
  seg : r.Ready base s

def repMovsdSegEffect (p base : BitVec 64) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (4 * (rcx.read s).toNat)⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (4 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (rdi.read s) : Operand (32 * (rcx.read s).toNat)),
      (Operand.mem (base + rsi.read s) : Operand (32 * (rcx.read s).toNat)).read s⟩]

@[simp] theorem repMovsdSegEffect_components (p base : BitVec 64) (s : RamState) :
    (repMovsdSegEffect p base s).components =
      [.reg 6, .reg 7, .reg 1, .mem (rdi.read s) (4 * (rcx.read s).toNat), .rip] := by
  simp only [repMovsdSegEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 32 * (rcx.read s).toNat / 8 = 4 * (rcx.read s).toNat by omega]

theorem repMovsdSegEffect_avoids {p base : BitVec 64} {r : SegReg} {s : RamState} 
    (h : RangeApart (rdi.read s) (4 * (rcx.read s).toNat) p 3) :
    (repMovsdSegEffect p base s).Avoids (codeRange p [r.prefixByte, 0xF3, 0xA5]) :=
  Effect.avoids_of_mem (by rw [repMovsdSegEffect_components]; simp [Component.isMem]) h rfl

theorem rep_movsd_seg_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF3, 0xA5]) s) (hpre : RepMovsdSegPre p r base s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF3, 0xA5]) t ∧ (repMovsdSegEffect p base s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF3, 0xA5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovsdSegEffect p base s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovsdSegEffect_avoids (base := base) (r := r) hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3] (noSegPrefix_cons noSegPrefix_f3 noSegPrefix_nil)]
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsd_step_zero s h.midRep [r.prefixByte, 0xF3] (scanPrefix_seg_cons r (by simpa using scanPrefix_f3)) (by simp)
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
    have hready : RepMovsdSegLoop r base s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode,
        hpre.seg⟩
    have hd := rep_movsd_seg_loop hstride c' s hready
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

theorem rep_movsd_seg_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (RepMovsdSegPre p r base) (codeRange p [r.prefixByte, 0xF3, 0xA5]) (Effect.post (repMovsdSegEffect p base)) :=
  fun s h hcode hpre => ⟨_, rep_movsd_seg_steps hstride p r base s h hcode hpre⟩

theorem repMovsdSegEffect_bytes {p base : BitVec 64} {s s' : RamState} (h : (repMovsdSegEffect p base s).Holds s s')
    (i : Nat) (hi : i < 4 * (rcx.read s).toNat) :
    memByte s'.external (rdi.read s + BitVec.ofNat 64 i) =
      memByte s.external (base + rsi.read s + BitVec.ofNat 64 i) :=
  memByte_of_memLoad_eq (n := 32 * (rcx.read s).toNat) h.writes.2.2.2 i (by omega)

structure RepMovswLoop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0x66, 0xA5]
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

theorem RepMovswLoop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepMovswLoop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovswLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {count : Nat} (h : RepMovswLoop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repMovsAfter 16 3 s)) := by
  have := h.dstLow
  have := h.srcLow
  exact rep_movsw_step hstride s h.ready [0xF3, 0x66] (by simp [scanPrefix_f3, scanPrefix_66]) (by simp)
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

theorem RepMovswLoop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepMovswLoop s (count + 1)) : rcx.read (repMovsAfter 16 3 s) = BitVec.ofNat 64 count := by
  rw [repMovsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepMovswLoop.source_frame [Bindings] {s : RamState} {count : Nat}
    (h : RepMovswLoop s count) (j : Nat) (hj : j < 2 * count) :
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

theorem RepMovswLoop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepMovswLoop s (count + 2)) : RepMovswLoop (repMovsAfter 16 3 s) (count + 1) := by
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

structure RepMovswDone [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (2 * count)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (2 * count)
  copy : ∀ i < 2 * count,
    t.external[rdi.read s + BitVec.ofNat 64 i]? = s.external[rsi.read s + BitVec.ofNat 64 i]?
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) (2 * count), .rip] (clearRep s) t

theorem rep_movsw_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (h : RepMovswLoop s (count + 1)) :
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

structure RepMovswPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (rsi.read s).toNat + 2 * (rcx.read s).toNat ≤ 2^32
  dstLow : (rdi.read s).toNat + 2 * (rcx.read s).toNat ≤ 2^32
  srcMem : ∀ i < 2 * (rcx.read s).toNat, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 2 * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 2 * (rcx.read s).toNat ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 2 * (rcx.read s).toNat ≤ (rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (2 * (rcx.read s).toNat)
  dstCode : RangeApart (rdi.read s) (2 * (rcx.read s).toNat) p 3

def repMovswEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (2 * (rcx.read s).toNat)⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (2 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (rdi.read s) : Operand (16 * (rcx.read s).toNat)),
      (Operand.mem (rsi.read s) : Operand (16 * (rcx.read s).toNat)).read s⟩]

@[simp] theorem repMovswEffect_components (p : BitVec 64) (s : RamState) :
    (repMovswEffect p s).components =
      [.reg 6, .reg 7, .reg 1, .mem (rdi.read s) (2 * (rcx.read s).toNat), .rip] := by
  simp only [repMovswEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 16 * (rcx.read s).toNat / 8 = 2 * (rcx.read s).toNat by omega]

theorem repMovswEffect_avoids {p : BitVec 64} {s : RamState} 
    (h : RangeApart (rdi.read s) (2 * (rcx.read s).toNat) p 3) :
    (repMovswEffect p s).Avoids (codeRange p [0xF3, 0x66, 0xA5]) :=
  Effect.avoids_of_mem (by rw [repMovswEffect_components]; simp [Component.isMem]) h rfl

theorem rep_movsw_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0x66, 0xA5]) s) (hpre : RepMovswPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0x66, 0xA5]) t ∧ (repMovswEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF3, 0x66, 0xA5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovswEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovswEffect_avoids hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsw_step_zero s h.midRep [0xF3, 0x66] (by simp [scanPrefix_f3, scanPrefix_66]) (by simp)
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
    have hready : RepMovswLoop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_movsw_loop hstride c' s hready
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

theorem rep_movsw_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepMovswPre p) (codeRange p [0xF3, 0x66, 0xA5]) (Effect.post (repMovswEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_movsw_steps hstride p s h hcode hpre⟩

theorem repMovswEffect_bytes {p : BitVec 64} {s s' : RamState} (h : (repMovswEffect p s).Holds s s')
    (i : Nat) (hi : i < 2 * (rcx.read s).toNat) :
    memByte s'.external (rdi.read s + BitVec.ofNat 64 i) =
      memByte s.external (rsi.read s + BitVec.ofNat 64 i) :=
  memByte_of_memLoad_eq (n := 16 * (rcx.read s).toNat) h.writes.2.2.2 i (by omega)

structure RepMovswSegLoop [Bindings] (r : SegReg) (base : BitVec 64) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF3, 0x66, 0xA5]
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

theorem RepMovswSegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovswSegLoop r base s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovswSegLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {r : SegReg} {base : BitVec 64} {s : RamState}
    {count : Nat} (h : RepMovswSegLoop r base s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repMovsSegAfter base 16 4 s)) := by
  have := h.dstLow
  have := h.srcLow
  have hsrc : MemReadable s (base + rsi.read s) 2 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3, 0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3, 0x66] (noSegPrefix_cons noSegPrefix_f3 (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil))]
  have hstep := rep_movsw_seg_step hstride s h.ready [r.prefixByte, 0xF3, 0x66] (scanPrefix_seg_cons r (by simp [scanPrefix_f3, scanPrefix_66])) (by simp)
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

theorem RepMovswSegLoop.rcx_after [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovswSegLoop r base s (count + 1)) : rcx.read (repMovsSegAfter base 16 4 s) = BitVec.ofNat 64 count := by
  rw [repMovsSegAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepMovswSegLoop.source_frame [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovswSegLoop r base s count) (j : Nat) (hj : j < 2 * count) :
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

theorem RepMovswSegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovswSegLoop r base s (count + 2)) : RepMovswSegLoop r base (repMovsSegAfter base 16 4 s) (count + 1) := by
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

structure RepMovswSegDone [Bindings] (base : BitVec 64) (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 4)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (2 * count)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (2 * count)
  copy : ∀ i < 2 * count,
    t.external[rdi.read s + BitVec.ofNat 64 i]? = s.external[base + rsi.read s + BitVec.ofNat 64 i]?
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) (2 * count), .rip] (clearRep s) t

theorem rep_movsw_seg_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {r : SegReg} {base : BitVec 64} (count : Nat)
    (s : RamState) (h : RepMovswSegLoop r base s (count + 1)) :
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

structure RepMovswSegPre (p : BitVec 64) (r : SegReg) (base : BitVec 64) (s : RamState) :
    Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (base + rsi.read s).toNat + 2 * (rcx.read s).toNat ≤ 2^32
  dstLow : (rdi.read s).toNat + 2 * (rcx.read s).toNat ≤ 2^32
  srcMem : ∀ i < 2 * (rcx.read s).toNat, (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 2 * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (base + rsi.read s).toNat + 2 * (rcx.read s).toNat ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 2 * (rcx.read s).toNat ≤ (base + rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (2 * (rcx.read s).toNat)
  dstCode : RangeApart (rdi.read s) (2 * (rcx.read s).toNat) p 4
  seg : r.Ready base s

def repMovswSegEffect (p base : BitVec 64) (s : RamState) : Effect where
  rip := p + 4
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (2 * (rcx.read s).toNat)⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (2 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (rdi.read s) : Operand (16 * (rcx.read s).toNat)),
      (Operand.mem (base + rsi.read s) : Operand (16 * (rcx.read s).toNat)).read s⟩]

@[simp] theorem repMovswSegEffect_components (p base : BitVec 64) (s : RamState) :
    (repMovswSegEffect p base s).components =
      [.reg 6, .reg 7, .reg 1, .mem (rdi.read s) (2 * (rcx.read s).toNat), .rip] := by
  simp only [repMovswSegEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 16 * (rcx.read s).toNat / 8 = 2 * (rcx.read s).toNat by omega]

theorem repMovswSegEffect_avoids {p base : BitVec 64} {r : SegReg} {s : RamState} 
    (h : RangeApart (rdi.read s) (2 * (rcx.read s).toNat) p 4) :
    (repMovswSegEffect p base s).Avoids (codeRange p [r.prefixByte, 0xF3, 0x66, 0xA5]) :=
  Effect.avoids_of_mem (by rw [repMovswSegEffect_components]; simp [Component.isMem]) h rfl

theorem rep_movsw_seg_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF3, 0x66, 0xA5]) s) (hpre : RepMovswSegPre p r base s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF3, 0x66, 0xA5]) t ∧ (repMovswSegEffect p base s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF3, 0x66, 0xA5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovswSegEffect p base s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovswSegEffect_avoids (base := base) (r := r) hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3, 0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3, 0x66] (noSegPrefix_cons noSegPrefix_f3 (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil))]
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 4 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsw_step_zero s h.midRep [r.prefixByte, 0xF3, 0x66] (scanPrefix_seg_cons r (by simp [scanPrefix_f3, scanPrefix_66])) (by simp)
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
    have hready : RepMovswSegLoop r base s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode,
        hpre.seg⟩
    have hd := rep_movsw_seg_loop hstride c' s hready
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

theorem rep_movsw_seg_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (RepMovswSegPre p r base) (codeRange p [r.prefixByte, 0xF3, 0x66, 0xA5]) (Effect.post (repMovswSegEffect p base)) :=
  fun s h hcode hpre => ⟨_, rep_movsw_seg_steps hstride p r base s h hcode hpre⟩

theorem repMovswSegEffect_bytes {p base : BitVec 64} {s s' : RamState} (h : (repMovswSegEffect p base s).Holds s s')
    (i : Nat) (hi : i < 2 * (rcx.read s).toNat) :
    memByte s'.external (rdi.read s + BitVec.ofNat 64 i) =
      memByte s.external (base + rsi.read s + BitVec.ofNat 64 i) :=
  memByte_of_memLoad_eq (n := 16 * (rcx.read s).toNat) h.writes.2.2.2 i (by omega)

structure RepMovsbLoop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0xA4]
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

theorem RepMovsbLoop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsbLoop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovsbLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {count : Nat} (h : RepMovsbLoop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repMovsAfter 8 2 s)) := by
  have := h.dstLow
  have := h.srcLow
  exact rep_movsb_step hstride s h.ready [0xF3] (by simpa using scanPrefix_f3) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne hpos)
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩

theorem RepMovsbLoop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsbLoop s (count + 1)) : rcx.read (repMovsAfter 8 2 s) = BitVec.ofNat 64 count := by
  rw [repMovsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepMovsbLoop.source_frame [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsbLoop s count) (j : Nat) (hj : j < 1 * count) :
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

theorem RepMovsbLoop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsbLoop s (count + 2)) : RepMovsbLoop (repMovsAfter 8 2 s) (count + 1) := by
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

structure RepMovsbDone [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (1 * count)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (1 * count)
  copy : ∀ i < 1 * count,
    t.external[rdi.read s + BitVec.ofNat 64 i]? = s.external[rsi.read s + BitVec.ofNat 64 i]?
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) (1 * count), .rip] (clearRep s) t

theorem rep_movsb_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (h : RepMovsbLoop s (count + 1)) :
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

structure RepMovsbPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (rsi.read s).toNat + 1 * (rcx.read s).toNat ≤ 2^32
  dstLow : (rdi.read s).toNat + 1 * (rcx.read s).toNat ≤ 2^32
  srcMem : ∀ i < 1 * (rcx.read s).toNat, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 1 * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 1 * (rcx.read s).toNat ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 1 * (rcx.read s).toNat ≤ (rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (1 * (rcx.read s).toNat)
  dstCode : RangeApart (rdi.read s) (1 * (rcx.read s).toNat) p 2

def repMovsbEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (1 * (rcx.read s).toNat)⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (1 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (rdi.read s) : Operand (8 * (rcx.read s).toNat)),
      (Operand.mem (rsi.read s) : Operand (8 * (rcx.read s).toNat)).read s⟩]

@[simp] theorem repMovsbEffect_components (p : BitVec 64) (s : RamState) :
    (repMovsbEffect p s).components =
      [.reg 6, .reg 7, .reg 1, .mem (rdi.read s) (1 * (rcx.read s).toNat), .rip] := by
  simp only [repMovsbEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 8 * (rcx.read s).toNat / 8 = 1 * (rcx.read s).toNat by omega]

theorem repMovsbEffect_avoids {p : BitVec 64} {s : RamState} 
    (h : RangeApart (rdi.read s) (1 * (rcx.read s).toNat) p 2) :
    (repMovsbEffect p s).Avoids (codeRange p [0xF3, 0xA4]) :=
  Effect.avoids_of_mem (by rw [repMovsbEffect_components]; simp [Component.isMem]) h rfl

theorem rep_movsb_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0xA4]) s) (hpre : RepMovsbPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0xA4]) t ∧ (repMovsbEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF3, 0xA4] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovsbEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovsbEffect_avoids hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 2 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsb_step_zero s h.midRep [0xF3] (by simpa using scanPrefix_f3) (by simp)
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
    have hready : RepMovsbLoop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_movsb_loop hstride c' s hready
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

theorem rep_movsb_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepMovsbPre p) (codeRange p [0xF3, 0xA4]) (Effect.post (repMovsbEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_movsb_steps hstride p s h hcode hpre⟩

theorem repMovsbEffect_bytes {p : BitVec 64} {s s' : RamState} (h : (repMovsbEffect p s).Holds s s')
    (i : Nat) (hi : i < 1 * (rcx.read s).toNat) :
    memByte s'.external (rdi.read s + BitVec.ofNat 64 i) =
      memByte s.external (rsi.read s + BitVec.ofNat 64 i) :=
  memByte_of_memLoad_eq (n := 8 * (rcx.read s).toNat) h.writes.2.2.2 i (by omega)

structure RepMovsbSegLoop [Bindings] (r : SegReg) (base : BitVec 64) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF3, 0xA4]
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

theorem RepMovsbSegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovsbSegLoop r base s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovsbSegLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {r : SegReg} {base : BitVec 64} {s : RamState}
    {count : Nat} (h : RepMovsbSegLoop r base s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repMovsSegAfter base 8 3 s)) := by
  have := h.dstLow
  have := h.srcLow
  have hsrc : MemReadable s (base + rsi.read s) 1 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3] (noSegPrefix_cons noSegPrefix_f3 noSegPrefix_nil)]
  have hstep := rep_movsb_seg_step hstride s h.ready [r.prefixByte, 0xF3] (scanPrefix_seg_cons r (by simpa using scanPrefix_f3)) (by simp)
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

theorem RepMovsbSegLoop.rcx_after [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovsbSegLoop r base s (count + 1)) : rcx.read (repMovsSegAfter base 8 3 s) = BitVec.ofNat 64 count := by
  rw [repMovsSegAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepMovsbSegLoop.source_frame [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovsbSegLoop r base s count) (j : Nat) (hj : j < 1 * count) :
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

theorem RepMovsbSegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepMovsbSegLoop r base s (count + 2)) : RepMovsbSegLoop r base (repMovsSegAfter base 8 3 s) (count + 1) := by
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

structure RepMovsbSegDone [Bindings] (base : BitVec 64) (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (1 * count)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (1 * count)
  copy : ∀ i < 1 * count,
    t.external[rdi.read s + BitVec.ofNat 64 i]? = s.external[base + rsi.read s + BitVec.ofNat 64 i]?
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) (1 * count), .rip] (clearRep s) t

theorem rep_movsb_seg_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {r : SegReg} {base : BitVec 64} (count : Nat)
    (s : RamState) (h : RepMovsbSegLoop r base s (count + 1)) :
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

structure RepMovsbSegPre (p : BitVec 64) (r : SegReg) (base : BitVec 64) (s : RamState) :
    Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (base + rsi.read s).toNat + 1 * (rcx.read s).toNat ≤ 2^32
  dstLow : (rdi.read s).toNat + 1 * (rcx.read s).toNat ≤ 2^32
  srcMem : ∀ i < 1 * (rcx.read s).toNat, (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 1 * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (base + rsi.read s).toNat + 1 * (rcx.read s).toNat ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 1 * (rcx.read s).toNat ≤ (base + rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (1 * (rcx.read s).toNat)
  dstCode : RangeApart (rdi.read s) (1 * (rcx.read s).toNat) p 3
  seg : r.Ready base s

def repMovsbSegEffect (p base : BitVec 64) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (1 * (rcx.read s).toNat)⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (1 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (rdi.read s) : Operand (8 * (rcx.read s).toNat)),
      (Operand.mem (base + rsi.read s) : Operand (8 * (rcx.read s).toNat)).read s⟩]

@[simp] theorem repMovsbSegEffect_components (p base : BitVec 64) (s : RamState) :
    (repMovsbSegEffect p base s).components =
      [.reg 6, .reg 7, .reg 1, .mem (rdi.read s) (1 * (rcx.read s).toNat), .rip] := by
  simp only [repMovsbSegEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 8 * (rcx.read s).toNat / 8 = 1 * (rcx.read s).toNat by omega]

theorem repMovsbSegEffect_avoids {p base : BitVec 64} {r : SegReg} {s : RamState} 
    (h : RangeApart (rdi.read s) (1 * (rcx.read s).toNat) p 3) :
    (repMovsbSegEffect p base s).Avoids (codeRange p [r.prefixByte, 0xF3, 0xA4]) :=
  Effect.avoids_of_mem (by rw [repMovsbSegEffect_components]; simp [Component.isMem]) h rfl

theorem rep_movsb_seg_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF3, 0xA4]) s) (hpre : RepMovsbSegPre p r base s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF3, 0xA4]) t ∧ (repMovsbSegEffect p base s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF3, 0xA4] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovsbSegEffect p base s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovsbSegEffect_avoids (base := base) (r := r) hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3] (noSegPrefix_cons noSegPrefix_f3 noSegPrefix_nil)]
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsb_step_zero s h.midRep [r.prefixByte, 0xF3] (scanPrefix_seg_cons r (by simpa using scanPrefix_f3)) (by simp)
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
    have hready : RepMovsbSegLoop r base s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode,
        hpre.seg⟩
    have hd := rep_movsb_seg_loop hstride c' s hready
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

theorem rep_movsb_seg_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (RepMovsbSegPre p r base) (codeRange p [r.prefixByte, 0xF3, 0xA4]) (Effect.post (repMovsbSegEffect p base)) :=
  fun s h hcode hpre => ⟨_, rep_movsb_seg_steps hstride p r base s h hcode hpre⟩

theorem repMovsbSegEffect_bytes {p base : BitVec 64} {s s' : RamState} (h : (repMovsbSegEffect p base s).Holds s s')
    (i : Nat) (hi : i < 1 * (rcx.read s).toNat) :
    memByte s'.external (rdi.read s + BitVec.ofNat 64 i) =
      memByte s.external (base + rsi.read s + BitVec.ofNat 64 i) :=
  memByte_of_memLoad_eq (n := 8 * (rcx.read s).toNat) h.writes.2.2.2 i (by omega)

structure RepMovsqA32Loop [Bindings] (rex : UInt8) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF3, rex, 0xA5]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 8 * count < 2^32
  dstLow : (rdi.read s).toNat + 8 * count < 2^32
  srcMem : ∀ i < 8 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 8 * count ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 8 * count ≤ (rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (8 * count)
  dstCode : RangeApart (rdi.read s) (8 * count) s.RIP 4

theorem RepMovsqA32Loop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepMovsqA32Loop rex s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovsqA32Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState}
    {count : Nat} (h : RepMovsqA32Loop rex s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repMovsAfter 64 4 s)) := by
  have hr := hrex.rexPrefix
  have := h.dstLow
  have := h.srcLow
  exact rep_movsq_a32_step hstride s h.ready [0x67, 0xF3, rex] (scanPrefix_asz_cons (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    h.df h.code h.codeLow (h.rcx_ne hpos)
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩
    (by omega) (by omega) (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)

theorem RepMovsqA32Loop.rcx_after [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepMovsqA32Loop rex s (count + 1)) : rcx.read (repMovsAfter 64 4 s) = BitVec.ofNat 64 count := by
  rw [repMovsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepMovsqA32Loop.source_frame [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepMovsqA32Loop rex s count) (j : Nat) (hj : j < 8 * count) :
    (repMovsAfter 64 4 s).external[rsi.read s + BitVec.ofNat 64 j]? =
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

theorem RepMovsqA32Loop.next [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepMovsqA32Loop rex s (count + 2)) : RepMovsqA32Loop rex (repMovsAfter 64 4 s) (count + 1) := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hrip : (repMovsAfter 64 4 s).RIP = s.RIP := by
    rw [repMovsAfter_rip 64 4 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : rsi.read (repMovsAfter 64 4 s) = rsi.read s + BitVec.ofNat 64 8 := repMovsAfter_rsi 64 4 s
  have hd : rdi.read (repMovsAfter 64 4 s) = rdi.read s + BitVec.ofNat 64 8 := repMovsAfter_rdi 64 4 s
  have hsn : (rsi.read (repMovsAfter 64 4 s)).toNat = (rsi.read s).toNat + 8 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repMovsAfter 64 4 s)).toNat = (rdi.read s).toNat + 8 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repMovs 64 4 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
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

structure RepMovsqA32Done [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 4)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (8 * count)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (8 * count)
  copy : ∀ i < 8 * count,
    t.external[rdi.read s + BitVec.ofNat 64 i]? = s.external[rsi.read s + BitVec.ofNat 64 i]?
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) (8 * count), .rip] (clearRep s) t

theorem rep_movsq_a32_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (count : Nat)
    (s : RamState) (h : RepMovsqA32Loop rex s (count + 1)) :
    RepMovsqA32Done s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repMovsAfter 64 4 s) :=
      nextState_of_step (h.step hstride hrex (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repMovsAfter 64 4 s).Repeat_String_Operation = false := by
      rw [repMovsAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repMovs 64 4 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repMovsAfter_rip 64 4 s h.ready.msr, hc]; rfl
    · rw [repMovsAfter_rcx, hc]
    · exact repMovsAfter_rsi 64 4 s
    · exact repMovsAfter_rdi 64 4 s
    · intro i hi
      exact repMovsAfter_copy 64 4 s (by decide) i (by omega) (h.srcMem i (by omega))
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repMovs 64 4 s
  | succ m ih =>
    have hnext : nextState s = (repMovsAfter 64 4 s) :=
      nextState_of_step (h.step hstride hrex (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hs : rsi.read (repMovsAfter 64 4 s) = rsi.read s + BitVec.ofNat 64 8 := repMovsAfter_rsi 64 4 s
    have hd : rdi.read (repMovsAfter 64 4 s) = rdi.read s + BitVec.ofNat 64 8 := repMovsAfter_rdi 64 4 s
    have hfirst (i : Nat) (hi : i < 8) :
        (repMovsAfter 64 4 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[rsi.read s + BitVec.ofNat 64 i]? :=
      repMovsAfter_copy 64 4 s (by decide) i hi (h.srcMem i (by omega))
    have ih' := ih (repMovsAfter 64 4 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repMovsAfter 64 4 s).RIP = s.RIP := by
      rw [repMovsAfter_rip 64 4 s h.ready.msr, h.counter]
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
    · refine (AgreesExcept.repMovs 64 4 s |>.trans ih'.agrees).widen ?_ ?_
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

structure RepMovsqA32Pre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (rsi.read s).toNat + 8 * (rcx.read s).toNat < 2^32
  dstLow : (rdi.read s).toNat + 8 * (rcx.read s).toNat < 2^32
  srcMem : ∀ i < 8 * (rcx.read s).toNat, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 8 * (rcx.read s).toNat ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 8 * (rcx.read s).toNat ≤ (rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (8 * (rcx.read s).toNat)
  dstCode : RangeApart (rdi.read s) (8 * (rcx.read s).toNat) p 4

def repMovsqA32Effect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 4
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (8 * (rcx.read s).toNat)⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (8 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (rdi.read s) : Operand (64 * (rcx.read s).toNat)),
      (Operand.mem (rsi.read s) : Operand (64 * (rcx.read s).toNat)).read s⟩]

@[simp] theorem repMovsqA32Effect_components (p : BitVec 64) (s : RamState) :
    (repMovsqA32Effect p s).components =
      [.reg 6, .reg 7, .reg 1, .mem (rdi.read s) (8 * (rcx.read s).toNat), .rip] := by
  simp only [repMovsqA32Effect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 64 * (rcx.read s).toNat / 8 = 8 * (rcx.read s).toNat by omega]

theorem repMovsqA32Effect_avoids {p : BitVec 64} {s : RamState} (rex : UInt8) 
    (h : RangeApart (rdi.read s) (8 * (rcx.read s).toNat) p 4) :
    (repMovsqA32Effect p s).Avoids (codeRange p [0x67, 0xF3, rex, 0xA5]) :=
  Effect.avoids_of_mem (by rw [repMovsqA32Effect_components]; simp [Component.isMem]) h rfl

theorem rep_movsq_a32_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF3, rex, 0xA5]) s) (hpre : RepMovsqA32Pre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF3, rex, 0xA5]) t ∧ (repMovsqA32Effect p s).Holds s t := by
  intro t
  have hr := hrex.rexPrefix
  have hcodeS : BytesAt s s.RIP [0x67, 0xF3, rex, 0xA5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovsqA32Effect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovsqA32Effect_avoids rex hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 4 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsq_a32_step_zero s h.midRep [0x67, 0xF3, rex] (scanPrefix_asz_cons (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp)
        (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
        (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
        (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
        (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
        (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
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
    have hready : RepMovsqA32Loop rex s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_movsq_a32_loop hstride hrex c' s hready
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
    · rw [repMovsqA32Effect_components, hn]
      exact hag.mono (by simp)

theorem rep_movsq_a32_triple_of_bytes [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepMovsqA32Pre p) (codeRange p [0x67, 0xF3, rex, 0xA5]) (Effect.post (repMovsqA32Effect p)) :=
  fun s h hcode hpre => ⟨_, rep_movsq_a32_steps hstride p rex hrex s h hcode hpre⟩

theorem rep_movsq_a32_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) :
    Triple (RepMovsqA32Pre p) (codeRange p [0x67, 0xF3, 0x48, 0xA5]) (Effect.post (repMovsqA32Effect p)) :=
  rep_movsq_a32_triple_of_bytes hstride p 0x48 (by unfold RexWPrefix; decide)

theorem repMovsqA32Effect_bytes {p : BitVec 64} {s s' : RamState} (h : (repMovsqA32Effect p s).Holds s s')
    (i : Nat) (hi : i < 8 * (rcx.read s).toNat) :
    memByte s'.external (rdi.read s + BitVec.ofNat 64 i) =
      memByte s.external (rsi.read s + BitVec.ofNat 64 i) :=
  memByte_of_memLoad_eq (n := 64 * (rcx.read s).toNat) h.writes.2.2.2 i (by omega)

structure RepMovsdA32Loop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF3, 0xA5]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 4 * count < 2^32
  dstLow : (rdi.read s).toNat + 4 * count < 2^32
  srcMem : ∀ i < 4 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 4 * count ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 4 * count ≤ (rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (4 * count)
  dstCode : RangeApart (rdi.read s) (4 * count) s.RIP 3

theorem RepMovsdA32Loop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsdA32Loop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovsdA32Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {count : Nat} (h : RepMovsdA32Loop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repMovsAfter 32 3 s)) := by
  have := h.dstLow
  have := h.srcLow
  exact rep_movsd_a32_step hstride s h.ready [0x67, 0xF3] (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    h.df h.code h.codeLow (h.rcx_ne hpos)
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩
    (by omega) (by omega) (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)

theorem RepMovsdA32Loop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsdA32Loop s (count + 1)) : rcx.read (repMovsAfter 32 3 s) = BitVec.ofNat 64 count := by
  rw [repMovsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepMovsdA32Loop.source_frame [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsdA32Loop s count) (j : Nat) (hj : j < 4 * count) :
    (repMovsAfter 32 3 s).external[rsi.read s + BitVec.ofNat 64 j]? =
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

theorem RepMovsdA32Loop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsdA32Loop s (count + 2)) : RepMovsdA32Loop (repMovsAfter 32 3 s) (count + 1) := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hrip : (repMovsAfter 32 3 s).RIP = s.RIP := by
    rw [repMovsAfter_rip 32 3 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : rsi.read (repMovsAfter 32 3 s) = rsi.read s + BitVec.ofNat 64 4 := repMovsAfter_rsi 32 3 s
  have hd : rdi.read (repMovsAfter 32 3 s) = rdi.read s + BitVec.ofNat 64 4 := repMovsAfter_rdi 32 3 s
  have hsn : (rsi.read (repMovsAfter 32 3 s)).toNat = (rsi.read s).toNat + 4 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repMovsAfter 32 3 s)).toNat = (rdi.read s).toNat + 4 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repMovs 32 3 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
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

structure RepMovsdA32Done [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (4 * count)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (4 * count)
  copy : ∀ i < 4 * count,
    t.external[rdi.read s + BitVec.ofNat 64 i]? = s.external[rsi.read s + BitVec.ofNat 64 i]?
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) (4 * count), .rip] (clearRep s) t

theorem rep_movsd_a32_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (h : RepMovsdA32Loop s (count + 1)) :
    RepMovsdA32Done s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repMovsAfter 32 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repMovsAfter 32 3 s).Repeat_String_Operation = false := by
      rw [repMovsAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repMovs 32 3 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repMovsAfter_rip 32 3 s h.ready.msr, hc]; rfl
    · rw [repMovsAfter_rcx, hc]
    · exact repMovsAfter_rsi 32 3 s
    · exact repMovsAfter_rdi 32 3 s
    · intro i hi
      exact repMovsAfter_copy 32 3 s (by decide) i (by omega) (h.srcMem i (by omega))
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repMovs 32 3 s
  | succ m ih =>
    have hnext : nextState s = (repMovsAfter 32 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hs : rsi.read (repMovsAfter 32 3 s) = rsi.read s + BitVec.ofNat 64 4 := repMovsAfter_rsi 32 3 s
    have hd : rdi.read (repMovsAfter 32 3 s) = rdi.read s + BitVec.ofNat 64 4 := repMovsAfter_rdi 32 3 s
    have hfirst (i : Nat) (hi : i < 4) :
        (repMovsAfter 32 3 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[rsi.read s + BitVec.ofNat 64 i]? :=
      repMovsAfter_copy 32 3 s (by decide) i hi (h.srcMem i (by omega))
    have ih' := ih (repMovsAfter 32 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repMovsAfter 32 3 s).RIP = s.RIP := by
      rw [repMovsAfter_rip 32 3 s h.ready.msr, h.counter]
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
    · refine (AgreesExcept.repMovs 32 3 s |>.trans ih'.agrees).widen ?_ ?_
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

structure RepMovsdA32Pre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (rsi.read s).toNat + 4 * (rcx.read s).toNat < 2^32
  dstLow : (rdi.read s).toNat + 4 * (rcx.read s).toNat < 2^32
  srcMem : ∀ i < 4 * (rcx.read s).toNat, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 4 * (rcx.read s).toNat ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 4 * (rcx.read s).toNat ≤ (rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (4 * (rcx.read s).toNat)
  dstCode : RangeApart (rdi.read s) (4 * (rcx.read s).toNat) p 3

def repMovsdA32Effect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (4 * (rcx.read s).toNat)⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (4 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (rdi.read s) : Operand (32 * (rcx.read s).toNat)),
      (Operand.mem (rsi.read s) : Operand (32 * (rcx.read s).toNat)).read s⟩]

@[simp] theorem repMovsdA32Effect_components (p : BitVec 64) (s : RamState) :
    (repMovsdA32Effect p s).components =
      [.reg 6, .reg 7, .reg 1, .mem (rdi.read s) (4 * (rcx.read s).toNat), .rip] := by
  simp only [repMovsdA32Effect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 32 * (rcx.read s).toNat / 8 = 4 * (rcx.read s).toNat by omega]

theorem repMovsdA32Effect_avoids {p : BitVec 64} {s : RamState} 
    (h : RangeApart (rdi.read s) (4 * (rcx.read s).toNat) p 3) :
    (repMovsdA32Effect p s).Avoids (codeRange p [0x67, 0xF3, 0xA5]) :=
  Effect.avoids_of_mem (by rw [repMovsdA32Effect_components]; simp [Component.isMem]) h rfl

theorem rep_movsd_a32_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF3, 0xA5]) s) (hpre : RepMovsdA32Pre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF3, 0xA5]) t ∧ (repMovsdA32Effect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0x67, 0xF3, 0xA5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovsdA32Effect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovsdA32Effect_avoids hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsd_a32_step_zero s h.midRep [0x67, 0xF3] (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
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
    have hready : RepMovsdA32Loop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_movsd_a32_loop hstride c' s hready
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
    · rw [repMovsdA32Effect_components, hn]
      exact hag.mono (by simp)

theorem rep_movsd_a32_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepMovsdA32Pre p) (codeRange p [0x67, 0xF3, 0xA5]) (Effect.post (repMovsdA32Effect p)) :=
  fun s h hcode hpre => ⟨_, rep_movsd_a32_steps hstride p s h hcode hpre⟩

theorem repMovsdA32Effect_bytes {p : BitVec 64} {s s' : RamState} (h : (repMovsdA32Effect p s).Holds s s')
    (i : Nat) (hi : i < 4 * (rcx.read s).toNat) :
    memByte s'.external (rdi.read s + BitVec.ofNat 64 i) =
      memByte s.external (rsi.read s + BitVec.ofNat 64 i) :=
  memByte_of_memLoad_eq (n := 32 * (rcx.read s).toNat) h.writes.2.2.2 i (by omega)

structure RepMovswA32Loop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF3, 0x66, 0xA5]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 2 * count < 2^32
  dstLow : (rdi.read s).toNat + 2 * count < 2^32
  srcMem : ∀ i < 2 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 2 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 2 * count ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 2 * count ≤ (rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (2 * count)
  dstCode : RangeApart (rdi.read s) (2 * count) s.RIP 4

theorem RepMovswA32Loop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepMovswA32Loop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovswA32Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {count : Nat} (h : RepMovswA32Loop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repMovsAfter 16 4 s)) := by
  have := h.dstLow
  have := h.srcLow
  exact rep_movsw_a32_step hstride s h.ready [0x67, 0xF3, 0x66] (scanPrefix_asz_cons (by simp [scanPrefix_f3, scanPrefix_66])) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    h.df h.code h.codeLow (h.rcx_ne hpos)
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩
    (by omega) (by omega) (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)

theorem RepMovswA32Loop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepMovswA32Loop s (count + 1)) : rcx.read (repMovsAfter 16 4 s) = BitVec.ofNat 64 count := by
  rw [repMovsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepMovswA32Loop.source_frame [Bindings] {s : RamState} {count : Nat}
    (h : RepMovswA32Loop s count) (j : Nat) (hj : j < 2 * count) :
    (repMovsAfter 16 4 s).external[rsi.read s + BitVec.ofNat 64 j]? =
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

theorem RepMovswA32Loop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepMovswA32Loop s (count + 2)) : RepMovswA32Loop (repMovsAfter 16 4 s) (count + 1) := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hrip : (repMovsAfter 16 4 s).RIP = s.RIP := by
    rw [repMovsAfter_rip 16 4 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : rsi.read (repMovsAfter 16 4 s) = rsi.read s + BitVec.ofNat 64 2 := repMovsAfter_rsi 16 4 s
  have hd : rdi.read (repMovsAfter 16 4 s) = rdi.read s + BitVec.ofNat 64 2 := repMovsAfter_rdi 16 4 s
  have hsn : (rsi.read (repMovsAfter 16 4 s)).toNat = (rsi.read s).toNat + 2 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repMovsAfter 16 4 s)).toNat = (rdi.read s).toNat + 2 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repMovs 16 4 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
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

structure RepMovswA32Done [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 4)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (2 * count)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (2 * count)
  copy : ∀ i < 2 * count,
    t.external[rdi.read s + BitVec.ofNat 64 i]? = s.external[rsi.read s + BitVec.ofNat 64 i]?
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) (2 * count), .rip] (clearRep s) t

theorem rep_movsw_a32_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (h : RepMovswA32Loop s (count + 1)) :
    RepMovswA32Done s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repMovsAfter 16 4 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repMovsAfter 16 4 s).Repeat_String_Operation = false := by
      rw [repMovsAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repMovs 16 4 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repMovsAfter_rip 16 4 s h.ready.msr, hc]; rfl
    · rw [repMovsAfter_rcx, hc]
    · exact repMovsAfter_rsi 16 4 s
    · exact repMovsAfter_rdi 16 4 s
    · intro i hi
      exact repMovsAfter_copy 16 4 s (by decide) i (by omega) (h.srcMem i (by omega))
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repMovs 16 4 s
  | succ m ih =>
    have hnext : nextState s = (repMovsAfter 16 4 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hs : rsi.read (repMovsAfter 16 4 s) = rsi.read s + BitVec.ofNat 64 2 := repMovsAfter_rsi 16 4 s
    have hd : rdi.read (repMovsAfter 16 4 s) = rdi.read s + BitVec.ofNat 64 2 := repMovsAfter_rdi 16 4 s
    have hfirst (i : Nat) (hi : i < 2) :
        (repMovsAfter 16 4 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[rsi.read s + BitVec.ofNat 64 i]? :=
      repMovsAfter_copy 16 4 s (by decide) i hi (h.srcMem i (by omega))
    have ih' := ih (repMovsAfter 16 4 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repMovsAfter 16 4 s).RIP = s.RIP := by
      rw [repMovsAfter_rip 16 4 s h.ready.msr, h.counter]
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
    · refine (AgreesExcept.repMovs 16 4 s |>.trans ih'.agrees).widen ?_ ?_
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

structure RepMovswA32Pre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (rsi.read s).toNat + 2 * (rcx.read s).toNat < 2^32
  dstLow : (rdi.read s).toNat + 2 * (rcx.read s).toNat < 2^32
  srcMem : ∀ i < 2 * (rcx.read s).toNat, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 2 * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 2 * (rcx.read s).toNat ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 2 * (rcx.read s).toNat ≤ (rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (2 * (rcx.read s).toNat)
  dstCode : RangeApart (rdi.read s) (2 * (rcx.read s).toNat) p 4

def repMovswA32Effect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 4
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (2 * (rcx.read s).toNat)⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (2 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (rdi.read s) : Operand (16 * (rcx.read s).toNat)),
      (Operand.mem (rsi.read s) : Operand (16 * (rcx.read s).toNat)).read s⟩]

@[simp] theorem repMovswA32Effect_components (p : BitVec 64) (s : RamState) :
    (repMovswA32Effect p s).components =
      [.reg 6, .reg 7, .reg 1, .mem (rdi.read s) (2 * (rcx.read s).toNat), .rip] := by
  simp only [repMovswA32Effect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 16 * (rcx.read s).toNat / 8 = 2 * (rcx.read s).toNat by omega]

theorem repMovswA32Effect_avoids {p : BitVec 64} {s : RamState} 
    (h : RangeApart (rdi.read s) (2 * (rcx.read s).toNat) p 4) :
    (repMovswA32Effect p s).Avoids (codeRange p [0x67, 0xF3, 0x66, 0xA5]) :=
  Effect.avoids_of_mem (by rw [repMovswA32Effect_components]; simp [Component.isMem]) h rfl

theorem rep_movsw_a32_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF3, 0x66, 0xA5]) s) (hpre : RepMovswA32Pre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF3, 0x66, 0xA5]) t ∧ (repMovswA32Effect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0x67, 0xF3, 0x66, 0xA5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovswA32Effect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovswA32Effect_avoids hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 4 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsw_a32_step_zero s h.midRep [0x67, 0xF3, 0x66] (scanPrefix_asz_cons (by simp [scanPrefix_f3, scanPrefix_66])) (by simp)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
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
    have hready : RepMovswA32Loop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_movsw_a32_loop hstride c' s hready
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
    · rw [repMovswA32Effect_components, hn]
      exact hag.mono (by simp)

theorem rep_movsw_a32_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepMovswA32Pre p) (codeRange p [0x67, 0xF3, 0x66, 0xA5]) (Effect.post (repMovswA32Effect p)) :=
  fun s h hcode hpre => ⟨_, rep_movsw_a32_steps hstride p s h hcode hpre⟩

theorem repMovswA32Effect_bytes {p : BitVec 64} {s s' : RamState} (h : (repMovswA32Effect p s).Holds s s')
    (i : Nat) (hi : i < 2 * (rcx.read s).toNat) :
    memByte s'.external (rdi.read s + BitVec.ofNat 64 i) =
      memByte s.external (rsi.read s + BitVec.ofNat 64 i) :=
  memByte_of_memLoad_eq (n := 16 * (rcx.read s).toNat) h.writes.2.2.2 i (by omega)

structure RepMovsbA32Loop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF3, 0xA4]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 1 * count < 2^32
  dstLow : (rdi.read s).toNat + 1 * count < 2^32
  srcMem : ∀ i < 1 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 1 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 1 * count ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 1 * count ≤ (rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (1 * count)
  dstCode : RangeApart (rdi.read s) (1 * count) s.RIP 3

theorem RepMovsbA32Loop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsbA32Loop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovsbA32Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {count : Nat} (h : RepMovsbA32Loop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repMovsAfter 8 3 s)) := by
  have := h.dstLow
  have := h.srcLow
  exact rep_movsb_a32_step hstride s h.ready [0x67, 0xF3] (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    h.df h.code h.codeLow (h.rcx_ne hpos)
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩
    (by omega) (by omega) (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)

theorem RepMovsbA32Loop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsbA32Loop s (count + 1)) : rcx.read (repMovsAfter 8 3 s) = BitVec.ofNat 64 count := by
  rw [repMovsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepMovsbA32Loop.source_frame [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsbA32Loop s count) (j : Nat) (hj : j < 1 * count) :
    (repMovsAfter 8 3 s).external[rsi.read s + BitVec.ofNat 64 j]? =
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

theorem RepMovsbA32Loop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepMovsbA32Loop s (count + 2)) : RepMovsbA32Loop (repMovsAfter 8 3 s) (count + 1) := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hrip : (repMovsAfter 8 3 s).RIP = s.RIP := by
    rw [repMovsAfter_rip 8 3 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : rsi.read (repMovsAfter 8 3 s) = rsi.read s + BitVec.ofNat 64 1 := repMovsAfter_rsi 8 3 s
  have hd : rdi.read (repMovsAfter 8 3 s) = rdi.read s + BitVec.ofNat 64 1 := repMovsAfter_rdi 8 3 s
  have hsn : (rsi.read (repMovsAfter 8 3 s)).toNat = (rsi.read s).toNat + 1 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repMovsAfter 8 3 s)).toNat = (rdi.read s).toNat + 1 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repMovs 8 3 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
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

structure RepMovsbA32Done [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (1 * count)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (1 * count)
  copy : ∀ i < 1 * count,
    t.external[rdi.read s + BitVec.ofNat 64 i]? = s.external[rsi.read s + BitVec.ofNat 64 i]?
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) (1 * count), .rip] (clearRep s) t

theorem rep_movsb_a32_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (h : RepMovsbA32Loop s (count + 1)) :
    RepMovsbA32Done s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repMovsAfter 8 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repMovsAfter 8 3 s).Repeat_String_Operation = false := by
      rw [repMovsAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repMovs 8 3 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repMovsAfter_rip 8 3 s h.ready.msr, hc]; rfl
    · rw [repMovsAfter_rcx, hc]
    · exact repMovsAfter_rsi 8 3 s
    · exact repMovsAfter_rdi 8 3 s
    · intro i hi
      exact repMovsAfter_copy 8 3 s (by decide) i (by omega) (h.srcMem i (by omega))
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repMovs 8 3 s
  | succ m ih =>
    have hnext : nextState s = (repMovsAfter 8 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hs : rsi.read (repMovsAfter 8 3 s) = rsi.read s + BitVec.ofNat 64 1 := repMovsAfter_rsi 8 3 s
    have hd : rdi.read (repMovsAfter 8 3 s) = rdi.read s + BitVec.ofNat 64 1 := repMovsAfter_rdi 8 3 s
    have hfirst (i : Nat) (hi : i < 1) :
        (repMovsAfter 8 3 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[rsi.read s + BitVec.ofNat 64 i]? :=
      repMovsAfter_copy 8 3 s (by decide) i hi (h.srcMem i (by omega))
    have ih' := ih (repMovsAfter 8 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repMovsAfter 8 3 s).RIP = s.RIP := by
      rw [repMovsAfter_rip 8 3 s h.ready.msr, h.counter]
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
    · refine (AgreesExcept.repMovs 8 3 s |>.trans ih'.agrees).widen ?_ ?_
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

structure RepMovsbA32Pre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (rsi.read s).toNat + 1 * (rcx.read s).toNat < 2^32
  dstLow : (rdi.read s).toNat + 1 * (rcx.read s).toNat < 2^32
  srcMem : ∀ i < 1 * (rcx.read s).toNat, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 1 * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 1 * (rcx.read s).toNat ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 1 * (rcx.read s).toNat ≤ (rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (1 * (rcx.read s).toNat)
  dstCode : RangeApart (rdi.read s) (1 * (rcx.read s).toNat) p 3

def repMovsbA32Effect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (1 * (rcx.read s).toNat)⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (1 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (rdi.read s) : Operand (8 * (rcx.read s).toNat)),
      (Operand.mem (rsi.read s) : Operand (8 * (rcx.read s).toNat)).read s⟩]

@[simp] theorem repMovsbA32Effect_components (p : BitVec 64) (s : RamState) :
    (repMovsbA32Effect p s).components =
      [.reg 6, .reg 7, .reg 1, .mem (rdi.read s) (1 * (rcx.read s).toNat), .rip] := by
  simp only [repMovsbA32Effect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 8 * (rcx.read s).toNat / 8 = 1 * (rcx.read s).toNat by omega]

theorem repMovsbA32Effect_avoids {p : BitVec 64} {s : RamState} 
    (h : RangeApart (rdi.read s) (1 * (rcx.read s).toNat) p 3) :
    (repMovsbA32Effect p s).Avoids (codeRange p [0x67, 0xF3, 0xA4]) :=
  Effect.avoids_of_mem (by rw [repMovsbA32Effect_components]; simp [Component.isMem]) h rfl

theorem rep_movsb_a32_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF3, 0xA4]) s) (hpre : RepMovsbA32Pre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF3, 0xA4]) t ∧ (repMovsbA32Effect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0x67, 0xF3, 0xA4] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovsbA32Effect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovsbA32Effect_avoids hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsb_a32_step_zero s h.midRep [0x67, 0xF3] (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
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
    have hready : RepMovsbA32Loop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_movsb_a32_loop hstride c' s hready
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
    · rw [repMovsbA32Effect_components, hn]
      exact hag.mono (by simp)

theorem rep_movsb_a32_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepMovsbA32Pre p) (codeRange p [0x67, 0xF3, 0xA4]) (Effect.post (repMovsbA32Effect p)) :=
  fun s h hcode hpre => ⟨_, rep_movsb_a32_steps hstride p s h hcode hpre⟩

theorem repMovsbA32Effect_bytes {p : BitVec 64} {s s' : RamState} (h : (repMovsbA32Effect p s).Holds s s')
    (i : Nat) (hi : i < 1 * (rcx.read s).toNat) :
    memByte s'.external (rdi.read s + BitVec.ofNat 64 i) =
      memByte s.external (rsi.read s + BitVec.ofNat 64 i) :=
  memByte_of_memLoad_eq (n := 8 * (rcx.read s).toNat) h.writes.2.2.2 i (by omega)

attribute [x86_compose] repMovsqEffect repMovsqSegEffect repMovsdEffect repMovsdSegEffect repMovswEffect repMovswSegEffect repMovsbEffect repMovsbSegEffect repMovsqA32Effect repMovsdA32Effect repMovswA32Effect repMovsbA32Effect

@[x86_local] theorem repMovsqSegEffect_local {p base : BitVec 64} :
    Effect.Local (repMovsqSegEffect p base) := by
  rep_effect_local [repMovsqSegEffect]

@[x86_local] theorem repMovsdEffect_local {p : BitVec 64} : Effect.Local (repMovsdEffect p) := by
  rep_effect_local [repMovsdEffect]

@[x86_local] theorem repMovsdSegEffect_local {p base : BitVec 64} :
    Effect.Local (repMovsdSegEffect p base) := by
  rep_effect_local [repMovsdSegEffect]

@[x86_local] theorem repMovswEffect_local {p : BitVec 64} : Effect.Local (repMovswEffect p) := by
  rep_effect_local [repMovswEffect]

@[x86_local] theorem repMovswSegEffect_local {p base : BitVec 64} :
    Effect.Local (repMovswSegEffect p base) := by
  rep_effect_local [repMovswSegEffect]

@[x86_local] theorem repMovsbEffect_local {p : BitVec 64} : Effect.Local (repMovsbEffect p) := by
  rep_effect_local [repMovsbEffect]

@[x86_local] theorem repMovsbSegEffect_local {p base : BitVec 64} :
    Effect.Local (repMovsbSegEffect p base) := by
  rep_effect_local [repMovsbSegEffect]

@[x86_local] theorem repMovsqA32Effect_local {p : BitVec 64} : Effect.Local (repMovsqA32Effect p) := by
  rep_effect_local [repMovsqA32Effect]

@[x86_local] theorem repMovsdA32Effect_local {p : BitVec 64} : Effect.Local (repMovsdA32Effect p) := by
  rep_effect_local [repMovsdA32Effect]

@[x86_local] theorem repMovswA32Effect_local {p : BitVec 64} : Effect.Local (repMovswA32Effect p) := by
  rep_effect_local [repMovswA32Effect]

@[x86_local] theorem repMovsbA32Effect_local {p : BitVec 64} : Effect.Local (repMovsbA32Effect p) := by
  rep_effect_local [repMovsbA32Effect]

end X86Proofs
