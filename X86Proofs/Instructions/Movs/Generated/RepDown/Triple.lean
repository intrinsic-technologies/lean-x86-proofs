
import X86Proofs.Instructions.Movs.Generated.RepDown.Step
import X86Proofs.Program.Effect

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

structure RepMovsqDownLoop [Bindings] (rex : UInt8) (s : RamState) (slo lo : Nat) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF3, rex, 0xA5]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcTop : (rsi.read s).toNat + 8 = slo + 8 * count
  srcLow : slo + 8 * count ≤ 2^32
  dstTop : (rdi.read s).toNat + 8 = lo + 8 * count
  dstLow : lo + 8 * count ≤ 2^32
  srcMem : ∀ i < 8 * count, (s.external[BitVec.ofNat 64 slo + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * count, (s.external[BitVec.ofNat 64 lo + BitVec.ofNat 64 i]?).isSome
  disjoint : slo + 8 * count ≤ lo ∨ lo + 8 * count ≤ slo
  dstTables : PageTableEntriesApart lo (8 * count)
  dstCode : RangeApart (BitVec.ofNat 64 lo) (8 * count) s.RIP 3

theorem RepMovsqDownLoop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {slo lo : Nat} {count : Nat}
    (h : RepMovsqDownLoop rex s slo lo count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovsqDownLoop.top [Bindings] {rex : UInt8} {s : RamState} {slo lo : Nat} {count : Nat}
    (h : RepMovsqDownLoop rex s slo lo (count + 1)) (i : Nat) :
    BitVec.ofNat 64 lo + BitVec.ofNat 64 (8 * count + i) = rdi.read s + BitVec.ofNat 64 i :=
  ofNat_add_ofNat_eq (by have := h.dstTop; omega) i

theorem RepMovsqDownLoop.stop [Bindings] {rex : UInt8} {s : RamState} {slo lo : Nat} {count : Nat}
    (h : RepMovsqDownLoop rex s slo lo (count + 1)) (i : Nat) :
    BitVec.ofNat 64 slo + BitVec.ofNat 64 (8 * count + i) = rsi.read s + BitVec.ofNat 64 i :=
  ofNat_add_ofNat_eq (by have := h.srcTop; omega) i

theorem RepMovsqDownLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState}
    {slo lo : Nat} {count : Nat} (h : RepMovsqDownLoop rex s slo lo (count + 1)) :
    X86.Machine.step s = some (.next (repMovsDownAfter 64 3 s)) := by
  have hr := hrex.rexPrefix
  have := h.dstLow
  have := h.dstTop
  have := h.srcLow
  have := h.srcTop
  exact rep_movsq_down_step hstride s h.ready [0xF3, rex] (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    h.df h.code h.codeLow (h.rcx_ne (by omega))
    ⟨by omega, fun i hi => h.stop i ▸ h.srcMem (8 * count + i) (by omega)⟩
    ⟨by omega, fun i hi => h.top i ▸ h.dstMem (8 * count + i) (by omega),
      by have := h.dstTables; omega⟩

theorem RepMovsqDownLoop.source_frame [Bindings] {rex : UInt8} {s : RamState} {slo lo : Nat} {count : Nat}
    (h : RepMovsqDownLoop rex s slo lo (count + 1)) (j : Nat) (hj : j < 8 * (count + 1)) :
    (repMovsDownAfter 64 3 s).external[BitVec.ofNat 64 slo + BitVec.ofNat 64 j]? =
      s.external[BitVec.ofNat 64 slo + BitVec.ofNat 64 j]? := by
  rw [repMovsDownAfter_external]
  apply memStore_getElem?_of_ne
  intro i hi he
  rw [← h.top i] at he
  have hn := congrArg BitVec.toNat he
  have := h.srcLow
  have := h.dstLow
  have := h.disjoint
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hn
  omega

theorem RepMovsqDownLoop.next [Bindings] {rex : UInt8} {s : RamState} {slo lo : Nat} {count : Nat}
    (h : RepMovsqDownLoop rex s slo lo (count + 2)) : RepMovsqDownLoop rex (repMovsDownAfter 64 3 s) slo lo (count + 1) := by
  have hdl := h.dstLow
  have htop := h.dstTop
  have hsl := h.srcLow
  have hstop := h.srcTop
  have hrip : (repMovsDownAfter 64 3 s).RIP = s.RIP := by
    rw [repMovsDownAfter_rip 64 3 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hsn : (rsi.read (repMovsDownAfter 64 3 s)).toNat = (rsi.read s).toNat - 8 := by
    rw [repMovsDownAfter_rsi, toNat_sub_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repMovsDownAfter 64 3 s)).toNat = (rdi.read s).toNat - 8 := by
    rw [repMovsDownAfter_rdi, toNat_sub_ofNat _ _ (by omega)]
  refine ⟨h.ready.repMovsDown 64 3 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    by rw [repMovsDownAfter_rcx, h.counter, ofNat_succ_sub_one], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repMovsDownAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode (8 * (count + 1) + j) (by omega) i (by simpa using hi)
        (by rw [h.top j]; exact he)
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · omega
  · rw [hdn]; omega
  · omega
  · intro i hi
    rw [h.source_frame i (by omega)]
    exact h.srcMem i (by omega)
  · intro i hi
    rw [repMovsDownAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem i (by omega))
  · have := h.disjoint; omega
  · have := h.dstTables; omega
  · intro i hi j hj
    rw [hrip]
    exact h.dstCode i (by omega) j hj

structure RepMovsqDownDone [Bindings] (s t : RamState) (slo lo : Nat) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s - BitVec.ofNat 64 (8 * count)
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (8 * count)
  copy : ∀ i < 8 * count, t.external[BitVec.ofNat 64 lo + BitVec.ofNat 64 i]? =
    s.external[BitVec.ofNat 64 slo + BitVec.ofNat 64 i]?
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (BitVec.ofNat 64 lo) (8 * count), .rip] (clearRep s) t

theorem rep_movsq_down_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (count : Nat)
    (s : RamState) (slo lo : Nat) (h : RepMovsqDownLoop rex s slo lo (count + 1)) :
    RepMovsqDownDone s (nextStates (count + 1) s) slo lo (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repMovsDownAfter 64 3 s) :=
      nextState_of_step (h.step hstride hrex )
    have hdl := h.dstLow
    have htop := h.dstTop
    have hsl := h.srcLow
    have hstop := h.srcTop
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repMovsDownAfter 64 3 s).Repeat_String_Operation = false := by
      rw [repMovsDownAfter_repeat, hc]; rfl
    have hlo : rdi.read s = BitVec.ofNat 64 lo := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
    have hslo : rsi.read s = BitVec.ofNat 64 slo := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repMovsDown 64 3 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repMovsDownAfter_rip 64 3 s h.ready.msr, hc]; rfl
    · rw [repMovsDownAfter_rcx, hc]
    · exact repMovsDownAfter_rsi 64 3 s
    · exact repMovsDownAfter_rdi 64 3 s
    · intro i hi
      rw [← hlo, ← hslo]
      exact repMovsDownAfter_copy 64 3 s (by decide) i (by omega)
        (by rw [hslo]; exact h.srcMem i (by omega))
    · rw [← clearRep_eq hflag, ← hlo]
      exact AgreesExcept.repMovsDown 64 3 s
  | succ m ih =>
    have hnext : nextState s = (repMovsDownAfter 64 3 s) :=
      nextState_of_step (h.step hstride hrex )
    have hdl := h.dstLow
    have htop := h.dstTop
    have hsl := h.srcLow
    have hstop := h.srcTop
    have hfirst (i : Nat) (hi : i < 8) :
        (repMovsDownAfter 64 3 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[rsi.read s + BitVec.ofNat 64 i]? :=
      repMovsDownAfter_copy 64 3 s (by decide) i hi
        (h.stop i ▸ h.srcMem (8 * (m + 1) + i) (by omega))
    have ih' := ih (repMovsDownAfter 64 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repMovsDownAfter 64 3 s).RIP = s.RIP := by
      rw [repMovsDownAfter_rip 64 3 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, repMovsDownAfter_rsi, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, repMovsDownAfter_rdi, sub_ofNat_sub_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 8 * (m + 1)
      · rw [ih'.copy i hsmall, h.source_frame i (by omega)]
      · obtain ⟨j, rfl⟩ : ∃ j, i = 8 * (m + 1) + j := ⟨i - 8 * (m + 1), by omega⟩
        rw [h.top j, h.stop j]
        refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst j (by omega))
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j', hj', he⟩ := hcov
        rw [← h.top j] at he
        have hn := congrArg BitVec.toNat he
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hn
        omega
    · refine (AgreesExcept.repMovsDown 64 3 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (BitVec.ofNat 64 lo) (8 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨8 * (m + 1) + j, by omega, by rw [h.top j]; exact he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩

structure RepMovsqDownPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  srcBase : 8 * (rcx.read s).toNat ≤ (rsi.read s).toNat + 8
  srcLow : (rsi.read s).toNat + 8 ≤ 2^32
  dstBase : 8 * (rcx.read s).toNat ≤ (rdi.read s).toNat + 8
  dstLow : (rdi.read s).toNat + 8 ≤ 2^32
  srcMem : ∀ i < 8 * (rcx.read s).toNat,
    (s.external[downBase rsi 8 s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * (rcx.read s).toNat,
    (s.external[downBase rdi 8 s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 8 ≤ (rdi.read s).toNat + 8 - 8 * (rcx.read s).toNat ∨
    (rdi.read s).toNat + 8 ≤ (rsi.read s).toNat + 8 - 8 * (rcx.read s).toNat
  dstTables : PageTableEntriesApart ((rdi.read s).toNat + 8 - 8 * (rcx.read s).toNat)
    (8 * (rcx.read s).toNat)
  dstCode : RangeApart (downBase rdi 8 s) (8 * (rcx.read s).toNat) p 3

def repMovsqDownEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s - BitVec.ofNat 64 (8 * (rcx.read s).toNat)⟩,
    ⟨rdi, rdi.read s - BitVec.ofNat 64 (8 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (downBase rdi 8 s) : Operand (64 * (rcx.read s).toNat)),
      (Operand.mem (downBase rsi 8 s) : Operand (64 * (rcx.read s).toNat)).read s⟩]

@[simp] theorem repMovsqDownEffect_components (p : BitVec 64) (s : RamState) :
    (repMovsqDownEffect p s).components =
      [.reg 6, .reg 7, .reg 1, .mem (downBase rdi 8 s) (8 * (rcx.read s).toNat), .rip] := by
  simp only [repMovsqDownEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 64 * (rcx.read s).toNat / 8 = 8 * (rcx.read s).toNat by omega]

theorem repMovsqDownEffect_avoids {p : BitVec 64} {s : RamState} (rex : UInt8) 
    (h : RangeApart (downBase rdi 8 s) (8 * (rcx.read s).toNat) p 3) :
    (repMovsqDownEffect p s).Avoids (codeRange p [0xF3, rex, 0xA5]) :=
  Effect.avoids_of_mem (by rw [repMovsqDownEffect_components]; simp [Component.isMem]) h rfl

theorem rep_movsq_down_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, rex, 0xA5]) s) (hpre : RepMovsqDownPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, rex, 0xA5]) t ∧ (repMovsqDownEffect p s).Holds s t := by
  intro t
  have hr := hrex.rexPrefix
  have hcodeS : BytesAt s s.RIP [0xF3, rex, 0xA5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovsqDownEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovsqDownEffect_avoids rex hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsq_scan_step_zero s h.midRep [0xF3, rex] (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp)
        (by rw [scanContext_f3_rex _ _ hr]; rfl)
        (by rw [scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
        (by rw [scanContext_f3_rex _ _ hr]; rfl)
        (by rw [scanContext_f3_rex _ _ hr]; rfl)
        (by rw [scanContext_f3_rex _ _ hr]; rfl)
        hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repZeroAfter 3 s) :=
      (AgreesExcept.repZero 3 s).of_clearRep hrep (repZeroAfter_repeat 3 s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables, ?_, ?_, trivial, ?_⟩
    · rw [repZeroAfter_rip _ s h.ready.msr, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hag.read (by simp), hn, Nat.mul_zero]
        exact (BitVec.sub_zero _).symm
      · rw [hag.read (by simp), hn, Nat.mul_zero]
        exact (BitVec.sub_zero _).symm
      · rw [hag.read (by simp), hz]
      · apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have hi' : i < 64 * (rcx.read s).toNat := hi
        omega
    · exact hag.mono (by simp)
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.dstLow
      have := hpre.dstBase
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hsb : downBase rsi 8 s =
        BitVec.ofNat 64 ((rsi.read s).toNat + 8 - 8 * (c' + 1)) := by
      rw [downBase, hn]
    have hb : downBase rdi 8 s =
        BitVec.ofNat 64 ((rdi.read s).toNat + 8 - 8 * (c' + 1)) := by
      rw [downBase, hn]
    have hready : RepMovsqDownLoop rex s ((rsi.read s).toNat + 8 - 8 * (c' + 1)) ((rdi.read s).toNat + 8 - 8 * (c' + 1)) (c' + 1) := by
      have := hpre.dstBase
      have := hpre.dstLow
      have := hpre.srcBase
      have := hpre.srcLow
      refine ⟨h.midRep, hpre.df, hcodeS, hlow, hc, by omega, by omega, by omega, by omega,
        fun i hi => hsb ▸ hpre.srcMem i (by omega),
        fun i hi => hb ▸ hpre.dstMem i (by omega), by have := hpre.disjoint; omega, by have := hpre.dstTables; omega,
        hpre.rip ▸ hb ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_movsq_down_loop hstride hrex c' s _ _ hready
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
        rw [hb, hsb]
        apply memLoad_congr
        intro i hi
        have hi' : i < 64 * (rcx.read s).toNat / 8 := hi
        exact memByte_congr (hd.copy i (by omega))
    · rw [repMovsqDownEffect_components, hn, hb]
      exact hag.mono (by simp)

theorem rep_movsq_down_triple_of_bytes [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepMovsqDownPre p) (codeRange p [0xF3, rex, 0xA5]) (Effect.post (repMovsqDownEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_movsq_down_steps hstride p rex hrex s h hcode hpre⟩

theorem rep_movsq_down_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) :
    Triple (RepMovsqDownPre p) (codeRange p [0xF3, 0x48, 0xA5]) (Effect.post (repMovsqDownEffect p)) :=
  rep_movsq_down_triple_of_bytes hstride p 0x48 (by unfold RexWPrefix; decide)

structure RepMovsdDownLoop [Bindings] (s : RamState) (slo lo : Nat) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0xA5]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcTop : (rsi.read s).toNat + 4 = slo + 4 * count
  srcLow : slo + 4 * count ≤ 2^32
  dstTop : (rdi.read s).toNat + 4 = lo + 4 * count
  dstLow : lo + 4 * count ≤ 2^32
  srcMem : ∀ i < 4 * count, (s.external[BitVec.ofNat 64 slo + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * count, (s.external[BitVec.ofNat 64 lo + BitVec.ofNat 64 i]?).isSome
  disjoint : slo + 4 * count ≤ lo ∨ lo + 4 * count ≤ slo
  dstTables : PageTableEntriesApart lo (4 * count)
  dstCode : RangeApart (BitVec.ofNat 64 lo) (4 * count) s.RIP 2

theorem RepMovsdDownLoop.rcx_ne [Bindings] {s : RamState} {slo lo : Nat} {count : Nat}
    (h : RepMovsdDownLoop s slo lo count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovsdDownLoop.top [Bindings] {s : RamState} {slo lo : Nat} {count : Nat}
    (h : RepMovsdDownLoop s slo lo (count + 1)) (i : Nat) :
    BitVec.ofNat 64 lo + BitVec.ofNat 64 (4 * count + i) = rdi.read s + BitVec.ofNat 64 i :=
  ofNat_add_ofNat_eq (by have := h.dstTop; omega) i

theorem RepMovsdDownLoop.stop [Bindings] {s : RamState} {slo lo : Nat} {count : Nat}
    (h : RepMovsdDownLoop s slo lo (count + 1)) (i : Nat) :
    BitVec.ofNat 64 slo + BitVec.ofNat 64 (4 * count + i) = rsi.read s + BitVec.ofNat 64 i :=
  ofNat_add_ofNat_eq (by have := h.srcTop; omega) i

theorem RepMovsdDownLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {slo lo : Nat} {count : Nat} (h : RepMovsdDownLoop s slo lo (count + 1)) :
    X86.Machine.step s = some (.next (repMovsDownAfter 32 2 s)) := by
  have := h.dstLow
  have := h.dstTop
  have := h.srcLow
  have := h.srcTop
  exact rep_movsd_down_step hstride s h.ready [0xF3] (by simpa using scanPrefix_f3) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne (by omega))
    ⟨by omega, fun i hi => h.stop i ▸ h.srcMem (4 * count + i) (by omega)⟩
    ⟨by omega, fun i hi => h.top i ▸ h.dstMem (4 * count + i) (by omega),
      by have := h.dstTables; omega⟩

theorem RepMovsdDownLoop.source_frame [Bindings] {s : RamState} {slo lo : Nat} {count : Nat}
    (h : RepMovsdDownLoop s slo lo (count + 1)) (j : Nat) (hj : j < 4 * (count + 1)) :
    (repMovsDownAfter 32 2 s).external[BitVec.ofNat 64 slo + BitVec.ofNat 64 j]? =
      s.external[BitVec.ofNat 64 slo + BitVec.ofNat 64 j]? := by
  rw [repMovsDownAfter_external]
  apply memStore_getElem?_of_ne
  intro i hi he
  rw [← h.top i] at he
  have hn := congrArg BitVec.toNat he
  have := h.srcLow
  have := h.dstLow
  have := h.disjoint
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hn
  omega

theorem RepMovsdDownLoop.next [Bindings] {s : RamState} {slo lo : Nat} {count : Nat}
    (h : RepMovsdDownLoop s slo lo (count + 2)) : RepMovsdDownLoop (repMovsDownAfter 32 2 s) slo lo (count + 1) := by
  have hdl := h.dstLow
  have htop := h.dstTop
  have hsl := h.srcLow
  have hstop := h.srcTop
  have hrip : (repMovsDownAfter 32 2 s).RIP = s.RIP := by
    rw [repMovsDownAfter_rip 32 2 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hsn : (rsi.read (repMovsDownAfter 32 2 s)).toNat = (rsi.read s).toNat - 4 := by
    rw [repMovsDownAfter_rsi, toNat_sub_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repMovsDownAfter 32 2 s)).toNat = (rdi.read s).toNat - 4 := by
    rw [repMovsDownAfter_rdi, toNat_sub_ofNat _ _ (by omega)]
  refine ⟨h.ready.repMovsDown 32 2 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    by rw [repMovsDownAfter_rcx, h.counter, ofNat_succ_sub_one], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repMovsDownAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode (4 * (count + 1) + j) (by omega) i (by simpa using hi)
        (by rw [h.top j]; exact he)
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · omega
  · rw [hdn]; omega
  · omega
  · intro i hi
    rw [h.source_frame i (by omega)]
    exact h.srcMem i (by omega)
  · intro i hi
    rw [repMovsDownAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem i (by omega))
  · have := h.disjoint; omega
  · have := h.dstTables; omega
  · intro i hi j hj
    rw [hrip]
    exact h.dstCode i (by omega) j hj

structure RepMovsdDownDone [Bindings] (s t : RamState) (slo lo : Nat) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s - BitVec.ofNat 64 (4 * count)
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (4 * count)
  copy : ∀ i < 4 * count, t.external[BitVec.ofNat 64 lo + BitVec.ofNat 64 i]? =
    s.external[BitVec.ofNat 64 slo + BitVec.ofNat 64 i]?
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (BitVec.ofNat 64 lo) (4 * count), .rip] (clearRep s) t

theorem rep_movsd_down_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (slo lo : Nat) (h : RepMovsdDownLoop s slo lo (count + 1)) :
    RepMovsdDownDone s (nextStates (count + 1) s) slo lo (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repMovsDownAfter 32 2 s) :=
      nextState_of_step (h.step hstride )
    have hdl := h.dstLow
    have htop := h.dstTop
    have hsl := h.srcLow
    have hstop := h.srcTop
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repMovsDownAfter 32 2 s).Repeat_String_Operation = false := by
      rw [repMovsDownAfter_repeat, hc]; rfl
    have hlo : rdi.read s = BitVec.ofNat 64 lo := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
    have hslo : rsi.read s = BitVec.ofNat 64 slo := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repMovsDown 32 2 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repMovsDownAfter_rip 32 2 s h.ready.msr, hc]; rfl
    · rw [repMovsDownAfter_rcx, hc]
    · exact repMovsDownAfter_rsi 32 2 s
    · exact repMovsDownAfter_rdi 32 2 s
    · intro i hi
      rw [← hlo, ← hslo]
      exact repMovsDownAfter_copy 32 2 s (by decide) i (by omega)
        (by rw [hslo]; exact h.srcMem i (by omega))
    · rw [← clearRep_eq hflag, ← hlo]
      exact AgreesExcept.repMovsDown 32 2 s
  | succ m ih =>
    have hnext : nextState s = (repMovsDownAfter 32 2 s) :=
      nextState_of_step (h.step hstride )
    have hdl := h.dstLow
    have htop := h.dstTop
    have hsl := h.srcLow
    have hstop := h.srcTop
    have hfirst (i : Nat) (hi : i < 4) :
        (repMovsDownAfter 32 2 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[rsi.read s + BitVec.ofNat 64 i]? :=
      repMovsDownAfter_copy 32 2 s (by decide) i hi
        (h.stop i ▸ h.srcMem (4 * (m + 1) + i) (by omega))
    have ih' := ih (repMovsDownAfter 32 2 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repMovsDownAfter 32 2 s).RIP = s.RIP := by
      rw [repMovsDownAfter_rip 32 2 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, repMovsDownAfter_rsi, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, repMovsDownAfter_rdi, sub_ofNat_sub_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 4 * (m + 1)
      · rw [ih'.copy i hsmall, h.source_frame i (by omega)]
      · obtain ⟨j, rfl⟩ : ∃ j, i = 4 * (m + 1) + j := ⟨i - 4 * (m + 1), by omega⟩
        rw [h.top j, h.stop j]
        refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst j (by omega))
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j', hj', he⟩ := hcov
        rw [← h.top j] at he
        have hn := congrArg BitVec.toNat he
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hn
        omega
    · refine (AgreesExcept.repMovsDown 32 2 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (BitVec.ofNat 64 lo) (4 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨4 * (m + 1) + j, by omega, by rw [h.top j]; exact he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩

structure RepMovsdDownPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  srcBase : 4 * (rcx.read s).toNat ≤ (rsi.read s).toNat + 4
  srcLow : (rsi.read s).toNat + 4 ≤ 2^32
  dstBase : 4 * (rcx.read s).toNat ≤ (rdi.read s).toNat + 4
  dstLow : (rdi.read s).toNat + 4 ≤ 2^32
  srcMem : ∀ i < 4 * (rcx.read s).toNat,
    (s.external[downBase rsi 4 s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * (rcx.read s).toNat,
    (s.external[downBase rdi 4 s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 4 ≤ (rdi.read s).toNat + 4 - 4 * (rcx.read s).toNat ∨
    (rdi.read s).toNat + 4 ≤ (rsi.read s).toNat + 4 - 4 * (rcx.read s).toNat
  dstTables : PageTableEntriesApart ((rdi.read s).toNat + 4 - 4 * (rcx.read s).toNat)
    (4 * (rcx.read s).toNat)
  dstCode : RangeApart (downBase rdi 4 s) (4 * (rcx.read s).toNat) p 2

def repMovsdDownEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rsi, rsi.read s - BitVec.ofNat 64 (4 * (rcx.read s).toNat)⟩,
    ⟨rdi, rdi.read s - BitVec.ofNat 64 (4 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (downBase rdi 4 s) : Operand (32 * (rcx.read s).toNat)),
      (Operand.mem (downBase rsi 4 s) : Operand (32 * (rcx.read s).toNat)).read s⟩]

@[simp] theorem repMovsdDownEffect_components (p : BitVec 64) (s : RamState) :
    (repMovsdDownEffect p s).components =
      [.reg 6, .reg 7, .reg 1, .mem (downBase rdi 4 s) (4 * (rcx.read s).toNat), .rip] := by
  simp only [repMovsdDownEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 32 * (rcx.read s).toNat / 8 = 4 * (rcx.read s).toNat by omega]

theorem repMovsdDownEffect_avoids {p : BitVec 64} {s : RamState} 
    (h : RangeApart (downBase rdi 4 s) (4 * (rcx.read s).toNat) p 2) :
    (repMovsdDownEffect p s).Avoids (codeRange p [0xF3, 0xA5]) :=
  Effect.avoids_of_mem (by rw [repMovsdDownEffect_components]; simp [Component.isMem]) h rfl

theorem rep_movsd_down_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0xA5]) s) (hpre : RepMovsdDownPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0xA5]) t ∧ (repMovsdDownEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF3, 0xA5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovsdDownEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovsdDownEffect_avoids hpre.dstCode) hcode, hh.2⟩
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
      · rw [hag.read (by simp), hn, Nat.mul_zero]
        exact (BitVec.sub_zero _).symm
      · rw [hag.read (by simp), hn, Nat.mul_zero]
        exact (BitVec.sub_zero _).symm
      · rw [hag.read (by simp), hz]
      · apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have hi' : i < 32 * (rcx.read s).toNat := hi
        omega
    · exact hag.mono (by simp)
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.dstLow
      have := hpre.dstBase
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hsb : downBase rsi 4 s =
        BitVec.ofNat 64 ((rsi.read s).toNat + 4 - 4 * (c' + 1)) := by
      rw [downBase, hn]
    have hb : downBase rdi 4 s =
        BitVec.ofNat 64 ((rdi.read s).toNat + 4 - 4 * (c' + 1)) := by
      rw [downBase, hn]
    have hready : RepMovsdDownLoop s ((rsi.read s).toNat + 4 - 4 * (c' + 1)) ((rdi.read s).toNat + 4 - 4 * (c' + 1)) (c' + 1) := by
      have := hpre.dstBase
      have := hpre.dstLow
      have := hpre.srcBase
      have := hpre.srcLow
      refine ⟨h.midRep, hpre.df, hcodeS, hlow, hc, by omega, by omega, by omega, by omega,
        fun i hi => hsb ▸ hpre.srcMem i (by omega),
        fun i hi => hb ▸ hpre.dstMem i (by omega), by have := hpre.disjoint; omega, by have := hpre.dstTables; omega,
        hpre.rip ▸ hb ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_movsd_down_loop hstride c' s _ _ hready
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
        rw [hb, hsb]
        apply memLoad_congr
        intro i hi
        have hi' : i < 32 * (rcx.read s).toNat / 8 := hi
        exact memByte_congr (hd.copy i (by omega))
    · rw [repMovsdDownEffect_components, hn, hb]
      exact hag.mono (by simp)

theorem rep_movsd_down_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepMovsdDownPre p) (codeRange p [0xF3, 0xA5]) (Effect.post (repMovsdDownEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_movsd_down_steps hstride p s h hcode hpre⟩

structure RepMovswDownLoop [Bindings] (s : RamState) (slo lo : Nat) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0x66, 0xA5]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcTop : (rsi.read s).toNat + 2 = slo + 2 * count
  srcLow : slo + 2 * count ≤ 2^32
  dstTop : (rdi.read s).toNat + 2 = lo + 2 * count
  dstLow : lo + 2 * count ≤ 2^32
  srcMem : ∀ i < 2 * count, (s.external[BitVec.ofNat 64 slo + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 2 * count, (s.external[BitVec.ofNat 64 lo + BitVec.ofNat 64 i]?).isSome
  disjoint : slo + 2 * count ≤ lo ∨ lo + 2 * count ≤ slo
  dstTables : PageTableEntriesApart lo (2 * count)
  dstCode : RangeApart (BitVec.ofNat 64 lo) (2 * count) s.RIP 3

theorem RepMovswDownLoop.rcx_ne [Bindings] {s : RamState} {slo lo : Nat} {count : Nat}
    (h : RepMovswDownLoop s slo lo count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovswDownLoop.top [Bindings] {s : RamState} {slo lo : Nat} {count : Nat}
    (h : RepMovswDownLoop s slo lo (count + 1)) (i : Nat) :
    BitVec.ofNat 64 lo + BitVec.ofNat 64 (2 * count + i) = rdi.read s + BitVec.ofNat 64 i :=
  ofNat_add_ofNat_eq (by have := h.dstTop; omega) i

theorem RepMovswDownLoop.stop [Bindings] {s : RamState} {slo lo : Nat} {count : Nat}
    (h : RepMovswDownLoop s slo lo (count + 1)) (i : Nat) :
    BitVec.ofNat 64 slo + BitVec.ofNat 64 (2 * count + i) = rsi.read s + BitVec.ofNat 64 i :=
  ofNat_add_ofNat_eq (by have := h.srcTop; omega) i

theorem RepMovswDownLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {slo lo : Nat} {count : Nat} (h : RepMovswDownLoop s slo lo (count + 1)) :
    X86.Machine.step s = some (.next (repMovsDownAfter 16 3 s)) := by
  have := h.dstLow
  have := h.dstTop
  have := h.srcLow
  have := h.srcTop
  exact rep_movsw_down_step hstride s h.ready [0xF3, 0x66] (by simp [scanPrefix_f3, scanPrefix_66]) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne (by omega))
    ⟨by omega, fun i hi => h.stop i ▸ h.srcMem (2 * count + i) (by omega)⟩
    ⟨by omega, fun i hi => h.top i ▸ h.dstMem (2 * count + i) (by omega),
      by have := h.dstTables; omega⟩

theorem RepMovswDownLoop.source_frame [Bindings] {s : RamState} {slo lo : Nat} {count : Nat}
    (h : RepMovswDownLoop s slo lo (count + 1)) (j : Nat) (hj : j < 2 * (count + 1)) :
    (repMovsDownAfter 16 3 s).external[BitVec.ofNat 64 slo + BitVec.ofNat 64 j]? =
      s.external[BitVec.ofNat 64 slo + BitVec.ofNat 64 j]? := by
  rw [repMovsDownAfter_external]
  apply memStore_getElem?_of_ne
  intro i hi he
  rw [← h.top i] at he
  have hn := congrArg BitVec.toNat he
  have := h.srcLow
  have := h.dstLow
  have := h.disjoint
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hn
  omega

theorem RepMovswDownLoop.next [Bindings] {s : RamState} {slo lo : Nat} {count : Nat}
    (h : RepMovswDownLoop s slo lo (count + 2)) : RepMovswDownLoop (repMovsDownAfter 16 3 s) slo lo (count + 1) := by
  have hdl := h.dstLow
  have htop := h.dstTop
  have hsl := h.srcLow
  have hstop := h.srcTop
  have hrip : (repMovsDownAfter 16 3 s).RIP = s.RIP := by
    rw [repMovsDownAfter_rip 16 3 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hsn : (rsi.read (repMovsDownAfter 16 3 s)).toNat = (rsi.read s).toNat - 2 := by
    rw [repMovsDownAfter_rsi, toNat_sub_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repMovsDownAfter 16 3 s)).toNat = (rdi.read s).toNat - 2 := by
    rw [repMovsDownAfter_rdi, toNat_sub_ofNat _ _ (by omega)]
  refine ⟨h.ready.repMovsDown 16 3 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    by rw [repMovsDownAfter_rcx, h.counter, ofNat_succ_sub_one], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repMovsDownAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode (2 * (count + 1) + j) (by omega) i (by simpa using hi)
        (by rw [h.top j]; exact he)
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · omega
  · rw [hdn]; omega
  · omega
  · intro i hi
    rw [h.source_frame i (by omega)]
    exact h.srcMem i (by omega)
  · intro i hi
    rw [repMovsDownAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem i (by omega))
  · have := h.disjoint; omega
  · have := h.dstTables; omega
  · intro i hi j hj
    rw [hrip]
    exact h.dstCode i (by omega) j hj

structure RepMovswDownDone [Bindings] (s t : RamState) (slo lo : Nat) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s - BitVec.ofNat 64 (2 * count)
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (2 * count)
  copy : ∀ i < 2 * count, t.external[BitVec.ofNat 64 lo + BitVec.ofNat 64 i]? =
    s.external[BitVec.ofNat 64 slo + BitVec.ofNat 64 i]?
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (BitVec.ofNat 64 lo) (2 * count), .rip] (clearRep s) t

theorem rep_movsw_down_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (slo lo : Nat) (h : RepMovswDownLoop s slo lo (count + 1)) :
    RepMovswDownDone s (nextStates (count + 1) s) slo lo (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repMovsDownAfter 16 3 s) :=
      nextState_of_step (h.step hstride )
    have hdl := h.dstLow
    have htop := h.dstTop
    have hsl := h.srcLow
    have hstop := h.srcTop
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repMovsDownAfter 16 3 s).Repeat_String_Operation = false := by
      rw [repMovsDownAfter_repeat, hc]; rfl
    have hlo : rdi.read s = BitVec.ofNat 64 lo := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
    have hslo : rsi.read s = BitVec.ofNat 64 slo := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repMovsDown 16 3 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repMovsDownAfter_rip 16 3 s h.ready.msr, hc]; rfl
    · rw [repMovsDownAfter_rcx, hc]
    · exact repMovsDownAfter_rsi 16 3 s
    · exact repMovsDownAfter_rdi 16 3 s
    · intro i hi
      rw [← hlo, ← hslo]
      exact repMovsDownAfter_copy 16 3 s (by decide) i (by omega)
        (by rw [hslo]; exact h.srcMem i (by omega))
    · rw [← clearRep_eq hflag, ← hlo]
      exact AgreesExcept.repMovsDown 16 3 s
  | succ m ih =>
    have hnext : nextState s = (repMovsDownAfter 16 3 s) :=
      nextState_of_step (h.step hstride )
    have hdl := h.dstLow
    have htop := h.dstTop
    have hsl := h.srcLow
    have hstop := h.srcTop
    have hfirst (i : Nat) (hi : i < 2) :
        (repMovsDownAfter 16 3 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[rsi.read s + BitVec.ofNat 64 i]? :=
      repMovsDownAfter_copy 16 3 s (by decide) i hi
        (h.stop i ▸ h.srcMem (2 * (m + 1) + i) (by omega))
    have ih' := ih (repMovsDownAfter 16 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repMovsDownAfter 16 3 s).RIP = s.RIP := by
      rw [repMovsDownAfter_rip 16 3 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, repMovsDownAfter_rsi, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, repMovsDownAfter_rdi, sub_ofNat_sub_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 2 * (m + 1)
      · rw [ih'.copy i hsmall, h.source_frame i (by omega)]
      · obtain ⟨j, rfl⟩ : ∃ j, i = 2 * (m + 1) + j := ⟨i - 2 * (m + 1), by omega⟩
        rw [h.top j, h.stop j]
        refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst j (by omega))
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j', hj', he⟩ := hcov
        rw [← h.top j] at he
        have hn := congrArg BitVec.toNat he
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hn
        omega
    · refine (AgreesExcept.repMovsDown 16 3 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (BitVec.ofNat 64 lo) (2 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨2 * (m + 1) + j, by omega, by rw [h.top j]; exact he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩

structure RepMovswDownPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  srcBase : 2 * (rcx.read s).toNat ≤ (rsi.read s).toNat + 2
  srcLow : (rsi.read s).toNat + 2 ≤ 2^32
  dstBase : 2 * (rcx.read s).toNat ≤ (rdi.read s).toNat + 2
  dstLow : (rdi.read s).toNat + 2 ≤ 2^32
  srcMem : ∀ i < 2 * (rcx.read s).toNat,
    (s.external[downBase rsi 2 s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 2 * (rcx.read s).toNat,
    (s.external[downBase rdi 2 s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 2 ≤ (rdi.read s).toNat + 2 - 2 * (rcx.read s).toNat ∨
    (rdi.read s).toNat + 2 ≤ (rsi.read s).toNat + 2 - 2 * (rcx.read s).toNat
  dstTables : PageTableEntriesApart ((rdi.read s).toNat + 2 - 2 * (rcx.read s).toNat)
    (2 * (rcx.read s).toNat)
  dstCode : RangeApart (downBase rdi 2 s) (2 * (rcx.read s).toNat) p 3

def repMovswDownEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s - BitVec.ofNat 64 (2 * (rcx.read s).toNat)⟩,
    ⟨rdi, rdi.read s - BitVec.ofNat 64 (2 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (downBase rdi 2 s) : Operand (16 * (rcx.read s).toNat)),
      (Operand.mem (downBase rsi 2 s) : Operand (16 * (rcx.read s).toNat)).read s⟩]

@[simp] theorem repMovswDownEffect_components (p : BitVec 64) (s : RamState) :
    (repMovswDownEffect p s).components =
      [.reg 6, .reg 7, .reg 1, .mem (downBase rdi 2 s) (2 * (rcx.read s).toNat), .rip] := by
  simp only [repMovswDownEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 16 * (rcx.read s).toNat / 8 = 2 * (rcx.read s).toNat by omega]

theorem repMovswDownEffect_avoids {p : BitVec 64} {s : RamState} 
    (h : RangeApart (downBase rdi 2 s) (2 * (rcx.read s).toNat) p 3) :
    (repMovswDownEffect p s).Avoids (codeRange p [0xF3, 0x66, 0xA5]) :=
  Effect.avoids_of_mem (by rw [repMovswDownEffect_components]; simp [Component.isMem]) h rfl

theorem rep_movsw_down_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0x66, 0xA5]) s) (hpre : RepMovswDownPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0x66, 0xA5]) t ∧ (repMovswDownEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF3, 0x66, 0xA5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovswDownEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovswDownEffect_avoids hpre.dstCode) hcode, hh.2⟩
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
      · rw [hag.read (by simp), hn, Nat.mul_zero]
        exact (BitVec.sub_zero _).symm
      · rw [hag.read (by simp), hn, Nat.mul_zero]
        exact (BitVec.sub_zero _).symm
      · rw [hag.read (by simp), hz]
      · apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have hi' : i < 16 * (rcx.read s).toNat := hi
        omega
    · exact hag.mono (by simp)
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.dstLow
      have := hpre.dstBase
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hsb : downBase rsi 2 s =
        BitVec.ofNat 64 ((rsi.read s).toNat + 2 - 2 * (c' + 1)) := by
      rw [downBase, hn]
    have hb : downBase rdi 2 s =
        BitVec.ofNat 64 ((rdi.read s).toNat + 2 - 2 * (c' + 1)) := by
      rw [downBase, hn]
    have hready : RepMovswDownLoop s ((rsi.read s).toNat + 2 - 2 * (c' + 1)) ((rdi.read s).toNat + 2 - 2 * (c' + 1)) (c' + 1) := by
      have := hpre.dstBase
      have := hpre.dstLow
      have := hpre.srcBase
      have := hpre.srcLow
      refine ⟨h.midRep, hpre.df, hcodeS, hlow, hc, by omega, by omega, by omega, by omega,
        fun i hi => hsb ▸ hpre.srcMem i (by omega),
        fun i hi => hb ▸ hpre.dstMem i (by omega), by have := hpre.disjoint; omega, by have := hpre.dstTables; omega,
        hpre.rip ▸ hb ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_movsw_down_loop hstride c' s _ _ hready
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
        rw [hb, hsb]
        apply memLoad_congr
        intro i hi
        have hi' : i < 16 * (rcx.read s).toNat / 8 := hi
        exact memByte_congr (hd.copy i (by omega))
    · rw [repMovswDownEffect_components, hn, hb]
      exact hag.mono (by simp)

theorem rep_movsw_down_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepMovswDownPre p) (codeRange p [0xF3, 0x66, 0xA5]) (Effect.post (repMovswDownEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_movsw_down_steps hstride p s h hcode hpre⟩

structure RepMovsbDownLoop [Bindings] (s : RamState) (slo lo : Nat) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0xA4]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcTop : (rsi.read s).toNat + 1 = slo + 1 * count
  srcLow : slo + 1 * count ≤ 2^32
  dstTop : (rdi.read s).toNat + 1 = lo + 1 * count
  dstLow : lo + 1 * count ≤ 2^32
  srcMem : ∀ i < 1 * count, (s.external[BitVec.ofNat 64 slo + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 1 * count, (s.external[BitVec.ofNat 64 lo + BitVec.ofNat 64 i]?).isSome
  disjoint : slo + 1 * count ≤ lo ∨ lo + 1 * count ≤ slo
  dstTables : PageTableEntriesApart lo (1 * count)
  dstCode : RangeApart (BitVec.ofNat 64 lo) (1 * count) s.RIP 2

theorem RepMovsbDownLoop.rcx_ne [Bindings] {s : RamState} {slo lo : Nat} {count : Nat}
    (h : RepMovsbDownLoop s slo lo count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepMovsbDownLoop.top [Bindings] {s : RamState} {slo lo : Nat} {count : Nat}
    (h : RepMovsbDownLoop s slo lo (count + 1)) (i : Nat) :
    BitVec.ofNat 64 lo + BitVec.ofNat 64 (1 * count + i) = rdi.read s + BitVec.ofNat 64 i :=
  ofNat_add_ofNat_eq (by have := h.dstTop; omega) i

theorem RepMovsbDownLoop.stop [Bindings] {s : RamState} {slo lo : Nat} {count : Nat}
    (h : RepMovsbDownLoop s slo lo (count + 1)) (i : Nat) :
    BitVec.ofNat 64 slo + BitVec.ofNat 64 (1 * count + i) = rsi.read s + BitVec.ofNat 64 i :=
  ofNat_add_ofNat_eq (by have := h.srcTop; omega) i

theorem RepMovsbDownLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {slo lo : Nat} {count : Nat} (h : RepMovsbDownLoop s slo lo (count + 1)) :
    X86.Machine.step s = some (.next (repMovsDownAfter 8 2 s)) := by
  have := h.dstLow
  have := h.dstTop
  have := h.srcLow
  have := h.srcTop
  exact rep_movsb_down_step hstride s h.ready [0xF3] (by simpa using scanPrefix_f3) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne (by omega))
    ⟨by omega, fun i hi => h.stop i ▸ h.srcMem (1 * count + i) (by omega)⟩
    ⟨by omega, fun i hi => h.top i ▸ h.dstMem (1 * count + i) (by omega),
      by have := h.dstTables; omega⟩

theorem RepMovsbDownLoop.source_frame [Bindings] {s : RamState} {slo lo : Nat} {count : Nat}
    (h : RepMovsbDownLoop s slo lo (count + 1)) (j : Nat) (hj : j < 1 * (count + 1)) :
    (repMovsDownAfter 8 2 s).external[BitVec.ofNat 64 slo + BitVec.ofNat 64 j]? =
      s.external[BitVec.ofNat 64 slo + BitVec.ofNat 64 j]? := by
  rw [repMovsDownAfter_external]
  apply memStore_getElem?_of_ne
  intro i hi he
  rw [← h.top i] at he
  have hn := congrArg BitVec.toNat he
  have := h.srcLow
  have := h.dstLow
  have := h.disjoint
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hn
  omega

theorem RepMovsbDownLoop.next [Bindings] {s : RamState} {slo lo : Nat} {count : Nat}
    (h : RepMovsbDownLoop s slo lo (count + 2)) : RepMovsbDownLoop (repMovsDownAfter 8 2 s) slo lo (count + 1) := by
  have hdl := h.dstLow
  have htop := h.dstTop
  have hsl := h.srcLow
  have hstop := h.srcTop
  have hrip : (repMovsDownAfter 8 2 s).RIP = s.RIP := by
    rw [repMovsDownAfter_rip 8 2 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hsn : (rsi.read (repMovsDownAfter 8 2 s)).toNat = (rsi.read s).toNat - 1 := by
    rw [repMovsDownAfter_rsi, toNat_sub_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repMovsDownAfter 8 2 s)).toNat = (rdi.read s).toNat - 1 := by
    rw [repMovsDownAfter_rdi, toNat_sub_ofNat _ _ (by omega)]
  refine ⟨h.ready.repMovsDown 8 2 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    by rw [repMovsDownAfter_rcx, h.counter, ofNat_succ_sub_one], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repMovsDownAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode (1 * (count + 1) + j) (by omega) i (by simpa using hi)
        (by rw [h.top j]; exact he)
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · omega
  · rw [hdn]; omega
  · omega
  · intro i hi
    rw [h.source_frame i (by omega)]
    exact h.srcMem i (by omega)
  · intro i hi
    rw [repMovsDownAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem i (by omega))
  · have := h.disjoint; omega
  · have := h.dstTables; omega
  · intro i hi j hj
    rw [hrip]
    exact h.dstCode i (by omega) j hj

structure RepMovsbDownDone [Bindings] (s t : RamState) (slo lo : Nat) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s - BitVec.ofNat 64 (1 * count)
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (1 * count)
  copy : ∀ i < 1 * count, t.external[BitVec.ofNat 64 lo + BitVec.ofNat 64 i]? =
    s.external[BitVec.ofNat 64 slo + BitVec.ofNat 64 i]?
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (BitVec.ofNat 64 lo) (1 * count), .rip] (clearRep s) t

theorem rep_movsb_down_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (slo lo : Nat) (h : RepMovsbDownLoop s slo lo (count + 1)) :
    RepMovsbDownDone s (nextStates (count + 1) s) slo lo (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repMovsDownAfter 8 2 s) :=
      nextState_of_step (h.step hstride )
    have hdl := h.dstLow
    have htop := h.dstTop
    have hsl := h.srcLow
    have hstop := h.srcTop
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repMovsDownAfter 8 2 s).Repeat_String_Operation = false := by
      rw [repMovsDownAfter_repeat, hc]; rfl
    have hlo : rdi.read s = BitVec.ofNat 64 lo := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
    have hslo : rsi.read s = BitVec.ofNat 64 slo := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repMovsDown 8 2 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repMovsDownAfter_rip 8 2 s h.ready.msr, hc]; rfl
    · rw [repMovsDownAfter_rcx, hc]
    · exact repMovsDownAfter_rsi 8 2 s
    · exact repMovsDownAfter_rdi 8 2 s
    · intro i hi
      rw [← hlo, ← hslo]
      exact repMovsDownAfter_copy 8 2 s (by decide) i (by omega)
        (by rw [hslo]; exact h.srcMem i (by omega))
    · rw [← clearRep_eq hflag, ← hlo]
      exact AgreesExcept.repMovsDown 8 2 s
  | succ m ih =>
    have hnext : nextState s = (repMovsDownAfter 8 2 s) :=
      nextState_of_step (h.step hstride )
    have hdl := h.dstLow
    have htop := h.dstTop
    have hsl := h.srcLow
    have hstop := h.srcTop
    have hfirst (i : Nat) (hi : i < 1) :
        (repMovsDownAfter 8 2 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[rsi.read s + BitVec.ofNat 64 i]? :=
      repMovsDownAfter_copy 8 2 s (by decide) i hi
        (h.stop i ▸ h.srcMem (1 * (m + 1) + i) (by omega))
    have ih' := ih (repMovsDownAfter 8 2 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repMovsDownAfter 8 2 s).RIP = s.RIP := by
      rw [repMovsDownAfter_rip 8 2 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, repMovsDownAfter_rsi, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, repMovsDownAfter_rdi, sub_ofNat_sub_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 1 * (m + 1)
      · rw [ih'.copy i hsmall, h.source_frame i (by omega)]
      · obtain ⟨j, rfl⟩ : ∃ j, i = 1 * (m + 1) + j := ⟨i - 1 * (m + 1), by omega⟩
        rw [h.top j, h.stop j]
        refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst j (by omega))
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j', hj', he⟩ := hcov
        rw [← h.top j] at he
        have hn := congrArg BitVec.toNat he
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hn
        omega
    · refine (AgreesExcept.repMovsDown 8 2 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (BitVec.ofNat 64 lo) (1 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨1 * (m + 1) + j, by omega, by rw [h.top j]; exact he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩

structure RepMovsbDownPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  srcBase : 1 * (rcx.read s).toNat ≤ (rsi.read s).toNat + 1
  srcLow : (rsi.read s).toNat + 1 ≤ 2^32
  dstBase : 1 * (rcx.read s).toNat ≤ (rdi.read s).toNat + 1
  dstLow : (rdi.read s).toNat + 1 ≤ 2^32
  srcMem : ∀ i < 1 * (rcx.read s).toNat,
    (s.external[downBase rsi 1 s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 1 * (rcx.read s).toNat,
    (s.external[downBase rdi 1 s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 1 ≤ (rdi.read s).toNat + 1 - 1 * (rcx.read s).toNat ∨
    (rdi.read s).toNat + 1 ≤ (rsi.read s).toNat + 1 - 1 * (rcx.read s).toNat
  dstTables : PageTableEntriesApart ((rdi.read s).toNat + 1 - 1 * (rcx.read s).toNat)
    (1 * (rcx.read s).toNat)
  dstCode : RangeApart (downBase rdi 1 s) (1 * (rcx.read s).toNat) p 2

def repMovsbDownEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rsi, rsi.read s - BitVec.ofNat 64 (1 * (rcx.read s).toNat)⟩,
    ⟨rdi, rdi.read s - BitVec.ofNat 64 (1 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (downBase rdi 1 s) : Operand (8 * (rcx.read s).toNat)),
      (Operand.mem (downBase rsi 1 s) : Operand (8 * (rcx.read s).toNat)).read s⟩]

@[simp] theorem repMovsbDownEffect_components (p : BitVec 64) (s : RamState) :
    (repMovsbDownEffect p s).components =
      [.reg 6, .reg 7, .reg 1, .mem (downBase rdi 1 s) (1 * (rcx.read s).toNat), .rip] := by
  simp only [repMovsbDownEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 8 * (rcx.read s).toNat / 8 = 1 * (rcx.read s).toNat by omega]

theorem repMovsbDownEffect_avoids {p : BitVec 64} {s : RamState} 
    (h : RangeApart (downBase rdi 1 s) (1 * (rcx.read s).toNat) p 2) :
    (repMovsbDownEffect p s).Avoids (codeRange p [0xF3, 0xA4]) :=
  Effect.avoids_of_mem (by rw [repMovsbDownEffect_components]; simp [Component.isMem]) h rfl

theorem rep_movsb_down_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0xA4]) s) (hpre : RepMovsbDownPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0xA4]) t ∧ (repMovsbDownEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF3, 0xA4] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovsbDownEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovsbDownEffect_avoids hpre.dstCode) hcode, hh.2⟩
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
      · rw [hag.read (by simp), hn, Nat.mul_zero]
        exact (BitVec.sub_zero _).symm
      · rw [hag.read (by simp), hn, Nat.mul_zero]
        exact (BitVec.sub_zero _).symm
      · rw [hag.read (by simp), hz]
      · apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have hi' : i < 8 * (rcx.read s).toNat := hi
        omega
    · exact hag.mono (by simp)
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.dstLow
      have := hpre.dstBase
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hsb : downBase rsi 1 s =
        BitVec.ofNat 64 ((rsi.read s).toNat + 1 - 1 * (c' + 1)) := by
      rw [downBase, hn]
    have hb : downBase rdi 1 s =
        BitVec.ofNat 64 ((rdi.read s).toNat + 1 - 1 * (c' + 1)) := by
      rw [downBase, hn]
    have hready : RepMovsbDownLoop s ((rsi.read s).toNat + 1 - 1 * (c' + 1)) ((rdi.read s).toNat + 1 - 1 * (c' + 1)) (c' + 1) := by
      have := hpre.dstBase
      have := hpre.dstLow
      have := hpre.srcBase
      have := hpre.srcLow
      refine ⟨h.midRep, hpre.df, hcodeS, hlow, hc, by omega, by omega, by omega, by omega,
        fun i hi => hsb ▸ hpre.srcMem i (by omega),
        fun i hi => hb ▸ hpre.dstMem i (by omega), by have := hpre.disjoint; omega, by have := hpre.dstTables; omega,
        hpre.rip ▸ hb ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_movsb_down_loop hstride c' s _ _ hready
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
        rw [hb, hsb]
        apply memLoad_congr
        intro i hi
        have hi' : i < 8 * (rcx.read s).toNat / 8 := hi
        exact memByte_congr (hd.copy i (by omega))
    · rw [repMovsbDownEffect_components, hn, hb]
      exact hag.mono (by simp)

theorem rep_movsb_down_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepMovsbDownPre p) (codeRange p [0xF3, 0xA4]) (Effect.post (repMovsbDownEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_movsb_down_steps hstride p s h hcode hpre⟩

attribute [x86_compose] repMovsqDownEffect repMovsdDownEffect repMovswDownEffect repMovsbDownEffect

@[x86_local] theorem repMovsqDownEffect_local {p : BitVec 64} : Effect.Local (repMovsqDownEffect p) := by
  rep_effect_local [repMovsqDownEffect, downBase]

@[x86_local] theorem repMovsdDownEffect_local {p : BitVec 64} : Effect.Local (repMovsdDownEffect p) := by
  rep_effect_local [repMovsdDownEffect, downBase]

@[x86_local] theorem repMovswDownEffect_local {p : BitVec 64} : Effect.Local (repMovswDownEffect p) := by
  rep_effect_local [repMovswDownEffect, downBase]

@[x86_local] theorem repMovsbDownEffect_local {p : BitVec 64} : Effect.Local (repMovsbDownEffect p) := by
  rep_effect_local [repMovsbDownEffect, downBase]

end X86Proofs

