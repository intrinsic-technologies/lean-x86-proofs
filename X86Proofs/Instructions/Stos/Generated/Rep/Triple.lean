
import X86Proofs.Instructions.Stos.Generated.Rep.Step
import X86Proofs.Program.Effect

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

structure RepStosqLoop [Bindings] (rex : UInt8) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, rex, 0xAB]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  dstLow : (rdi.read s).toNat + 8 * count ≤ 2^32
  dstMem : ∀ i < 8 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart (rdi.read s).toNat (8 * count)
  dstCode : RangeApart (rdi.read s) (8 * count) s.RIP 3

theorem RepStosqLoop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepStosqLoop rex s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepStosqLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState}
    {count : Nat} (h : RepStosqLoop rex s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repStosAfter 64 3 s)) := by
  have hr := hrex.rexPrefix
  have := h.dstLow
  exact rep_stosq_step hstride s h.ready [0xF3, rex] (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    h.df h.code h.codeLow (h.rcx_ne hpos)
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩

theorem RepStosqLoop.rcx_after [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepStosqLoop rex s (count + 1)) : rcx.read (repStosAfter 64 3 s) = BitVec.ofNat 64 count := by
  rw [repStosAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepStosqLoop.next [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepStosqLoop rex s (count + 2)) : RepStosqLoop rex (repStosAfter 64 3 s) (count + 1) := by
  have hdl := h.dstLow
  have hrip : (repStosAfter 64 3 s).RIP = s.RIP := by
    rw [repStosAfter_rip 64 3 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hd : rdi.read (repStosAfter 64 3 s) = rdi.read s + BitVec.ofNat 64 8 := repStosAfter_rdi 64 3 s
  have hdn : (rdi.read (repStosAfter 64 3 s)).toNat = (rdi.read s).toNat + 8 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repStos 64 3 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repStosAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by omega) i (by simpa using hi) he
  · rw [hrip]; exact h.codeLow
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repStosAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (8 + i) (by omega))
  · rw [hdn]; have := h.dstTables; omega
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, hrip]
    exact h.dstCode (8 + i) (by omega) j hj

structure RepStosqDone [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rcxZero : rcx.read t = 0
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (8 * count)
  fill : ∀ i < 8 * count, t.external[rdi.read s + BitVec.ofNat 64 i]? =
    some (storedByte ((Operand.reg 0 : Operand 64).read s) (i % 8))
  agrees : AgreesExcept [.reg 1, .reg 7, .mem (rdi.read s) (8 * count), .rip] (clearRep s) t

theorem rep_stosq_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (count : Nat)
    (s : RamState) (h : RepStosqLoop rex s (count + 1)) :
    RepStosqDone s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repStosAfter 64 3 s) :=
      nextState_of_step (h.step hstride hrex (by omega))
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repStosAfter 64 3 s).Repeat_String_Operation = false := by
      rw [repStosAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repStos 64 3 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repStosAfter_rip 64 3 s h.ready.msr, hc]; rfl
    · rw [repStosAfter_rcx, hc]
    · exact repStosAfter_rdi 64 3 s
    · intro i hi
      rw [Nat.mod_eq_of_lt (show i < 8 by omega)]
      exact repStosAfter_fill 64 3 s (by decide) i (by omega)
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repStos 64 3 s
  | succ m ih =>
    have hnext : nextState s = (repStosAfter 64 3 s) :=
      nextState_of_step (h.step hstride hrex (by omega))
    have hdl := h.dstLow
    have hd : rdi.read (repStosAfter 64 3 s) = rdi.read s + BitVec.ofNat 64 8 := repStosAfter_rdi 64 3 s
    have hfirst (i : Nat) (hi : i < 8) :
        (repStosAfter 64 3 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          some (storedByte ((Operand.reg 0 : Operand 64).read s) i) :=
      repStosAfter_fill 64 3 s (by decide) i hi
    have ih' := ih (repStosAfter 64 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repStosAfter 64 3 s).RIP = s.RIP := by
      rw [repStosAfter_rip 64 3 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 8
      · rw [Nat.mod_eq_of_lt hsmall]
        refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst i hsmall)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [hd, add_ofNat_add_ofNat] at he
        have hn := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
        omega
      · have hc := ih'.fill (i - 8) (by omega)
        rw [hd, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega), repStosAfter_rax,
          show (i - 8) % 8 = i % 8 by omega] at hc
        exact hc
    · refine (AgreesExcept.repStos 64 3 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (8 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hd, add_ofNat_add_ofNat] at he
          exact ⟨8 + j, by omega, he⟩

structure RepStosqPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  dstLow : (rdi.read s).toNat + 8 * (rcx.read s).toNat ≤ 2^32
  dstMem : ∀ i < 8 * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart (rdi.read s).toNat (8 * (rcx.read s).toNat)
  dstCode : RangeApart (rdi.read s) (8 * (rcx.read s).toNat) p 3

def repStosqEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (8 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (rdi.read s) : Operand (64 * (rcx.read s).toNat)),
      ((Operand.reg 0 : Operand 64).read s).replicate (rcx.read s).toNat⟩]

@[simp] theorem repStosqEffect_components (p : BitVec 64) (s : RamState) :
    (repStosqEffect p s).components =
      [.reg 7, .reg 1, .mem (rdi.read s) (8 * (rcx.read s).toNat), .rip] := by
  simp only [repStosqEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 64 * (rcx.read s).toNat / 8 = 8 * (rcx.read s).toNat by omega]

theorem repStosqEffect_avoids {p : BitVec 64} {s : RamState} (rex : UInt8) 
    (h : RangeApart (rdi.read s) (8 * (rcx.read s).toNat) p 3) :
    (repStosqEffect p s).Avoids (codeRange p [0xF3, rex, 0xAB]) :=
  Effect.avoids_of_mem (by rw [repStosqEffect_components]; simp [Component.isMem]) h rfl

theorem rep_stosq_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, rex, 0xAB]) s) (hpre : RepStosqPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, rex, 0xAB]) t ∧ (repStosqEffect p s).Holds s t := by
  intro t
  have hr := hrex.rexPrefix
  have hcodeS : BytesAt s s.RIP [0xF3, rex, 0xAB] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repStosqEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repStosqEffect_avoids rex hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_stosq_step_zero s h.midRep [0xF3, rex] (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp)
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
    · refine ⟨?_, ?_, ?_⟩
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
    have hready : RepStosqLoop rex s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.dstLow,
        hn ▸ hpre.dstMem, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_stosq_loop hstride hrex c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, ?_, ?_, trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_⟩
      · rw [hd.rdiAfter, hn]
      · exact hd.rcxZero
      · show memLoad (nextStates (c' + 1) s).external (rdi.read s) (64 * (rcx.read s).toNat) = _
        apply memLoad_eq_of_memByte (by omega)
        intro i hi
        rw [storedByte_replicate _ (by decide) _ i (by omega)]
        have hf := hd.fill i (by omega)
        simp only [memByte, PhysicalMemory.read]
        exact congrArg (fun o : Option UInt8 => o.getD 0) hf
    · rw [repStosqEffect_components, hn]
      exact hag.mono (by simp)

theorem rep_stosq_triple_of_bytes [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepStosqPre p) (codeRange p [0xF3, rex, 0xAB]) (Effect.post (repStosqEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_stosq_steps hstride p rex hrex s h hcode hpre⟩

theorem rep_stosq_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) :
    Triple (RepStosqPre p) (codeRange p [0xF3, 0x48, 0xAB]) (Effect.post (repStosqEffect p)) :=
  rep_stosq_triple_of_bytes hstride p 0x48 (by unfold RexWPrefix; decide)

theorem repStosqEffect_bytes {p : BitVec 64} {s s' : RamState} (h : (repStosqEffect p s).Holds s s')
    (i : Nat) (hi : i < 8 * (rcx.read s).toNat) :
    memByte s'.external (rdi.read s + BitVec.ofNat 64 i) =
      storedByte ((Operand.reg 0 : Operand 64).read s) (i % 8) := by
  have hw : memLoad s'.external (rdi.read s) (64 * (rcx.read s).toNat) =
      ((Operand.reg 0 : Operand 64).read s).replicate (rcx.read s).toNat := h.writes.2.2
  rw [← storedByte_memLoad (n := 64 * (rcx.read s).toNat) _ _ i (by omega), hw,
    storedByte_replicate _ (by decide) _ i (by omega)]

structure RepStosdLoop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0xAB]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  dstLow : (rdi.read s).toNat + 4 * count ≤ 2^32
  dstMem : ∀ i < 4 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart (rdi.read s).toNat (4 * count)
  dstCode : RangeApart (rdi.read s) (4 * count) s.RIP 2

theorem RepStosdLoop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepStosdLoop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepStosdLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {count : Nat} (h : RepStosdLoop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repStosAfter 32 2 s)) := by
  have := h.dstLow
  exact rep_stosd_step hstride s h.ready [0xF3] (by simpa using scanPrefix_f3) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne hpos)
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩

theorem RepStosdLoop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepStosdLoop s (count + 1)) : rcx.read (repStosAfter 32 2 s) = BitVec.ofNat 64 count := by
  rw [repStosAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepStosdLoop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepStosdLoop s (count + 2)) : RepStosdLoop (repStosAfter 32 2 s) (count + 1) := by
  have hdl := h.dstLow
  have hrip : (repStosAfter 32 2 s).RIP = s.RIP := by
    rw [repStosAfter_rip 32 2 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hd : rdi.read (repStosAfter 32 2 s) = rdi.read s + BitVec.ofNat 64 4 := repStosAfter_rdi 32 2 s
  have hdn : (rdi.read (repStosAfter 32 2 s)).toNat = (rdi.read s).toNat + 4 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repStos 32 2 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repStosAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by omega) i (by simpa using hi) he
  · rw [hrip]; exact h.codeLow
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repStosAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (4 + i) (by omega))
  · rw [hdn]; have := h.dstTables; omega
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, hrip]
    exact h.dstCode (4 + i) (by omega) j hj

structure RepStosdDone [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rcxZero : rcx.read t = 0
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (4 * count)
  fill : ∀ i < 4 * count, t.external[rdi.read s + BitVec.ofNat 64 i]? =
    some (storedByte ((Operand.reg 0 : Operand 32).read s) (i % 4))
  agrees : AgreesExcept [.reg 1, .reg 7, .mem (rdi.read s) (4 * count), .rip] (clearRep s) t

theorem rep_stosd_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (h : RepStosdLoop s (count + 1)) :
    RepStosdDone s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repStosAfter 32 2 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repStosAfter 32 2 s).Repeat_String_Operation = false := by
      rw [repStosAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repStos 32 2 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repStosAfter_rip 32 2 s h.ready.msr, hc]; rfl
    · rw [repStosAfter_rcx, hc]
    · exact repStosAfter_rdi 32 2 s
    · intro i hi
      rw [Nat.mod_eq_of_lt (show i < 4 by omega)]
      exact repStosAfter_fill 32 2 s (by decide) i (by omega)
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repStos 32 2 s
  | succ m ih =>
    have hnext : nextState s = (repStosAfter 32 2 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hdl := h.dstLow
    have hd : rdi.read (repStosAfter 32 2 s) = rdi.read s + BitVec.ofNat 64 4 := repStosAfter_rdi 32 2 s
    have hfirst (i : Nat) (hi : i < 4) :
        (repStosAfter 32 2 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          some (storedByte ((Operand.reg 0 : Operand 32).read s) i) :=
      repStosAfter_fill 32 2 s (by decide) i hi
    have ih' := ih (repStosAfter 32 2 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repStosAfter 32 2 s).RIP = s.RIP := by
      rw [repStosAfter_rip 32 2 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 4
      · rw [Nat.mod_eq_of_lt hsmall]
        refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst i hsmall)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [hd, add_ofNat_add_ofNat] at he
        have hn := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
        omega
      · have hc := ih'.fill (i - 4) (by omega)
        rw [hd, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega), repStosAfter_rax,
          show (i - 4) % 4 = i % 4 by omega] at hc
        exact hc
    · refine (AgreesExcept.repStos 32 2 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (4 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hd, add_ofNat_add_ofNat] at he
          exact ⟨4 + j, by omega, he⟩

structure RepStosdPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  dstLow : (rdi.read s).toNat + 4 * (rcx.read s).toNat ≤ 2^32
  dstMem : ∀ i < 4 * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart (rdi.read s).toNat (4 * (rcx.read s).toNat)
  dstCode : RangeApart (rdi.read s) (4 * (rcx.read s).toNat) p 2

def repStosdEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (4 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (rdi.read s) : Operand (32 * (rcx.read s).toNat)),
      ((Operand.reg 0 : Operand 32).read s).replicate (rcx.read s).toNat⟩]

@[simp] theorem repStosdEffect_components (p : BitVec 64) (s : RamState) :
    (repStosdEffect p s).components =
      [.reg 7, .reg 1, .mem (rdi.read s) (4 * (rcx.read s).toNat), .rip] := by
  simp only [repStosdEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 32 * (rcx.read s).toNat / 8 = 4 * (rcx.read s).toNat by omega]

theorem repStosdEffect_avoids {p : BitVec 64} {s : RamState} 
    (h : RangeApart (rdi.read s) (4 * (rcx.read s).toNat) p 2) :
    (repStosdEffect p s).Avoids (codeRange p [0xF3, 0xAB]) :=
  Effect.avoids_of_mem (by rw [repStosdEffect_components]; simp [Component.isMem]) h rfl

theorem rep_stosd_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0xAB]) s) (hpre : RepStosdPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0xAB]) t ∧ (repStosdEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF3, 0xAB] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repStosdEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repStosdEffect_avoids hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 2 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_stosd_step_zero s h.midRep [0xF3] (by simpa using scanPrefix_f3) (by simp)
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
    · refine ⟨?_, ?_, ?_⟩
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
    have hready : RepStosdLoop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.dstLow,
        hn ▸ hpre.dstMem, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_stosd_loop hstride c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, ?_, ?_, trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_⟩
      · rw [hd.rdiAfter, hn]
      · exact hd.rcxZero
      · show memLoad (nextStates (c' + 1) s).external (rdi.read s) (32 * (rcx.read s).toNat) = _
        apply memLoad_eq_of_memByte (by omega)
        intro i hi
        rw [storedByte_replicate _ (by decide) _ i (by omega)]
        have hf := hd.fill i (by omega)
        simp only [memByte, PhysicalMemory.read]
        exact congrArg (fun o : Option UInt8 => o.getD 0) hf
    · rw [repStosdEffect_components, hn]
      exact hag.mono (by simp)

theorem rep_stosd_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepStosdPre p) (codeRange p [0xF3, 0xAB]) (Effect.post (repStosdEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_stosd_steps hstride p s h hcode hpre⟩

theorem repStosdEffect_bytes {p : BitVec 64} {s s' : RamState} (h : (repStosdEffect p s).Holds s s')
    (i : Nat) (hi : i < 4 * (rcx.read s).toNat) :
    memByte s'.external (rdi.read s + BitVec.ofNat 64 i) =
      storedByte ((Operand.reg 0 : Operand 32).read s) (i % 4) := by
  have hw : memLoad s'.external (rdi.read s) (32 * (rcx.read s).toNat) =
      ((Operand.reg 0 : Operand 32).read s).replicate (rcx.read s).toNat := h.writes.2.2
  rw [← storedByte_memLoad (n := 32 * (rcx.read s).toNat) _ _ i (by omega), hw,
    storedByte_replicate _ (by decide) _ i (by omega)]

structure RepStoswLoop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0x66, 0xAB]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  dstLow : (rdi.read s).toNat + 2 * count ≤ 2^32
  dstMem : ∀ i < 2 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart (rdi.read s).toNat (2 * count)
  dstCode : RangeApart (rdi.read s) (2 * count) s.RIP 3

theorem RepStoswLoop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepStoswLoop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepStoswLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {count : Nat} (h : RepStoswLoop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repStosAfter 16 3 s)) := by
  have := h.dstLow
  exact rep_stosw_step hstride s h.ready [0xF3, 0x66] (by simp [scanPrefix_f3, scanPrefix_66]) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne hpos)
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩

theorem RepStoswLoop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepStoswLoop s (count + 1)) : rcx.read (repStosAfter 16 3 s) = BitVec.ofNat 64 count := by
  rw [repStosAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepStoswLoop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepStoswLoop s (count + 2)) : RepStoswLoop (repStosAfter 16 3 s) (count + 1) := by
  have hdl := h.dstLow
  have hrip : (repStosAfter 16 3 s).RIP = s.RIP := by
    rw [repStosAfter_rip 16 3 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hd : rdi.read (repStosAfter 16 3 s) = rdi.read s + BitVec.ofNat 64 2 := repStosAfter_rdi 16 3 s
  have hdn : (rdi.read (repStosAfter 16 3 s)).toNat = (rdi.read s).toNat + 2 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repStos 16 3 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repStosAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by omega) i (by simpa using hi) he
  · rw [hrip]; exact h.codeLow
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repStosAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (2 + i) (by omega))
  · rw [hdn]; have := h.dstTables; omega
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, hrip]
    exact h.dstCode (2 + i) (by omega) j hj

structure RepStoswDone [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rcxZero : rcx.read t = 0
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (2 * count)
  fill : ∀ i < 2 * count, t.external[rdi.read s + BitVec.ofNat 64 i]? =
    some (storedByte ((Operand.reg 0 : Operand 16).read s) (i % 2))
  agrees : AgreesExcept [.reg 1, .reg 7, .mem (rdi.read s) (2 * count), .rip] (clearRep s) t

theorem rep_stosw_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (h : RepStoswLoop s (count + 1)) :
    RepStoswDone s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repStosAfter 16 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repStosAfter 16 3 s).Repeat_String_Operation = false := by
      rw [repStosAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repStos 16 3 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repStosAfter_rip 16 3 s h.ready.msr, hc]; rfl
    · rw [repStosAfter_rcx, hc]
    · exact repStosAfter_rdi 16 3 s
    · intro i hi
      rw [Nat.mod_eq_of_lt (show i < 2 by omega)]
      exact repStosAfter_fill 16 3 s (by decide) i (by omega)
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repStos 16 3 s
  | succ m ih =>
    have hnext : nextState s = (repStosAfter 16 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hdl := h.dstLow
    have hd : rdi.read (repStosAfter 16 3 s) = rdi.read s + BitVec.ofNat 64 2 := repStosAfter_rdi 16 3 s
    have hfirst (i : Nat) (hi : i < 2) :
        (repStosAfter 16 3 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          some (storedByte ((Operand.reg 0 : Operand 16).read s) i) :=
      repStosAfter_fill 16 3 s (by decide) i hi
    have ih' := ih (repStosAfter 16 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repStosAfter 16 3 s).RIP = s.RIP := by
      rw [repStosAfter_rip 16 3 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 2
      · rw [Nat.mod_eq_of_lt hsmall]
        refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst i hsmall)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [hd, add_ofNat_add_ofNat] at he
        have hn := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
        omega
      · have hc := ih'.fill (i - 2) (by omega)
        rw [hd, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega), repStosAfter_rax,
          show (i - 2) % 2 = i % 2 by omega] at hc
        exact hc
    · refine (AgreesExcept.repStos 16 3 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (2 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hd, add_ofNat_add_ofNat] at he
          exact ⟨2 + j, by omega, he⟩

structure RepStoswPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  dstLow : (rdi.read s).toNat + 2 * (rcx.read s).toNat ≤ 2^32
  dstMem : ∀ i < 2 * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart (rdi.read s).toNat (2 * (rcx.read s).toNat)
  dstCode : RangeApart (rdi.read s) (2 * (rcx.read s).toNat) p 3

def repStoswEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (2 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (rdi.read s) : Operand (16 * (rcx.read s).toNat)),
      ((Operand.reg 0 : Operand 16).read s).replicate (rcx.read s).toNat⟩]

@[simp] theorem repStoswEffect_components (p : BitVec 64) (s : RamState) :
    (repStoswEffect p s).components =
      [.reg 7, .reg 1, .mem (rdi.read s) (2 * (rcx.read s).toNat), .rip] := by
  simp only [repStoswEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 16 * (rcx.read s).toNat / 8 = 2 * (rcx.read s).toNat by omega]

theorem repStoswEffect_avoids {p : BitVec 64} {s : RamState} 
    (h : RangeApart (rdi.read s) (2 * (rcx.read s).toNat) p 3) :
    (repStoswEffect p s).Avoids (codeRange p [0xF3, 0x66, 0xAB]) :=
  Effect.avoids_of_mem (by rw [repStoswEffect_components]; simp [Component.isMem]) h rfl

theorem rep_stosw_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0x66, 0xAB]) s) (hpre : RepStoswPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0x66, 0xAB]) t ∧ (repStoswEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF3, 0x66, 0xAB] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repStoswEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repStoswEffect_avoids hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_stosw_step_zero s h.midRep [0xF3, 0x66] (by simp [scanPrefix_f3, scanPrefix_66]) (by simp)
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
    · refine ⟨?_, ?_, ?_⟩
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
    have hready : RepStoswLoop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.dstLow,
        hn ▸ hpre.dstMem, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_stosw_loop hstride c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, ?_, ?_, trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_⟩
      · rw [hd.rdiAfter, hn]
      · exact hd.rcxZero
      · show memLoad (nextStates (c' + 1) s).external (rdi.read s) (16 * (rcx.read s).toNat) = _
        apply memLoad_eq_of_memByte (by omega)
        intro i hi
        rw [storedByte_replicate _ (by decide) _ i (by omega)]
        have hf := hd.fill i (by omega)
        simp only [memByte, PhysicalMemory.read]
        exact congrArg (fun o : Option UInt8 => o.getD 0) hf
    · rw [repStoswEffect_components, hn]
      exact hag.mono (by simp)

theorem rep_stosw_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepStoswPre p) (codeRange p [0xF3, 0x66, 0xAB]) (Effect.post (repStoswEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_stosw_steps hstride p s h hcode hpre⟩

theorem repStoswEffect_bytes {p : BitVec 64} {s s' : RamState} (h : (repStoswEffect p s).Holds s s')
    (i : Nat) (hi : i < 2 * (rcx.read s).toNat) :
    memByte s'.external (rdi.read s + BitVec.ofNat 64 i) =
      storedByte ((Operand.reg 0 : Operand 16).read s) (i % 2) := by
  have hw : memLoad s'.external (rdi.read s) (16 * (rcx.read s).toNat) =
      ((Operand.reg 0 : Operand 16).read s).replicate (rcx.read s).toNat := h.writes.2.2
  rw [← storedByte_memLoad (n := 16 * (rcx.read s).toNat) _ _ i (by omega), hw,
    storedByte_replicate _ (by decide) _ i (by omega)]

structure RepStosbLoop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0xAA]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  dstLow : (rdi.read s).toNat + 1 * count ≤ 2^32
  dstMem : ∀ i < 1 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart (rdi.read s).toNat (1 * count)
  dstCode : RangeApart (rdi.read s) (1 * count) s.RIP 2

theorem RepStosbLoop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepStosbLoop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepStosbLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {count : Nat} (h : RepStosbLoop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repStosAfter 8 2 s)) := by
  have := h.dstLow
  exact rep_stosb_step hstride s h.ready [0xF3] (by simpa using scanPrefix_f3) (by simp)
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne hpos)
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩

theorem RepStosbLoop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepStosbLoop s (count + 1)) : rcx.read (repStosAfter 8 2 s) = BitVec.ofNat 64 count := by
  rw [repStosAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepStosbLoop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepStosbLoop s (count + 2)) : RepStosbLoop (repStosAfter 8 2 s) (count + 1) := by
  have hdl := h.dstLow
  have hrip : (repStosAfter 8 2 s).RIP = s.RIP := by
    rw [repStosAfter_rip 8 2 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hd : rdi.read (repStosAfter 8 2 s) = rdi.read s + BitVec.ofNat 64 1 := repStosAfter_rdi 8 2 s
  have hdn : (rdi.read (repStosAfter 8 2 s)).toNat = (rdi.read s).toNat + 1 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repStos 8 2 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repStosAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by omega) i (by simpa using hi) he
  · rw [hrip]; exact h.codeLow
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repStosAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (1 + i) (by omega))
  · rw [hdn]; have := h.dstTables; omega
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, hrip]
    exact h.dstCode (1 + i) (by omega) j hj

structure RepStosbDone [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rcxZero : rcx.read t = 0
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (1 * count)
  fill : ∀ i < 1 * count, t.external[rdi.read s + BitVec.ofNat 64 i]? =
    some (storedByte ((Operand.reg 0 : Operand 8).read s) (i % 1))
  agrees : AgreesExcept [.reg 1, .reg 7, .mem (rdi.read s) (1 * count), .rip] (clearRep s) t

theorem rep_stosb_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (h : RepStosbLoop s (count + 1)) :
    RepStosbDone s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repStosAfter 8 2 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repStosAfter 8 2 s).Repeat_String_Operation = false := by
      rw [repStosAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repStos 8 2 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repStosAfter_rip 8 2 s h.ready.msr, hc]; rfl
    · rw [repStosAfter_rcx, hc]
    · exact repStosAfter_rdi 8 2 s
    · intro i hi
      rw [Nat.mod_eq_of_lt (show i < 1 by omega)]
      exact repStosAfter_fill 8 2 s (by decide) i (by omega)
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repStos 8 2 s
  | succ m ih =>
    have hnext : nextState s = (repStosAfter 8 2 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hdl := h.dstLow
    have hd : rdi.read (repStosAfter 8 2 s) = rdi.read s + BitVec.ofNat 64 1 := repStosAfter_rdi 8 2 s
    have hfirst (i : Nat) (hi : i < 1) :
        (repStosAfter 8 2 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          some (storedByte ((Operand.reg 0 : Operand 8).read s) i) :=
      repStosAfter_fill 8 2 s (by decide) i hi
    have ih' := ih (repStosAfter 8 2 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repStosAfter 8 2 s).RIP = s.RIP := by
      rw [repStosAfter_rip 8 2 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 1
      · rw [Nat.mod_eq_of_lt hsmall]
        refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst i hsmall)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [hd, add_ofNat_add_ofNat] at he
        have hn := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
        omega
      · have hc := ih'.fill (i - 1) (by omega)
        rw [hd, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega), repStosAfter_rax,
          show (i - 1) % 1 = i % 1 by omega] at hc
        exact hc
    · refine (AgreesExcept.repStos 8 2 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (1 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hd, add_ofNat_add_ofNat] at he
          exact ⟨1 + j, by omega, he⟩

structure RepStosbPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  dstLow : (rdi.read s).toNat + 1 * (rcx.read s).toNat ≤ 2^32
  dstMem : ∀ i < 1 * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart (rdi.read s).toNat (1 * (rcx.read s).toNat)
  dstCode : RangeApart (rdi.read s) (1 * (rcx.read s).toNat) p 2

def repStosbEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (1 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (rdi.read s) : Operand (8 * (rcx.read s).toNat)),
      ((Operand.reg 0 : Operand 8).read s).replicate (rcx.read s).toNat⟩]

@[simp] theorem repStosbEffect_components (p : BitVec 64) (s : RamState) :
    (repStosbEffect p s).components =
      [.reg 7, .reg 1, .mem (rdi.read s) (1 * (rcx.read s).toNat), .rip] := by
  simp only [repStosbEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 8 * (rcx.read s).toNat / 8 = 1 * (rcx.read s).toNat by omega]

theorem repStosbEffect_avoids {p : BitVec 64} {s : RamState} 
    (h : RangeApart (rdi.read s) (1 * (rcx.read s).toNat) p 2) :
    (repStosbEffect p s).Avoids (codeRange p [0xF3, 0xAA]) :=
  Effect.avoids_of_mem (by rw [repStosbEffect_components]; simp [Component.isMem]) h rfl

theorem rep_stosb_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0xAA]) s) (hpre : RepStosbPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0xAA]) t ∧ (repStosbEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF3, 0xAA] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repStosbEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repStosbEffect_avoids hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 2 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_stosb_step_zero s h.midRep [0xF3] (by simpa using scanPrefix_f3) (by simp)
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
    · refine ⟨?_, ?_, ?_⟩
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
    have hready : RepStosbLoop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.dstLow,
        hn ▸ hpre.dstMem, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_stosb_loop hstride c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, ?_, ?_, trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_⟩
      · rw [hd.rdiAfter, hn]
      · exact hd.rcxZero
      · show memLoad (nextStates (c' + 1) s).external (rdi.read s) (8 * (rcx.read s).toNat) = _
        apply memLoad_eq_of_memByte (by omega)
        intro i hi
        rw [storedByte_replicate _ (by decide) _ i (by omega)]
        have hf := hd.fill i (by omega)
        simp only [memByte, PhysicalMemory.read]
        exact congrArg (fun o : Option UInt8 => o.getD 0) hf
    · rw [repStosbEffect_components, hn]
      exact hag.mono (by simp)

theorem rep_stosb_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepStosbPre p) (codeRange p [0xF3, 0xAA]) (Effect.post (repStosbEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_stosb_steps hstride p s h hcode hpre⟩

theorem repStosbEffect_bytes {p : BitVec 64} {s s' : RamState} (h : (repStosbEffect p s).Holds s s')
    (i : Nat) (hi : i < 1 * (rcx.read s).toNat) :
    memByte s'.external (rdi.read s + BitVec.ofNat 64 i) =
      storedByte ((Operand.reg 0 : Operand 8).read s) (i % 1) := by
  have hw : memLoad s'.external (rdi.read s) (8 * (rcx.read s).toNat) =
      ((Operand.reg 0 : Operand 8).read s).replicate (rcx.read s).toNat := h.writes.2.2
  rw [← storedByte_memLoad (n := 8 * (rcx.read s).toNat) _ _ i (by omega), hw,
    storedByte_replicate _ (by decide) _ i (by omega)]

structure RepStosqA32Loop [Bindings] (rex : UInt8) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF3, rex, 0xAB]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  dstLow : (rdi.read s).toNat + 8 * count < 2^32
  dstMem : ∀ i < 8 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart (rdi.read s).toNat (8 * count)
  dstCode : RangeApart (rdi.read s) (8 * count) s.RIP 4

theorem RepStosqA32Loop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepStosqA32Loop rex s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepStosqA32Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState}
    {count : Nat} (h : RepStosqA32Loop rex s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repStosAfter 64 4 s)) := by
  have hr := hrex.rexPrefix
  have := h.dstLow
  exact rep_stosq_a32_step hstride s h.ready [0x67, 0xF3, rex] (scanPrefix_asz_cons (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    h.df h.code h.codeLow (h.rcx_ne hpos)
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩
    (by omega) (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)

theorem RepStosqA32Loop.rcx_after [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepStosqA32Loop rex s (count + 1)) : rcx.read (repStosAfter 64 4 s) = BitVec.ofNat 64 count := by
  rw [repStosAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepStosqA32Loop.next [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepStosqA32Loop rex s (count + 2)) : RepStosqA32Loop rex (repStosAfter 64 4 s) (count + 1) := by
  have hdl := h.dstLow
  have hrip : (repStosAfter 64 4 s).RIP = s.RIP := by
    rw [repStosAfter_rip 64 4 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hd : rdi.read (repStosAfter 64 4 s) = rdi.read s + BitVec.ofNat 64 8 := repStosAfter_rdi 64 4 s
  have hdn : (rdi.read (repStosAfter 64 4 s)).toNat = (rdi.read s).toNat + 8 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repStos 64 4 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repStosAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by omega) i (by simpa using hi) he
  · rw [hrip]; exact h.codeLow
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repStosAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (8 + i) (by omega))
  · rw [hdn]; have := h.dstTables; omega
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, hrip]
    exact h.dstCode (8 + i) (by omega) j hj

structure RepStosqA32Done [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 4)
  rcxZero : rcx.read t = 0
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (8 * count)
  fill : ∀ i < 8 * count, t.external[rdi.read s + BitVec.ofNat 64 i]? =
    some (storedByte ((Operand.reg 0 : Operand 64).read s) (i % 8))
  agrees : AgreesExcept [.reg 1, .reg 7, .mem (rdi.read s) (8 * count), .rip] (clearRep s) t

theorem rep_stosq_a32_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (count : Nat)
    (s : RamState) (h : RepStosqA32Loop rex s (count + 1)) :
    RepStosqA32Done s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repStosAfter 64 4 s) :=
      nextState_of_step (h.step hstride hrex (by omega))
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repStosAfter 64 4 s).Repeat_String_Operation = false := by
      rw [repStosAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repStos 64 4 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repStosAfter_rip 64 4 s h.ready.msr, hc]; rfl
    · rw [repStosAfter_rcx, hc]
    · exact repStosAfter_rdi 64 4 s
    · intro i hi
      rw [Nat.mod_eq_of_lt (show i < 8 by omega)]
      exact repStosAfter_fill 64 4 s (by decide) i (by omega)
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repStos 64 4 s
  | succ m ih =>
    have hnext : nextState s = (repStosAfter 64 4 s) :=
      nextState_of_step (h.step hstride hrex (by omega))
    have hdl := h.dstLow
    have hd : rdi.read (repStosAfter 64 4 s) = rdi.read s + BitVec.ofNat 64 8 := repStosAfter_rdi 64 4 s
    have hfirst (i : Nat) (hi : i < 8) :
        (repStosAfter 64 4 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          some (storedByte ((Operand.reg 0 : Operand 64).read s) i) :=
      repStosAfter_fill 64 4 s (by decide) i hi
    have ih' := ih (repStosAfter 64 4 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repStosAfter 64 4 s).RIP = s.RIP := by
      rw [repStosAfter_rip 64 4 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 8
      · rw [Nat.mod_eq_of_lt hsmall]
        refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst i hsmall)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [hd, add_ofNat_add_ofNat] at he
        have hn := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
        omega
      · have hc := ih'.fill (i - 8) (by omega)
        rw [hd, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega), repStosAfter_rax,
          show (i - 8) % 8 = i % 8 by omega] at hc
        exact hc
    · refine (AgreesExcept.repStos 64 4 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (8 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hd, add_ofNat_add_ofNat] at he
          exact ⟨8 + j, by omega, he⟩

structure RepStosqA32Pre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  dstLow : (rdi.read s).toNat + 8 * (rcx.read s).toNat < 2^32
  dstMem : ∀ i < 8 * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart (rdi.read s).toNat (8 * (rcx.read s).toNat)
  dstCode : RangeApart (rdi.read s) (8 * (rcx.read s).toNat) p 4

def repStosqA32Effect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 4
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (8 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (rdi.read s) : Operand (64 * (rcx.read s).toNat)),
      ((Operand.reg 0 : Operand 64).read s).replicate (rcx.read s).toNat⟩]

@[simp] theorem repStosqA32Effect_components (p : BitVec 64) (s : RamState) :
    (repStosqA32Effect p s).components =
      [.reg 7, .reg 1, .mem (rdi.read s) (8 * (rcx.read s).toNat), .rip] := by
  simp only [repStosqA32Effect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 64 * (rcx.read s).toNat / 8 = 8 * (rcx.read s).toNat by omega]

theorem repStosqA32Effect_avoids {p : BitVec 64} {s : RamState} (rex : UInt8) 
    (h : RangeApart (rdi.read s) (8 * (rcx.read s).toNat) p 4) :
    (repStosqA32Effect p s).Avoids (codeRange p [0x67, 0xF3, rex, 0xAB]) :=
  Effect.avoids_of_mem (by rw [repStosqA32Effect_components]; simp [Component.isMem]) h rfl

theorem rep_stosq_a32_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF3, rex, 0xAB]) s) (hpre : RepStosqA32Pre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF3, rex, 0xAB]) t ∧ (repStosqA32Effect p s).Holds s t := by
  intro t
  have hr := hrex.rexPrefix
  have hcodeS : BytesAt s s.RIP [0x67, 0xF3, rex, 0xAB] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repStosqA32Effect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repStosqA32Effect_avoids rex hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 4 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_stosq_a32_step_zero s h.midRep [0x67, 0xF3, rex] (scanPrefix_asz_cons (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp)
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
    · refine ⟨?_, ?_, ?_⟩
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
    have hready : RepStosqA32Loop rex s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.dstLow,
        hn ▸ hpre.dstMem, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_stosq_a32_loop hstride hrex c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, ?_, ?_, trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_⟩
      · rw [hd.rdiAfter, hn]
      · exact hd.rcxZero
      · show memLoad (nextStates (c' + 1) s).external (rdi.read s) (64 * (rcx.read s).toNat) = _
        apply memLoad_eq_of_memByte (by omega)
        intro i hi
        rw [storedByte_replicate _ (by decide) _ i (by omega)]
        have hf := hd.fill i (by omega)
        simp only [memByte, PhysicalMemory.read]
        exact congrArg (fun o : Option UInt8 => o.getD 0) hf
    · rw [repStosqA32Effect_components, hn]
      exact hag.mono (by simp)

theorem rep_stosq_a32_triple_of_bytes [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepStosqA32Pre p) (codeRange p [0x67, 0xF3, rex, 0xAB]) (Effect.post (repStosqA32Effect p)) :=
  fun s h hcode hpre => ⟨_, rep_stosq_a32_steps hstride p rex hrex s h hcode hpre⟩

theorem rep_stosq_a32_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) :
    Triple (RepStosqA32Pre p) (codeRange p [0x67, 0xF3, 0x48, 0xAB]) (Effect.post (repStosqA32Effect p)) :=
  rep_stosq_a32_triple_of_bytes hstride p 0x48 (by unfold RexWPrefix; decide)

theorem repStosqA32Effect_bytes {p : BitVec 64} {s s' : RamState} (h : (repStosqA32Effect p s).Holds s s')
    (i : Nat) (hi : i < 8 * (rcx.read s).toNat) :
    memByte s'.external (rdi.read s + BitVec.ofNat 64 i) =
      storedByte ((Operand.reg 0 : Operand 64).read s) (i % 8) := by
  have hw : memLoad s'.external (rdi.read s) (64 * (rcx.read s).toNat) =
      ((Operand.reg 0 : Operand 64).read s).replicate (rcx.read s).toNat := h.writes.2.2
  rw [← storedByte_memLoad (n := 64 * (rcx.read s).toNat) _ _ i (by omega), hw,
    storedByte_replicate _ (by decide) _ i (by omega)]

structure RepStosdA32Loop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF3, 0xAB]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  dstLow : (rdi.read s).toNat + 4 * count < 2^32
  dstMem : ∀ i < 4 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart (rdi.read s).toNat (4 * count)
  dstCode : RangeApart (rdi.read s) (4 * count) s.RIP 3

theorem RepStosdA32Loop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepStosdA32Loop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepStosdA32Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {count : Nat} (h : RepStosdA32Loop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repStosAfter 32 3 s)) := by
  have := h.dstLow
  exact rep_stosd_a32_step hstride s h.ready [0x67, 0xF3] (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    h.df h.code h.codeLow (h.rcx_ne hpos)
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩
    (by omega) (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)

theorem RepStosdA32Loop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepStosdA32Loop s (count + 1)) : rcx.read (repStosAfter 32 3 s) = BitVec.ofNat 64 count := by
  rw [repStosAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepStosdA32Loop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepStosdA32Loop s (count + 2)) : RepStosdA32Loop (repStosAfter 32 3 s) (count + 1) := by
  have hdl := h.dstLow
  have hrip : (repStosAfter 32 3 s).RIP = s.RIP := by
    rw [repStosAfter_rip 32 3 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hd : rdi.read (repStosAfter 32 3 s) = rdi.read s + BitVec.ofNat 64 4 := repStosAfter_rdi 32 3 s
  have hdn : (rdi.read (repStosAfter 32 3 s)).toNat = (rdi.read s).toNat + 4 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repStos 32 3 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repStosAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by omega) i (by simpa using hi) he
  · rw [hrip]; exact h.codeLow
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repStosAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (4 + i) (by omega))
  · rw [hdn]; have := h.dstTables; omega
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, hrip]
    exact h.dstCode (4 + i) (by omega) j hj

structure RepStosdA32Done [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rcxZero : rcx.read t = 0
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (4 * count)
  fill : ∀ i < 4 * count, t.external[rdi.read s + BitVec.ofNat 64 i]? =
    some (storedByte ((Operand.reg 0 : Operand 32).read s) (i % 4))
  agrees : AgreesExcept [.reg 1, .reg 7, .mem (rdi.read s) (4 * count), .rip] (clearRep s) t

theorem rep_stosd_a32_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (h : RepStosdA32Loop s (count + 1)) :
    RepStosdA32Done s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repStosAfter 32 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repStosAfter 32 3 s).Repeat_String_Operation = false := by
      rw [repStosAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repStos 32 3 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repStosAfter_rip 32 3 s h.ready.msr, hc]; rfl
    · rw [repStosAfter_rcx, hc]
    · exact repStosAfter_rdi 32 3 s
    · intro i hi
      rw [Nat.mod_eq_of_lt (show i < 4 by omega)]
      exact repStosAfter_fill 32 3 s (by decide) i (by omega)
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repStos 32 3 s
  | succ m ih =>
    have hnext : nextState s = (repStosAfter 32 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hdl := h.dstLow
    have hd : rdi.read (repStosAfter 32 3 s) = rdi.read s + BitVec.ofNat 64 4 := repStosAfter_rdi 32 3 s
    have hfirst (i : Nat) (hi : i < 4) :
        (repStosAfter 32 3 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          some (storedByte ((Operand.reg 0 : Operand 32).read s) i) :=
      repStosAfter_fill 32 3 s (by decide) i hi
    have ih' := ih (repStosAfter 32 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repStosAfter 32 3 s).RIP = s.RIP := by
      rw [repStosAfter_rip 32 3 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 4
      · rw [Nat.mod_eq_of_lt hsmall]
        refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst i hsmall)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [hd, add_ofNat_add_ofNat] at he
        have hn := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
        omega
      · have hc := ih'.fill (i - 4) (by omega)
        rw [hd, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega), repStosAfter_rax,
          show (i - 4) % 4 = i % 4 by omega] at hc
        exact hc
    · refine (AgreesExcept.repStos 32 3 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (4 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hd, add_ofNat_add_ofNat] at he
          exact ⟨4 + j, by omega, he⟩

structure RepStosdA32Pre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  dstLow : (rdi.read s).toNat + 4 * (rcx.read s).toNat < 2^32
  dstMem : ∀ i < 4 * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart (rdi.read s).toNat (4 * (rcx.read s).toNat)
  dstCode : RangeApart (rdi.read s) (4 * (rcx.read s).toNat) p 3

def repStosdA32Effect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (4 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (rdi.read s) : Operand (32 * (rcx.read s).toNat)),
      ((Operand.reg 0 : Operand 32).read s).replicate (rcx.read s).toNat⟩]

@[simp] theorem repStosdA32Effect_components (p : BitVec 64) (s : RamState) :
    (repStosdA32Effect p s).components =
      [.reg 7, .reg 1, .mem (rdi.read s) (4 * (rcx.read s).toNat), .rip] := by
  simp only [repStosdA32Effect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 32 * (rcx.read s).toNat / 8 = 4 * (rcx.read s).toNat by omega]

theorem repStosdA32Effect_avoids {p : BitVec 64} {s : RamState} 
    (h : RangeApart (rdi.read s) (4 * (rcx.read s).toNat) p 3) :
    (repStosdA32Effect p s).Avoids (codeRange p [0x67, 0xF3, 0xAB]) :=
  Effect.avoids_of_mem (by rw [repStosdA32Effect_components]; simp [Component.isMem]) h rfl

theorem rep_stosd_a32_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF3, 0xAB]) s) (hpre : RepStosdA32Pre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF3, 0xAB]) t ∧ (repStosdA32Effect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0x67, 0xF3, 0xAB] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repStosdA32Effect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repStosdA32Effect_avoids hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_stosd_a32_step_zero s h.midRep [0x67, 0xF3] (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp)
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
    · refine ⟨?_, ?_, ?_⟩
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
    have hready : RepStosdA32Loop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.dstLow,
        hn ▸ hpre.dstMem, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_stosd_a32_loop hstride c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, ?_, ?_, trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_⟩
      · rw [hd.rdiAfter, hn]
      · exact hd.rcxZero
      · show memLoad (nextStates (c' + 1) s).external (rdi.read s) (32 * (rcx.read s).toNat) = _
        apply memLoad_eq_of_memByte (by omega)
        intro i hi
        rw [storedByte_replicate _ (by decide) _ i (by omega)]
        have hf := hd.fill i (by omega)
        simp only [memByte, PhysicalMemory.read]
        exact congrArg (fun o : Option UInt8 => o.getD 0) hf
    · rw [repStosdA32Effect_components, hn]
      exact hag.mono (by simp)

theorem rep_stosd_a32_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepStosdA32Pre p) (codeRange p [0x67, 0xF3, 0xAB]) (Effect.post (repStosdA32Effect p)) :=
  fun s h hcode hpre => ⟨_, rep_stosd_a32_steps hstride p s h hcode hpre⟩

theorem repStosdA32Effect_bytes {p : BitVec 64} {s s' : RamState} (h : (repStosdA32Effect p s).Holds s s')
    (i : Nat) (hi : i < 4 * (rcx.read s).toNat) :
    memByte s'.external (rdi.read s + BitVec.ofNat 64 i) =
      storedByte ((Operand.reg 0 : Operand 32).read s) (i % 4) := by
  have hw : memLoad s'.external (rdi.read s) (32 * (rcx.read s).toNat) =
      ((Operand.reg 0 : Operand 32).read s).replicate (rcx.read s).toNat := h.writes.2.2
  rw [← storedByte_memLoad (n := 32 * (rcx.read s).toNat) _ _ i (by omega), hw,
    storedByte_replicate _ (by decide) _ i (by omega)]

structure RepStoswA32Loop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF3, 0x66, 0xAB]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  dstLow : (rdi.read s).toNat + 2 * count < 2^32
  dstMem : ∀ i < 2 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart (rdi.read s).toNat (2 * count)
  dstCode : RangeApart (rdi.read s) (2 * count) s.RIP 4

theorem RepStoswA32Loop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepStoswA32Loop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepStoswA32Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {count : Nat} (h : RepStoswA32Loop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repStosAfter 16 4 s)) := by
  have := h.dstLow
  exact rep_stosw_a32_step hstride s h.ready [0x67, 0xF3, 0x66] (scanPrefix_asz_cons (by simp [scanPrefix_f3, scanPrefix_66])) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    h.df h.code h.codeLow (h.rcx_ne hpos)
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩
    (by omega) (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)

theorem RepStoswA32Loop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepStoswA32Loop s (count + 1)) : rcx.read (repStosAfter 16 4 s) = BitVec.ofNat 64 count := by
  rw [repStosAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepStoswA32Loop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepStoswA32Loop s (count + 2)) : RepStoswA32Loop (repStosAfter 16 4 s) (count + 1) := by
  have hdl := h.dstLow
  have hrip : (repStosAfter 16 4 s).RIP = s.RIP := by
    rw [repStosAfter_rip 16 4 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hd : rdi.read (repStosAfter 16 4 s) = rdi.read s + BitVec.ofNat 64 2 := repStosAfter_rdi 16 4 s
  have hdn : (rdi.read (repStosAfter 16 4 s)).toNat = (rdi.read s).toNat + 2 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repStos 16 4 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repStosAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by omega) i (by simpa using hi) he
  · rw [hrip]; exact h.codeLow
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repStosAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (2 + i) (by omega))
  · rw [hdn]; have := h.dstTables; omega
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, hrip]
    exact h.dstCode (2 + i) (by omega) j hj

structure RepStoswA32Done [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 4)
  rcxZero : rcx.read t = 0
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (2 * count)
  fill : ∀ i < 2 * count, t.external[rdi.read s + BitVec.ofNat 64 i]? =
    some (storedByte ((Operand.reg 0 : Operand 16).read s) (i % 2))
  agrees : AgreesExcept [.reg 1, .reg 7, .mem (rdi.read s) (2 * count), .rip] (clearRep s) t

theorem rep_stosw_a32_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (h : RepStoswA32Loop s (count + 1)) :
    RepStoswA32Done s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repStosAfter 16 4 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repStosAfter 16 4 s).Repeat_String_Operation = false := by
      rw [repStosAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repStos 16 4 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repStosAfter_rip 16 4 s h.ready.msr, hc]; rfl
    · rw [repStosAfter_rcx, hc]
    · exact repStosAfter_rdi 16 4 s
    · intro i hi
      rw [Nat.mod_eq_of_lt (show i < 2 by omega)]
      exact repStosAfter_fill 16 4 s (by decide) i (by omega)
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repStos 16 4 s
  | succ m ih =>
    have hnext : nextState s = (repStosAfter 16 4 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hdl := h.dstLow
    have hd : rdi.read (repStosAfter 16 4 s) = rdi.read s + BitVec.ofNat 64 2 := repStosAfter_rdi 16 4 s
    have hfirst (i : Nat) (hi : i < 2) :
        (repStosAfter 16 4 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          some (storedByte ((Operand.reg 0 : Operand 16).read s) i) :=
      repStosAfter_fill 16 4 s (by decide) i hi
    have ih' := ih (repStosAfter 16 4 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repStosAfter 16 4 s).RIP = s.RIP := by
      rw [repStosAfter_rip 16 4 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 2
      · rw [Nat.mod_eq_of_lt hsmall]
        refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst i hsmall)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [hd, add_ofNat_add_ofNat] at he
        have hn := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
        omega
      · have hc := ih'.fill (i - 2) (by omega)
        rw [hd, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega), repStosAfter_rax,
          show (i - 2) % 2 = i % 2 by omega] at hc
        exact hc
    · refine (AgreesExcept.repStos 16 4 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (2 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hd, add_ofNat_add_ofNat] at he
          exact ⟨2 + j, by omega, he⟩

structure RepStoswA32Pre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  dstLow : (rdi.read s).toNat + 2 * (rcx.read s).toNat < 2^32
  dstMem : ∀ i < 2 * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart (rdi.read s).toNat (2 * (rcx.read s).toNat)
  dstCode : RangeApart (rdi.read s) (2 * (rcx.read s).toNat) p 4

def repStoswA32Effect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 4
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (2 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (rdi.read s) : Operand (16 * (rcx.read s).toNat)),
      ((Operand.reg 0 : Operand 16).read s).replicate (rcx.read s).toNat⟩]

@[simp] theorem repStoswA32Effect_components (p : BitVec 64) (s : RamState) :
    (repStoswA32Effect p s).components =
      [.reg 7, .reg 1, .mem (rdi.read s) (2 * (rcx.read s).toNat), .rip] := by
  simp only [repStoswA32Effect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 16 * (rcx.read s).toNat / 8 = 2 * (rcx.read s).toNat by omega]

theorem repStoswA32Effect_avoids {p : BitVec 64} {s : RamState} 
    (h : RangeApart (rdi.read s) (2 * (rcx.read s).toNat) p 4) :
    (repStoswA32Effect p s).Avoids (codeRange p [0x67, 0xF3, 0x66, 0xAB]) :=
  Effect.avoids_of_mem (by rw [repStoswA32Effect_components]; simp [Component.isMem]) h rfl

theorem rep_stosw_a32_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF3, 0x66, 0xAB]) s) (hpre : RepStoswA32Pre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF3, 0x66, 0xAB]) t ∧ (repStoswA32Effect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0x67, 0xF3, 0x66, 0xAB] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repStoswA32Effect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repStoswA32Effect_avoids hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 4 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_stosw_a32_step_zero s h.midRep [0x67, 0xF3, 0x66] (scanPrefix_asz_cons (by simp [scanPrefix_f3, scanPrefix_66])) (by simp)
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
    · refine ⟨?_, ?_, ?_⟩
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
    have hready : RepStoswA32Loop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.dstLow,
        hn ▸ hpre.dstMem, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_stosw_a32_loop hstride c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, ?_, ?_, trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_⟩
      · rw [hd.rdiAfter, hn]
      · exact hd.rcxZero
      · show memLoad (nextStates (c' + 1) s).external (rdi.read s) (16 * (rcx.read s).toNat) = _
        apply memLoad_eq_of_memByte (by omega)
        intro i hi
        rw [storedByte_replicate _ (by decide) _ i (by omega)]
        have hf := hd.fill i (by omega)
        simp only [memByte, PhysicalMemory.read]
        exact congrArg (fun o : Option UInt8 => o.getD 0) hf
    · rw [repStoswA32Effect_components, hn]
      exact hag.mono (by simp)

theorem rep_stosw_a32_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepStoswA32Pre p) (codeRange p [0x67, 0xF3, 0x66, 0xAB]) (Effect.post (repStoswA32Effect p)) :=
  fun s h hcode hpre => ⟨_, rep_stosw_a32_steps hstride p s h hcode hpre⟩

theorem repStoswA32Effect_bytes {p : BitVec 64} {s s' : RamState} (h : (repStoswA32Effect p s).Holds s s')
    (i : Nat) (hi : i < 2 * (rcx.read s).toNat) :
    memByte s'.external (rdi.read s + BitVec.ofNat 64 i) =
      storedByte ((Operand.reg 0 : Operand 16).read s) (i % 2) := by
  have hw : memLoad s'.external (rdi.read s) (16 * (rcx.read s).toNat) =
      ((Operand.reg 0 : Operand 16).read s).replicate (rcx.read s).toNat := h.writes.2.2
  rw [← storedByte_memLoad (n := 16 * (rcx.read s).toNat) _ _ i (by omega), hw,
    storedByte_replicate _ (by decide) _ i (by omega)]

structure RepStosbA32Loop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF3, 0xAA]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  dstLow : (rdi.read s).toNat + 1 * count < 2^32
  dstMem : ∀ i < 1 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart (rdi.read s).toNat (1 * count)
  dstCode : RangeApart (rdi.read s) (1 * count) s.RIP 3

theorem RepStosbA32Loop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepStosbA32Loop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepStosbA32Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {count : Nat} (h : RepStosbA32Loop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repStosAfter 8 3 s)) := by
  have := h.dstLow
  exact rep_stosb_a32_step hstride s h.ready [0x67, 0xF3] (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    h.df h.code h.codeLow (h.rcx_ne hpos)
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩
    (by omega) (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)

theorem RepStosbA32Loop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepStosbA32Loop s (count + 1)) : rcx.read (repStosAfter 8 3 s) = BitVec.ofNat 64 count := by
  rw [repStosAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepStosbA32Loop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepStosbA32Loop s (count + 2)) : RepStosbA32Loop (repStosAfter 8 3 s) (count + 1) := by
  have hdl := h.dstLow
  have hrip : (repStosAfter 8 3 s).RIP = s.RIP := by
    rw [repStosAfter_rip 8 3 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hd : rdi.read (repStosAfter 8 3 s) = rdi.read s + BitVec.ofNat 64 1 := repStosAfter_rdi 8 3 s
  have hdn : (rdi.read (repStosAfter 8 3 s)).toNat = (rdi.read s).toNat + 1 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repStos 8 3 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repStosAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by omega) i (by simpa using hi) he
  · rw [hrip]; exact h.codeLow
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repStosAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (1 + i) (by omega))
  · rw [hdn]; have := h.dstTables; omega
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, hrip]
    exact h.dstCode (1 + i) (by omega) j hj

structure RepStosbA32Done [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rcxZero : rcx.read t = 0
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (1 * count)
  fill : ∀ i < 1 * count, t.external[rdi.read s + BitVec.ofNat 64 i]? =
    some (storedByte ((Operand.reg 0 : Operand 8).read s) (i % 1))
  agrees : AgreesExcept [.reg 1, .reg 7, .mem (rdi.read s) (1 * count), .rip] (clearRep s) t

theorem rep_stosb_a32_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (h : RepStosbA32Loop s (count + 1)) :
    RepStosbA32Done s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repStosAfter 8 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repStosAfter 8 3 s).Repeat_String_Operation = false := by
      rw [repStosAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repStos 8 3 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repStosAfter_rip 8 3 s h.ready.msr, hc]; rfl
    · rw [repStosAfter_rcx, hc]
    · exact repStosAfter_rdi 8 3 s
    · intro i hi
      rw [Nat.mod_eq_of_lt (show i < 1 by omega)]
      exact repStosAfter_fill 8 3 s (by decide) i (by omega)
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repStos 8 3 s
  | succ m ih =>
    have hnext : nextState s = (repStosAfter 8 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hdl := h.dstLow
    have hd : rdi.read (repStosAfter 8 3 s) = rdi.read s + BitVec.ofNat 64 1 := repStosAfter_rdi 8 3 s
    have hfirst (i : Nat) (hi : i < 1) :
        (repStosAfter 8 3 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          some (storedByte ((Operand.reg 0 : Operand 8).read s) i) :=
      repStosAfter_fill 8 3 s (by decide) i hi
    have ih' := ih (repStosAfter 8 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repStosAfter 8 3 s).RIP = s.RIP := by
      rw [repStosAfter_rip 8 3 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 1
      · rw [Nat.mod_eq_of_lt hsmall]
        refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst i hsmall)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [hd, add_ofNat_add_ofNat] at he
        have hn := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
        omega
      · have hc := ih'.fill (i - 1) (by omega)
        rw [hd, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega), repStosAfter_rax,
          show (i - 1) % 1 = i % 1 by omega] at hc
        exact hc
    · refine (AgreesExcept.repStos 8 3 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (1 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hd, add_ofNat_add_ofNat] at he
          exact ⟨1 + j, by omega, he⟩

structure RepStosbA32Pre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  dstLow : (rdi.read s).toNat + 1 * (rcx.read s).toNat < 2^32
  dstMem : ∀ i < 1 * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart (rdi.read s).toNat (1 * (rcx.read s).toNat)
  dstCode : RangeApart (rdi.read s) (1 * (rcx.read s).toNat) p 3

def repStosbA32Effect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (1 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (rdi.read s) : Operand (8 * (rcx.read s).toNat)),
      ((Operand.reg 0 : Operand 8).read s).replicate (rcx.read s).toNat⟩]

@[simp] theorem repStosbA32Effect_components (p : BitVec 64) (s : RamState) :
    (repStosbA32Effect p s).components =
      [.reg 7, .reg 1, .mem (rdi.read s) (1 * (rcx.read s).toNat), .rip] := by
  simp only [repStosbA32Effect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 8 * (rcx.read s).toNat / 8 = 1 * (rcx.read s).toNat by omega]

theorem repStosbA32Effect_avoids {p : BitVec 64} {s : RamState} 
    (h : RangeApart (rdi.read s) (1 * (rcx.read s).toNat) p 3) :
    (repStosbA32Effect p s).Avoids (codeRange p [0x67, 0xF3, 0xAA]) :=
  Effect.avoids_of_mem (by rw [repStosbA32Effect_components]; simp [Component.isMem]) h rfl

theorem rep_stosb_a32_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF3, 0xAA]) s) (hpre : RepStosbA32Pre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF3, 0xAA]) t ∧ (repStosbA32Effect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0x67, 0xF3, 0xAA] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repStosbA32Effect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repStosbA32Effect_avoids hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_stosb_a32_step_zero s h.midRep [0x67, 0xF3] (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp)
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
    · refine ⟨?_, ?_, ?_⟩
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
    have hready : RepStosbA32Loop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.dstLow,
        hn ▸ hpre.dstMem, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_stosb_a32_loop hstride c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, ?_, ?_, trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_⟩
      · rw [hd.rdiAfter, hn]
      · exact hd.rcxZero
      · show memLoad (nextStates (c' + 1) s).external (rdi.read s) (8 * (rcx.read s).toNat) = _
        apply memLoad_eq_of_memByte (by omega)
        intro i hi
        rw [storedByte_replicate _ (by decide) _ i (by omega)]
        have hf := hd.fill i (by omega)
        simp only [memByte, PhysicalMemory.read]
        exact congrArg (fun o : Option UInt8 => o.getD 0) hf
    · rw [repStosbA32Effect_components, hn]
      exact hag.mono (by simp)

theorem rep_stosb_a32_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepStosbA32Pre p) (codeRange p [0x67, 0xF3, 0xAA]) (Effect.post (repStosbA32Effect p)) :=
  fun s h hcode hpre => ⟨_, rep_stosb_a32_steps hstride p s h hcode hpre⟩

theorem repStosbA32Effect_bytes {p : BitVec 64} {s s' : RamState} (h : (repStosbA32Effect p s).Holds s s')
    (i : Nat) (hi : i < 1 * (rcx.read s).toNat) :
    memByte s'.external (rdi.read s + BitVec.ofNat 64 i) =
      storedByte ((Operand.reg 0 : Operand 8).read s) (i % 1) := by
  have hw : memLoad s'.external (rdi.read s) (8 * (rcx.read s).toNat) =
      ((Operand.reg 0 : Operand 8).read s).replicate (rcx.read s).toNat := h.writes.2.2
  rw [← storedByte_memLoad (n := 8 * (rcx.read s).toNat) _ _ i (by omega), hw,
    storedByte_replicate _ (by decide) _ i (by omega)]

attribute [x86_compose] repStosqEffect repStosdEffect repStoswEffect repStosbEffect repStosqA32Effect repStosdA32Effect repStoswA32Effect repStosbA32Effect

@[x86_local] theorem repStosqEffect_local {p : BitVec 64} : Effect.Local (repStosqEffect p) := by
  rep_effect_local [repStosqEffect]

@[x86_local] theorem repStosdEffect_local {p : BitVec 64} : Effect.Local (repStosdEffect p) := by
  rep_effect_local [repStosdEffect]

@[x86_local] theorem repStoswEffect_local {p : BitVec 64} : Effect.Local (repStoswEffect p) := by
  rep_effect_local [repStoswEffect]

@[x86_local] theorem repStosbEffect_local {p : BitVec 64} : Effect.Local (repStosbEffect p) := by
  rep_effect_local [repStosbEffect]

@[x86_local] theorem repStosqA32Effect_local {p : BitVec 64} : Effect.Local (repStosqA32Effect p) := by
  rep_effect_local [repStosqA32Effect]

@[x86_local] theorem repStosdA32Effect_local {p : BitVec 64} : Effect.Local (repStosdA32Effect p) := by
  rep_effect_local [repStosdA32Effect]

@[x86_local] theorem repStoswA32Effect_local {p : BitVec 64} : Effect.Local (repStoswA32Effect p) := by
  rep_effect_local [repStoswA32Effect]

@[x86_local] theorem repStosbA32Effect_local {p : BitVec 64} : Effect.Local (repStosbA32Effect p) := by
  rep_effect_local [repStosbA32Effect]

end X86Proofs
