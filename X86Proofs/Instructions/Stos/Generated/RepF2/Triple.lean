
import X86Proofs.Instructions.Stos.Generated.RepF2.Step
import X86Proofs.Instructions.Stos.Generated.Rep.Triple
import X86Proofs.Program.Effect

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

structure RepStosqF2Loop [Bindings] (rex : UInt8) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF2, rex, 0xAB]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  dstLow : (rdi.read s).toNat + 8 * count ≤ 2^32
  dstMem : ∀ i < 8 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart (rdi.read s).toNat (8 * count)
  dstCode : RangeApart (rdi.read s) (8 * count) s.RIP 3

theorem RepStosqF2Loop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepStosqF2Loop rex s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepStosqF2Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState}
    {count : Nat} (h : RepStosqF2Loop rex s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repStosAfter 64 3 s)) := by
  have hr := hrex.rexPrefix
  have := h.dstLow
  exact rep_stosq_f2_step hstride s h.ready [0xF2, rex] (by simp [scanPrefix_f2, hr.scanPrefix]) (by simp)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    h.df h.code h.codeLow (h.rcx_ne hpos)
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩

theorem RepStosqF2Loop.rcx_after [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepStosqF2Loop rex s (count + 1)) : rcx.read (repStosAfter 64 3 s) = BitVec.ofNat 64 count := by
  rw [repStosAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepStosqF2Loop.next [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepStosqF2Loop rex s (count + 2)) : RepStosqF2Loop rex (repStosAfter 64 3 s) (count + 1) := by
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

theorem rep_stosq_f2_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (count : Nat)
    (s : RamState) (h : RepStosqF2Loop rex s (count + 1)) :
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

theorem repStosqEffect_avoids_f2 {p : BitVec 64} {s : RamState} (rex : UInt8) 
    (h : RangeApart (rdi.read s) (8 * (rcx.read s).toNat) p 3) :
    (repStosqEffect p s).Avoids (codeRange p [0xF2, rex, 0xAB]) :=
  Effect.avoids_of_mem (by rw [repStosqEffect_components]; simp [Component.isMem]) h rfl

theorem rep_stosq_f2_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, rex, 0xAB]) s) (hpre : RepStosqPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, rex, 0xAB]) t ∧ (repStosqEffect p s).Holds s t := by
  intro t
  have hr := hrex.rexPrefix
  have hcodeS : BytesAt s s.RIP [0xF2, rex, 0xAB] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repStosqEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repStosqEffect_avoids_f2 rex hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_stosq_f2_step_zero s h.midRep [0xF2, rex] (by simp [scanPrefix_f2, hr.scanPrefix]) (by simp)
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
    have hready : RepStosqF2Loop rex s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.dstLow,
        hn ▸ hpre.dstMem, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_stosq_f2_loop hstride hrex c' s hready
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

theorem rep_stosq_f2_triple_of_bytes [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepStosqPre p) (codeRange p [0xF2, rex, 0xAB]) (Effect.post (repStosqEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_stosq_f2_steps hstride p rex hrex s h hcode hpre⟩

theorem rep_stosq_f2_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) :
    Triple (RepStosqPre p) (codeRange p [0xF2, 0x48, 0xAB]) (Effect.post (repStosqEffect p)) :=
  rep_stosq_f2_triple_of_bytes hstride p 0x48 (by unfold RexWPrefix; decide)

structure RepStosdF2Loop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF2, 0xAB]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  dstLow : (rdi.read s).toNat + 4 * count ≤ 2^32
  dstMem : ∀ i < 4 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart (rdi.read s).toNat (4 * count)
  dstCode : RangeApart (rdi.read s) (4 * count) s.RIP 2

theorem RepStosdF2Loop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepStosdF2Loop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepStosdF2Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {count : Nat} (h : RepStosdF2Loop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repStosAfter 32 2 s)) := by
  have := h.dstLow
  exact rep_stosd_f2_step hstride s h.ready [0xF2] (by simpa using scanPrefix_f2) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne hpos)
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩

theorem RepStosdF2Loop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepStosdF2Loop s (count + 1)) : rcx.read (repStosAfter 32 2 s) = BitVec.ofNat 64 count := by
  rw [repStosAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepStosdF2Loop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepStosdF2Loop s (count + 2)) : RepStosdF2Loop (repStosAfter 32 2 s) (count + 1) := by
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

theorem rep_stosd_f2_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (h : RepStosdF2Loop s (count + 1)) :
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

theorem repStosdEffect_avoids_f2 {p : BitVec 64} {s : RamState} 
    (h : RangeApart (rdi.read s) (4 * (rcx.read s).toNat) p 2) :
    (repStosdEffect p s).Avoids (codeRange p [0xF2, 0xAB]) :=
  Effect.avoids_of_mem (by rw [repStosdEffect_components]; simp [Component.isMem]) h rfl

theorem rep_stosd_f2_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, 0xAB]) s) (hpre : RepStosdPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, 0xAB]) t ∧ (repStosdEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF2, 0xAB] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repStosdEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repStosdEffect_avoids_f2 hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 2 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_stosd_f2_step_zero s h.midRep [0xF2] (by simpa using scanPrefix_f2) (by simp)
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
    have hready : RepStosdF2Loop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.dstLow,
        hn ▸ hpre.dstMem, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_stosd_f2_loop hstride c' s hready
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

theorem rep_stosd_f2_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepStosdPre p) (codeRange p [0xF2, 0xAB]) (Effect.post (repStosdEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_stosd_f2_steps hstride p s h hcode hpre⟩

structure RepStoswF2Loop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF2, 0x66, 0xAB]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  dstLow : (rdi.read s).toNat + 2 * count ≤ 2^32
  dstMem : ∀ i < 2 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart (rdi.read s).toNat (2 * count)
  dstCode : RangeApart (rdi.read s) (2 * count) s.RIP 3

theorem RepStoswF2Loop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepStoswF2Loop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepStoswF2Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {count : Nat} (h : RepStoswF2Loop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repStosAfter 16 3 s)) := by
  have := h.dstLow
  exact rep_stosw_f2_step hstride s h.ready [0xF2, 0x66] (by simp [scanPrefix_f2, scanPrefix_66]) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne hpos)
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩

theorem RepStoswF2Loop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepStoswF2Loop s (count + 1)) : rcx.read (repStosAfter 16 3 s) = BitVec.ofNat 64 count := by
  rw [repStosAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepStoswF2Loop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepStoswF2Loop s (count + 2)) : RepStoswF2Loop (repStosAfter 16 3 s) (count + 1) := by
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

theorem rep_stosw_f2_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (h : RepStoswF2Loop s (count + 1)) :
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

theorem repStoswEffect_avoids_f2 {p : BitVec 64} {s : RamState} 
    (h : RangeApart (rdi.read s) (2 * (rcx.read s).toNat) p 3) :
    (repStoswEffect p s).Avoids (codeRange p [0xF2, 0x66, 0xAB]) :=
  Effect.avoids_of_mem (by rw [repStoswEffect_components]; simp [Component.isMem]) h rfl

theorem rep_stosw_f2_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, 0x66, 0xAB]) s) (hpre : RepStoswPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, 0x66, 0xAB]) t ∧ (repStoswEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF2, 0x66, 0xAB] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repStoswEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repStoswEffect_avoids_f2 hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_stosw_f2_step_zero s h.midRep [0xF2, 0x66] (by simp [scanPrefix_f2, scanPrefix_66]) (by simp)
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
    have hready : RepStoswF2Loop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.dstLow,
        hn ▸ hpre.dstMem, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_stosw_f2_loop hstride c' s hready
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

theorem rep_stosw_f2_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepStoswPre p) (codeRange p [0xF2, 0x66, 0xAB]) (Effect.post (repStoswEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_stosw_f2_steps hstride p s h hcode hpre⟩

structure RepStosbF2Loop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF2, 0xAA]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  dstLow : (rdi.read s).toNat + 1 * count ≤ 2^32
  dstMem : ∀ i < 1 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart (rdi.read s).toNat (1 * count)
  dstCode : RangeApart (rdi.read s) (1 * count) s.RIP 2

theorem RepStosbF2Loop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepStosbF2Loop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepStosbF2Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {count : Nat} (h : RepStosbF2Loop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repStosAfter 8 2 s)) := by
  have := h.dstLow
  exact rep_stosb_f2_step hstride s h.ready [0xF2] (by simpa using scanPrefix_f2) (by simp)
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne hpos)
    ⟨by omega, fun i hi => h.dstMem i (by omega), by have := h.dstTables; omega⟩

theorem RepStosbF2Loop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepStosbF2Loop s (count + 1)) : rcx.read (repStosAfter 8 2 s) = BitVec.ofNat 64 count := by
  rw [repStosAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepStosbF2Loop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepStosbF2Loop s (count + 2)) : RepStosbF2Loop (repStosAfter 8 2 s) (count + 1) := by
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

theorem rep_stosb_f2_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (h : RepStosbF2Loop s (count + 1)) :
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

theorem repStosbEffect_avoids_f2 {p : BitVec 64} {s : RamState} 
    (h : RangeApart (rdi.read s) (1 * (rcx.read s).toNat) p 2) :
    (repStosbEffect p s).Avoids (codeRange p [0xF2, 0xAA]) :=
  Effect.avoids_of_mem (by rw [repStosbEffect_components]; simp [Component.isMem]) h rfl

theorem rep_stosb_f2_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, 0xAA]) s) (hpre : RepStosbPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, 0xAA]) t ∧ (repStosbEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF2, 0xAA] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repStosbEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repStosbEffect_avoids_f2 hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 2 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_stosb_f2_step_zero s h.midRep [0xF2] (by simpa using scanPrefix_f2) (by simp)
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
    have hready : RepStosbF2Loop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.dstLow,
        hn ▸ hpre.dstMem, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_stosb_f2_loop hstride c' s hready
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

theorem rep_stosb_f2_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepStosbPre p) (codeRange p [0xF2, 0xAA]) (Effect.post (repStosbEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_stosb_f2_steps hstride p s h hcode hpre⟩

end X86Proofs
