
import X86Proofs.Instructions.Stos.Generated.RepDown.Step
import X86Proofs.Program.Effect

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

structure RepStosqDownLoop [Bindings] (rex : UInt8) (s : RamState) (lo : Nat) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF3, rex, 0xAB]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  dstTop : (rdi.read s).toNat + 8 = lo + 8 * count
  dstLow : lo + 8 * count ≤ 2^32
  dstMem : ∀ i < 8 * count, (s.external[BitVec.ofNat 64 lo + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart lo (8 * count)
  dstCode : RangeApart (BitVec.ofNat 64 lo) (8 * count) s.RIP 3

theorem RepStosqDownLoop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {lo : Nat} {count : Nat}
    (h : RepStosqDownLoop rex s lo count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepStosqDownLoop.top [Bindings] {rex : UInt8} {s : RamState} {lo : Nat} {count : Nat}
    (h : RepStosqDownLoop rex s lo (count + 1)) (i : Nat) :
    BitVec.ofNat 64 lo + BitVec.ofNat 64 (8 * count + i) = rdi.read s + BitVec.ofNat 64 i :=
  ofNat_add_ofNat_eq (by have := h.dstTop; omega) i

theorem RepStosqDownLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState}
    {lo : Nat} {count : Nat} (h : RepStosqDownLoop rex s lo (count + 1)) :
    X86.Machine.step s = some (.next (repStosDownAfter 64 3 s)) := by
  have hr := hrex.rexPrefix
  have := h.dstLow
  have := h.dstTop
  exact rep_stosq_down_step hstride s h.ready [0xF3, rex] (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    h.df h.code h.codeLow (h.rcx_ne (by omega))
    ⟨by omega, fun i hi => h.top i ▸ h.dstMem (8 * count + i) (by omega),
      by have := h.dstTables; omega⟩

theorem RepStosqDownLoop.next [Bindings] {rex : UInt8} {s : RamState} {lo : Nat} {count : Nat}
    (h : RepStosqDownLoop rex s lo (count + 2)) : RepStosqDownLoop rex (repStosDownAfter 64 3 s) lo (count + 1) := by
  have hdl := h.dstLow
  have htop := h.dstTop
  have hrip : (repStosDownAfter 64 3 s).RIP = s.RIP := by
    rw [repStosDownAfter_rip 64 3 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hdn : (rdi.read (repStosDownAfter 64 3 s)).toNat = (rdi.read s).toNat - 8 := by
    rw [repStosDownAfter_rdi, toNat_sub_ofNat _ _ (by omega)]
  refine ⟨h.ready.repStosDown 64 3 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    by rw [repStosDownAfter_rcx, h.counter, ofNat_succ_sub_one], ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repStosDownAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode (8 * (count + 1) + j) (by omega) i (by simpa using hi)
        (by rw [h.top j]; exact he)
  · rw [hrip]; exact h.codeLow
  · rw [hdn]; omega
  · omega
  · intro i hi
    rw [repStosDownAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem i (by omega))
  · have := h.dstTables; omega
  · intro i hi j hj
    rw [hrip]
    exact h.dstCode i (by omega) j hj

structure RepStosqDownDone [Bindings] (s t : RamState) (lo : Nat) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rcxZero : rcx.read t = 0
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (8 * count)
  fill : ∀ i < 8 * count, t.external[BitVec.ofNat 64 lo + BitVec.ofNat 64 i]? =
    some (storedByte ((Operand.reg 0 : Operand 64).read s) (i % 8))
  agrees : AgreesExcept [.reg 1, .reg 7, .mem (BitVec.ofNat 64 lo) (8 * count), .rip] (clearRep s) t

theorem rep_stosq_down_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (count : Nat)
    (s : RamState) (lo : Nat) (h : RepStosqDownLoop rex s lo (count + 1)) :
    RepStosqDownDone s (nextStates (count + 1) s) lo (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repStosDownAfter 64 3 s) :=
      nextState_of_step (h.step hstride hrex )
    have hdl := h.dstLow
    have htop := h.dstTop
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repStosDownAfter 64 3 s).Repeat_String_Operation = false := by
      rw [repStosDownAfter_repeat, hc]; rfl
    have hlo : rdi.read s = BitVec.ofNat 64 lo := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repStosDown 64 3 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repStosDownAfter_rip 64 3 s h.ready.msr, hc]; rfl
    · rw [repStosDownAfter_rcx, hc]
    · exact repStosDownAfter_rdi 64 3 s
    · intro i hi
      rw [Nat.mod_eq_of_lt (show i < 8 by omega), ← hlo]
      exact repStosDownAfter_fill 64 3 s (by decide) i (by omega)
    · rw [← clearRep_eq hflag, ← hlo]
      exact AgreesExcept.repStosDown 64 3 s
  | succ m ih =>
    have hnext : nextState s = (repStosDownAfter 64 3 s) :=
      nextState_of_step (h.step hstride hrex )
    have hdl := h.dstLow
    have htop := h.dstTop
    have hfirst (i : Nat) (hi : i < 8) :
        (repStosDownAfter 64 3 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          some (storedByte ((Operand.reg 0 : Operand 64).read s) i) :=
      repStosDownAfter_fill 64 3 s (by decide) i hi
    have ih' := ih (repStosDownAfter 64 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repStosDownAfter 64 3 s).RIP = s.RIP := by
      rw [repStosDownAfter_rip 64 3 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, repStosDownAfter_rdi, sub_ofNat_sub_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 8 * (m + 1)
      · have hc := ih'.fill i hsmall
        rw [repStosDownAfter_rax] at hc
        exact hc
      · obtain ⟨j, rfl⟩ : ∃ j, i = 8 * (m + 1) + j := ⟨i - 8 * (m + 1), by omega⟩
        rw [show (8 * (m + 1) + j) % 8 = j by omega, h.top j]
        refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst j (by omega))
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j', hj', he⟩ := hcov
        rw [← h.top j] at he
        have hn := congrArg BitVec.toNat he
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hn
        omega
    · refine (AgreesExcept.repStosDown 64 3 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (BitVec.ofNat 64 lo) (8 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨8 * (m + 1) + j, by omega, by rw [h.top j]; exact he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩

structure RepStosqDownPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  dstBase : 8 * (rcx.read s).toNat ≤ (rdi.read s).toNat + 8
  dstLow : (rdi.read s).toNat + 8 ≤ 2^32
  dstMem : ∀ i < 8 * (rcx.read s).toNat,
    (s.external[downBase rdi 8 s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart ((rdi.read s).toNat + 8 - 8 * (rcx.read s).toNat)
    (8 * (rcx.read s).toNat)
  dstCode : RangeApart (downBase rdi 8 s) (8 * (rcx.read s).toNat) p 3

def repStosqDownEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rdi, rdi.read s - BitVec.ofNat 64 (8 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (downBase rdi 8 s) : Operand (64 * (rcx.read s).toNat)),
      ((Operand.reg 0 : Operand 64).read s).replicate (rcx.read s).toNat⟩]

@[simp] theorem repStosqDownEffect_components (p : BitVec 64) (s : RamState) :
    (repStosqDownEffect p s).components =
      [.reg 7, .reg 1, .mem (downBase rdi 8 s) (8 * (rcx.read s).toNat), .rip] := by
  simp only [repStosqDownEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 64 * (rcx.read s).toNat / 8 = 8 * (rcx.read s).toNat by omega]

theorem repStosqDownEffect_avoids {p : BitVec 64} {s : RamState} (rex : UInt8) 
    (h : RangeApart (downBase rdi 8 s) (8 * (rcx.read s).toNat) p 3) :
    (repStosqDownEffect p s).Avoids (codeRange p [0xF3, rex, 0xAB]) :=
  Effect.avoids_of_mem (by rw [repStosqDownEffect_components]; simp [Component.isMem]) h rfl

theorem rep_stosq_down_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, rex, 0xAB]) s) (hpre : RepStosqDownPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, rex, 0xAB]) t ∧ (repStosqDownEffect p s).Holds s t := by
  intro t
  have hr := hrex.rexPrefix
  have hcodeS : BytesAt s s.RIP [0xF3, rex, 0xAB] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repStosqDownEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repStosqDownEffect_avoids rex hpre.dstCode) hcode, hh.2⟩
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
    have hb : downBase rdi 8 s =
        BitVec.ofNat 64 ((rdi.read s).toNat + 8 - 8 * (c' + 1)) := by
      rw [downBase, hn]
    have hready : RepStosqDownLoop rex s ((rdi.read s).toNat + 8 - 8 * (c' + 1)) (c' + 1) := by
      have := hpre.dstBase
      have := hpre.dstLow
      refine ⟨h.midRep, hpre.df, hcodeS, hlow, hc, by omega, by omega,
        fun i hi => hb ▸ hpre.dstMem i (by omega), by have := hpre.dstTables; omega,
        hpre.rip ▸ hb ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_stosq_down_loop hstride hrex c' s _ hready
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
      · show memLoad (nextStates (c' + 1) s).external (downBase rdi 8 s)
          (64 * (rcx.read s).toNat) = _
        apply memLoad_eq_of_memByte (by omega)
        intro i hi
        rw [storedByte_replicate _ (by decide) _ i (by omega), hb]
        have hf := hd.fill i (by omega)
        simp only [memByte, PhysicalMemory.read]
        exact congrArg (fun o : Option UInt8 => o.getD 0) hf
    · rw [repStosqDownEffect_components, hn, hb]
      exact hag.mono (by simp)

theorem rep_stosq_down_triple_of_bytes [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepStosqDownPre p) (codeRange p [0xF3, rex, 0xAB]) (Effect.post (repStosqDownEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_stosq_down_steps hstride p rex hrex s h hcode hpre⟩

theorem rep_stosq_down_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) :
    Triple (RepStosqDownPre p) (codeRange p [0xF3, 0x48, 0xAB]) (Effect.post (repStosqDownEffect p)) :=
  rep_stosq_down_triple_of_bytes hstride p 0x48 (by unfold RexWPrefix; decide)

structure RepStosdDownLoop [Bindings] (s : RamState) (lo : Nat) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0xAB]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  dstTop : (rdi.read s).toNat + 4 = lo + 4 * count
  dstLow : lo + 4 * count ≤ 2^32
  dstMem : ∀ i < 4 * count, (s.external[BitVec.ofNat 64 lo + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart lo (4 * count)
  dstCode : RangeApart (BitVec.ofNat 64 lo) (4 * count) s.RIP 2

theorem RepStosdDownLoop.rcx_ne [Bindings] {s : RamState} {lo : Nat} {count : Nat}
    (h : RepStosdDownLoop s lo count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepStosdDownLoop.top [Bindings] {s : RamState} {lo : Nat} {count : Nat}
    (h : RepStosdDownLoop s lo (count + 1)) (i : Nat) :
    BitVec.ofNat 64 lo + BitVec.ofNat 64 (4 * count + i) = rdi.read s + BitVec.ofNat 64 i :=
  ofNat_add_ofNat_eq (by have := h.dstTop; omega) i

theorem RepStosdDownLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {lo : Nat} {count : Nat} (h : RepStosdDownLoop s lo (count + 1)) :
    X86.Machine.step s = some (.next (repStosDownAfter 32 2 s)) := by
  have := h.dstLow
  have := h.dstTop
  exact rep_stosd_down_step hstride s h.ready [0xF3] (by simpa using scanPrefix_f3) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne (by omega))
    ⟨by omega, fun i hi => h.top i ▸ h.dstMem (4 * count + i) (by omega),
      by have := h.dstTables; omega⟩

theorem RepStosdDownLoop.next [Bindings] {s : RamState} {lo : Nat} {count : Nat}
    (h : RepStosdDownLoop s lo (count + 2)) : RepStosdDownLoop (repStosDownAfter 32 2 s) lo (count + 1) := by
  have hdl := h.dstLow
  have htop := h.dstTop
  have hrip : (repStosDownAfter 32 2 s).RIP = s.RIP := by
    rw [repStosDownAfter_rip 32 2 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hdn : (rdi.read (repStosDownAfter 32 2 s)).toNat = (rdi.read s).toNat - 4 := by
    rw [repStosDownAfter_rdi, toNat_sub_ofNat _ _ (by omega)]
  refine ⟨h.ready.repStosDown 32 2 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    by rw [repStosDownAfter_rcx, h.counter, ofNat_succ_sub_one], ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repStosDownAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode (4 * (count + 1) + j) (by omega) i (by simpa using hi)
        (by rw [h.top j]; exact he)
  · rw [hrip]; exact h.codeLow
  · rw [hdn]; omega
  · omega
  · intro i hi
    rw [repStosDownAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem i (by omega))
  · have := h.dstTables; omega
  · intro i hi j hj
    rw [hrip]
    exact h.dstCode i (by omega) j hj

structure RepStosdDownDone [Bindings] (s t : RamState) (lo : Nat) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rcxZero : rcx.read t = 0
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (4 * count)
  fill : ∀ i < 4 * count, t.external[BitVec.ofNat 64 lo + BitVec.ofNat 64 i]? =
    some (storedByte ((Operand.reg 0 : Operand 32).read s) (i % 4))
  agrees : AgreesExcept [.reg 1, .reg 7, .mem (BitVec.ofNat 64 lo) (4 * count), .rip] (clearRep s) t

theorem rep_stosd_down_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (lo : Nat) (h : RepStosdDownLoop s lo (count + 1)) :
    RepStosdDownDone s (nextStates (count + 1) s) lo (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repStosDownAfter 32 2 s) :=
      nextState_of_step (h.step hstride )
    have hdl := h.dstLow
    have htop := h.dstTop
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repStosDownAfter 32 2 s).Repeat_String_Operation = false := by
      rw [repStosDownAfter_repeat, hc]; rfl
    have hlo : rdi.read s = BitVec.ofNat 64 lo := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repStosDown 32 2 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repStosDownAfter_rip 32 2 s h.ready.msr, hc]; rfl
    · rw [repStosDownAfter_rcx, hc]
    · exact repStosDownAfter_rdi 32 2 s
    · intro i hi
      rw [Nat.mod_eq_of_lt (show i < 4 by omega), ← hlo]
      exact repStosDownAfter_fill 32 2 s (by decide) i (by omega)
    · rw [← clearRep_eq hflag, ← hlo]
      exact AgreesExcept.repStosDown 32 2 s
  | succ m ih =>
    have hnext : nextState s = (repStosDownAfter 32 2 s) :=
      nextState_of_step (h.step hstride )
    have hdl := h.dstLow
    have htop := h.dstTop
    have hfirst (i : Nat) (hi : i < 4) :
        (repStosDownAfter 32 2 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          some (storedByte ((Operand.reg 0 : Operand 32).read s) i) :=
      repStosDownAfter_fill 32 2 s (by decide) i hi
    have ih' := ih (repStosDownAfter 32 2 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repStosDownAfter 32 2 s).RIP = s.RIP := by
      rw [repStosDownAfter_rip 32 2 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, repStosDownAfter_rdi, sub_ofNat_sub_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 4 * (m + 1)
      · have hc := ih'.fill i hsmall
        rw [repStosDownAfter_rax] at hc
        exact hc
      · obtain ⟨j, rfl⟩ : ∃ j, i = 4 * (m + 1) + j := ⟨i - 4 * (m + 1), by omega⟩
        rw [show (4 * (m + 1) + j) % 4 = j by omega, h.top j]
        refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst j (by omega))
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j', hj', he⟩ := hcov
        rw [← h.top j] at he
        have hn := congrArg BitVec.toNat he
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hn
        omega
    · refine (AgreesExcept.repStosDown 32 2 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (BitVec.ofNat 64 lo) (4 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨4 * (m + 1) + j, by omega, by rw [h.top j]; exact he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩

structure RepStosdDownPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  dstBase : 4 * (rcx.read s).toNat ≤ (rdi.read s).toNat + 4
  dstLow : (rdi.read s).toNat + 4 ≤ 2^32
  dstMem : ∀ i < 4 * (rcx.read s).toNat,
    (s.external[downBase rdi 4 s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart ((rdi.read s).toNat + 4 - 4 * (rcx.read s).toNat)
    (4 * (rcx.read s).toNat)
  dstCode : RangeApart (downBase rdi 4 s) (4 * (rcx.read s).toNat) p 2

def repStosdDownEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rdi, rdi.read s - BitVec.ofNat 64 (4 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (downBase rdi 4 s) : Operand (32 * (rcx.read s).toNat)),
      ((Operand.reg 0 : Operand 32).read s).replicate (rcx.read s).toNat⟩]

@[simp] theorem repStosdDownEffect_components (p : BitVec 64) (s : RamState) :
    (repStosdDownEffect p s).components =
      [.reg 7, .reg 1, .mem (downBase rdi 4 s) (4 * (rcx.read s).toNat), .rip] := by
  simp only [repStosdDownEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 32 * (rcx.read s).toNat / 8 = 4 * (rcx.read s).toNat by omega]

theorem repStosdDownEffect_avoids {p : BitVec 64} {s : RamState} 
    (h : RangeApart (downBase rdi 4 s) (4 * (rcx.read s).toNat) p 2) :
    (repStosdDownEffect p s).Avoids (codeRange p [0xF3, 0xAB]) :=
  Effect.avoids_of_mem (by rw [repStosdDownEffect_components]; simp [Component.isMem]) h rfl

theorem rep_stosd_down_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0xAB]) s) (hpre : RepStosdDownPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0xAB]) t ∧ (repStosdDownEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF3, 0xAB] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repStosdDownEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repStosdDownEffect_avoids hpre.dstCode) hcode, hh.2⟩
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
    have hb : downBase rdi 4 s =
        BitVec.ofNat 64 ((rdi.read s).toNat + 4 - 4 * (c' + 1)) := by
      rw [downBase, hn]
    have hready : RepStosdDownLoop s ((rdi.read s).toNat + 4 - 4 * (c' + 1)) (c' + 1) := by
      have := hpre.dstBase
      have := hpre.dstLow
      refine ⟨h.midRep, hpre.df, hcodeS, hlow, hc, by omega, by omega,
        fun i hi => hb ▸ hpre.dstMem i (by omega), by have := hpre.dstTables; omega,
        hpre.rip ▸ hb ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_stosd_down_loop hstride c' s _ hready
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
      · show memLoad (nextStates (c' + 1) s).external (downBase rdi 4 s)
          (32 * (rcx.read s).toNat) = _
        apply memLoad_eq_of_memByte (by omega)
        intro i hi
        rw [storedByte_replicate _ (by decide) _ i (by omega), hb]
        have hf := hd.fill i (by omega)
        simp only [memByte, PhysicalMemory.read]
        exact congrArg (fun o : Option UInt8 => o.getD 0) hf
    · rw [repStosdDownEffect_components, hn, hb]
      exact hag.mono (by simp)

theorem rep_stosd_down_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepStosdDownPre p) (codeRange p [0xF3, 0xAB]) (Effect.post (repStosdDownEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_stosd_down_steps hstride p s h hcode hpre⟩

structure RepStoswDownLoop [Bindings] (s : RamState) (lo : Nat) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0x66, 0xAB]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  dstTop : (rdi.read s).toNat + 2 = lo + 2 * count
  dstLow : lo + 2 * count ≤ 2^32
  dstMem : ∀ i < 2 * count, (s.external[BitVec.ofNat 64 lo + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart lo (2 * count)
  dstCode : RangeApart (BitVec.ofNat 64 lo) (2 * count) s.RIP 3

theorem RepStoswDownLoop.rcx_ne [Bindings] {s : RamState} {lo : Nat} {count : Nat}
    (h : RepStoswDownLoop s lo count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepStoswDownLoop.top [Bindings] {s : RamState} {lo : Nat} {count : Nat}
    (h : RepStoswDownLoop s lo (count + 1)) (i : Nat) :
    BitVec.ofNat 64 lo + BitVec.ofNat 64 (2 * count + i) = rdi.read s + BitVec.ofNat 64 i :=
  ofNat_add_ofNat_eq (by have := h.dstTop; omega) i

theorem RepStoswDownLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {lo : Nat} {count : Nat} (h : RepStoswDownLoop s lo (count + 1)) :
    X86.Machine.step s = some (.next (repStosDownAfter 16 3 s)) := by
  have := h.dstLow
  have := h.dstTop
  exact rep_stosw_down_step hstride s h.ready [0xF3, 0x66] (by simp [scanPrefix_f3, scanPrefix_66]) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne (by omega))
    ⟨by omega, fun i hi => h.top i ▸ h.dstMem (2 * count + i) (by omega),
      by have := h.dstTables; omega⟩

theorem RepStoswDownLoop.next [Bindings] {s : RamState} {lo : Nat} {count : Nat}
    (h : RepStoswDownLoop s lo (count + 2)) : RepStoswDownLoop (repStosDownAfter 16 3 s) lo (count + 1) := by
  have hdl := h.dstLow
  have htop := h.dstTop
  have hrip : (repStosDownAfter 16 3 s).RIP = s.RIP := by
    rw [repStosDownAfter_rip 16 3 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hdn : (rdi.read (repStosDownAfter 16 3 s)).toNat = (rdi.read s).toNat - 2 := by
    rw [repStosDownAfter_rdi, toNat_sub_ofNat _ _ (by omega)]
  refine ⟨h.ready.repStosDown 16 3 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    by rw [repStosDownAfter_rcx, h.counter, ofNat_succ_sub_one], ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repStosDownAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode (2 * (count + 1) + j) (by omega) i (by simpa using hi)
        (by rw [h.top j]; exact he)
  · rw [hrip]; exact h.codeLow
  · rw [hdn]; omega
  · omega
  · intro i hi
    rw [repStosDownAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem i (by omega))
  · have := h.dstTables; omega
  · intro i hi j hj
    rw [hrip]
    exact h.dstCode i (by omega) j hj

structure RepStoswDownDone [Bindings] (s t : RamState) (lo : Nat) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rcxZero : rcx.read t = 0
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (2 * count)
  fill : ∀ i < 2 * count, t.external[BitVec.ofNat 64 lo + BitVec.ofNat 64 i]? =
    some (storedByte ((Operand.reg 0 : Operand 16).read s) (i % 2))
  agrees : AgreesExcept [.reg 1, .reg 7, .mem (BitVec.ofNat 64 lo) (2 * count), .rip] (clearRep s) t

theorem rep_stosw_down_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (lo : Nat) (h : RepStoswDownLoop s lo (count + 1)) :
    RepStoswDownDone s (nextStates (count + 1) s) lo (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repStosDownAfter 16 3 s) :=
      nextState_of_step (h.step hstride )
    have hdl := h.dstLow
    have htop := h.dstTop
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repStosDownAfter 16 3 s).Repeat_String_Operation = false := by
      rw [repStosDownAfter_repeat, hc]; rfl
    have hlo : rdi.read s = BitVec.ofNat 64 lo := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repStosDown 16 3 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repStosDownAfter_rip 16 3 s h.ready.msr, hc]; rfl
    · rw [repStosDownAfter_rcx, hc]
    · exact repStosDownAfter_rdi 16 3 s
    · intro i hi
      rw [Nat.mod_eq_of_lt (show i < 2 by omega), ← hlo]
      exact repStosDownAfter_fill 16 3 s (by decide) i (by omega)
    · rw [← clearRep_eq hflag, ← hlo]
      exact AgreesExcept.repStosDown 16 3 s
  | succ m ih =>
    have hnext : nextState s = (repStosDownAfter 16 3 s) :=
      nextState_of_step (h.step hstride )
    have hdl := h.dstLow
    have htop := h.dstTop
    have hfirst (i : Nat) (hi : i < 2) :
        (repStosDownAfter 16 3 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          some (storedByte ((Operand.reg 0 : Operand 16).read s) i) :=
      repStosDownAfter_fill 16 3 s (by decide) i hi
    have ih' := ih (repStosDownAfter 16 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repStosDownAfter 16 3 s).RIP = s.RIP := by
      rw [repStosDownAfter_rip 16 3 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, repStosDownAfter_rdi, sub_ofNat_sub_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 2 * (m + 1)
      · have hc := ih'.fill i hsmall
        rw [repStosDownAfter_rax] at hc
        exact hc
      · obtain ⟨j, rfl⟩ : ∃ j, i = 2 * (m + 1) + j := ⟨i - 2 * (m + 1), by omega⟩
        rw [show (2 * (m + 1) + j) % 2 = j by omega, h.top j]
        refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst j (by omega))
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j', hj', he⟩ := hcov
        rw [← h.top j] at he
        have hn := congrArg BitVec.toNat he
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hn
        omega
    · refine (AgreesExcept.repStosDown 16 3 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (BitVec.ofNat 64 lo) (2 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨2 * (m + 1) + j, by omega, by rw [h.top j]; exact he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩

structure RepStoswDownPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  dstBase : 2 * (rcx.read s).toNat ≤ (rdi.read s).toNat + 2
  dstLow : (rdi.read s).toNat + 2 ≤ 2^32
  dstMem : ∀ i < 2 * (rcx.read s).toNat,
    (s.external[downBase rdi 2 s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart ((rdi.read s).toNat + 2 - 2 * (rcx.read s).toNat)
    (2 * (rcx.read s).toNat)
  dstCode : RangeApart (downBase rdi 2 s) (2 * (rcx.read s).toNat) p 3

def repStoswDownEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rdi, rdi.read s - BitVec.ofNat 64 (2 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (downBase rdi 2 s) : Operand (16 * (rcx.read s).toNat)),
      ((Operand.reg 0 : Operand 16).read s).replicate (rcx.read s).toNat⟩]

@[simp] theorem repStoswDownEffect_components (p : BitVec 64) (s : RamState) :
    (repStoswDownEffect p s).components =
      [.reg 7, .reg 1, .mem (downBase rdi 2 s) (2 * (rcx.read s).toNat), .rip] := by
  simp only [repStoswDownEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 16 * (rcx.read s).toNat / 8 = 2 * (rcx.read s).toNat by omega]

theorem repStoswDownEffect_avoids {p : BitVec 64} {s : RamState} 
    (h : RangeApart (downBase rdi 2 s) (2 * (rcx.read s).toNat) p 3) :
    (repStoswDownEffect p s).Avoids (codeRange p [0xF3, 0x66, 0xAB]) :=
  Effect.avoids_of_mem (by rw [repStoswDownEffect_components]; simp [Component.isMem]) h rfl

theorem rep_stosw_down_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0x66, 0xAB]) s) (hpre : RepStoswDownPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0x66, 0xAB]) t ∧ (repStoswDownEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF3, 0x66, 0xAB] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repStoswDownEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repStoswDownEffect_avoids hpre.dstCode) hcode, hh.2⟩
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
    have hb : downBase rdi 2 s =
        BitVec.ofNat 64 ((rdi.read s).toNat + 2 - 2 * (c' + 1)) := by
      rw [downBase, hn]
    have hready : RepStoswDownLoop s ((rdi.read s).toNat + 2 - 2 * (c' + 1)) (c' + 1) := by
      have := hpre.dstBase
      have := hpre.dstLow
      refine ⟨h.midRep, hpre.df, hcodeS, hlow, hc, by omega, by omega,
        fun i hi => hb ▸ hpre.dstMem i (by omega), by have := hpre.dstTables; omega,
        hpre.rip ▸ hb ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_stosw_down_loop hstride c' s _ hready
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
      · show memLoad (nextStates (c' + 1) s).external (downBase rdi 2 s)
          (16 * (rcx.read s).toNat) = _
        apply memLoad_eq_of_memByte (by omega)
        intro i hi
        rw [storedByte_replicate _ (by decide) _ i (by omega), hb]
        have hf := hd.fill i (by omega)
        simp only [memByte, PhysicalMemory.read]
        exact congrArg (fun o : Option UInt8 => o.getD 0) hf
    · rw [repStoswDownEffect_components, hn, hb]
      exact hag.mono (by simp)

theorem rep_stosw_down_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepStoswDownPre p) (codeRange p [0xF3, 0x66, 0xAB]) (Effect.post (repStoswDownEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_stosw_down_steps hstride p s h hcode hpre⟩

structure RepStosbDownLoop [Bindings] (s : RamState) (lo : Nat) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0xAA]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  dstTop : (rdi.read s).toNat + 1 = lo + 1 * count
  dstLow : lo + 1 * count ≤ 2^32
  dstMem : ∀ i < 1 * count, (s.external[BitVec.ofNat 64 lo + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart lo (1 * count)
  dstCode : RangeApart (BitVec.ofNat 64 lo) (1 * count) s.RIP 2

theorem RepStosbDownLoop.rcx_ne [Bindings] {s : RamState} {lo : Nat} {count : Nat}
    (h : RepStosbDownLoop s lo count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem RepStosbDownLoop.top [Bindings] {s : RamState} {lo : Nat} {count : Nat}
    (h : RepStosbDownLoop s lo (count + 1)) (i : Nat) :
    BitVec.ofNat 64 lo + BitVec.ofNat 64 (1 * count + i) = rdi.read s + BitVec.ofNat 64 i :=
  ofNat_add_ofNat_eq (by have := h.dstTop; omega) i

theorem RepStosbDownLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {lo : Nat} {count : Nat} (h : RepStosbDownLoop s lo (count + 1)) :
    X86.Machine.step s = some (.next (repStosDownAfter 8 2 s)) := by
  have := h.dstLow
  have := h.dstTop
  exact rep_stosb_down_step hstride s h.ready [0xF3] (by simpa using scanPrefix_f3) (by simp)
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne (by omega))
    ⟨by omega, fun i hi => h.top i ▸ h.dstMem (1 * count + i) (by omega),
      by have := h.dstTables; omega⟩

theorem RepStosbDownLoop.next [Bindings] {s : RamState} {lo : Nat} {count : Nat}
    (h : RepStosbDownLoop s lo (count + 2)) : RepStosbDownLoop (repStosDownAfter 8 2 s) lo (count + 1) := by
  have hdl := h.dstLow
  have htop := h.dstTop
  have hrip : (repStosDownAfter 8 2 s).RIP = s.RIP := by
    rw [repStosDownAfter_rip 8 2 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hdn : (rdi.read (repStosDownAfter 8 2 s)).toNat = (rdi.read s).toNat - 1 := by
    rw [repStosDownAfter_rdi, toNat_sub_ofNat _ _ (by omega)]
  refine ⟨h.ready.repStosDown 8 2 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    by rw [repStosDownAfter_rcx, h.counter, ofNat_succ_sub_one], ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repStosDownAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode (1 * (count + 1) + j) (by omega) i (by simpa using hi)
        (by rw [h.top j]; exact he)
  · rw [hrip]; exact h.codeLow
  · rw [hdn]; omega
  · omega
  · intro i hi
    rw [repStosDownAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem i (by omega))
  · have := h.dstTables; omega
  · intro i hi j hj
    rw [hrip]
    exact h.dstCode i (by omega) j hj

structure RepStosbDownDone [Bindings] (s t : RamState) (lo : Nat) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rcxZero : rcx.read t = 0
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (1 * count)
  fill : ∀ i < 1 * count, t.external[BitVec.ofNat 64 lo + BitVec.ofNat 64 i]? =
    some (storedByte ((Operand.reg 0 : Operand 8).read s) (i % 1))
  agrees : AgreesExcept [.reg 1, .reg 7, .mem (BitVec.ofNat 64 lo) (1 * count), .rip] (clearRep s) t

theorem rep_stosb_down_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (lo : Nat) (h : RepStosbDownLoop s lo (count + 1)) :
    RepStosbDownDone s (nextStates (count + 1) s) lo (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repStosDownAfter 8 2 s) :=
      nextState_of_step (h.step hstride )
    have hdl := h.dstLow
    have htop := h.dstTop
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repStosDownAfter 8 2 s).Repeat_String_Operation = false := by
      rw [repStosDownAfter_repeat, hc]; rfl
    have hlo : rdi.read s = BitVec.ofNat 64 lo := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repStosDown 8 2 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repStosDownAfter_rip 8 2 s h.ready.msr, hc]; rfl
    · rw [repStosDownAfter_rcx, hc]
    · exact repStosDownAfter_rdi 8 2 s
    · intro i hi
      rw [Nat.mod_eq_of_lt (show i < 1 by omega), ← hlo]
      exact repStosDownAfter_fill 8 2 s (by decide) i (by omega)
    · rw [← clearRep_eq hflag, ← hlo]
      exact AgreesExcept.repStosDown 8 2 s
  | succ m ih =>
    have hnext : nextState s = (repStosDownAfter 8 2 s) :=
      nextState_of_step (h.step hstride )
    have hdl := h.dstLow
    have htop := h.dstTop
    have hfirst (i : Nat) (hi : i < 1) :
        (repStosDownAfter 8 2 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          some (storedByte ((Operand.reg 0 : Operand 8).read s) i) :=
      repStosDownAfter_fill 8 2 s (by decide) i hi
    have ih' := ih (repStosDownAfter 8 2 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repStosDownAfter 8 2 s).RIP = s.RIP := by
      rw [repStosDownAfter_rip 8 2 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, repStosDownAfter_rdi, sub_ofNat_sub_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 1 * (m + 1)
      · have hc := ih'.fill i hsmall
        rw [repStosDownAfter_rax] at hc
        exact hc
      · obtain ⟨j, rfl⟩ : ∃ j, i = 1 * (m + 1) + j := ⟨i - 1 * (m + 1), by omega⟩
        rw [show (1 * (m + 1) + j) % 1 = j by omega, h.top j]
        refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst j (by omega))
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j', hj', he⟩ := hcov
        rw [← h.top j] at he
        have hn := congrArg BitVec.toNat he
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hn
        omega
    · refine (AgreesExcept.repStosDown 8 2 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (BitVec.ofNat 64 lo) (1 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨1 * (m + 1) + j, by omega, by rw [h.top j]; exact he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩

structure RepStosbDownPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  dstBase : 1 * (rcx.read s).toNat ≤ (rdi.read s).toNat + 1
  dstLow : (rdi.read s).toNat + 1 ≤ 2^32
  dstMem : ∀ i < 1 * (rcx.read s).toNat,
    (s.external[downBase rdi 1 s + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart ((rdi.read s).toNat + 1 - 1 * (rcx.read s).toNat)
    (1 * (rcx.read s).toNat)
  dstCode : RangeApart (downBase rdi 1 s) (1 * (rcx.read s).toNat) p 2

def repStosbDownEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rdi, rdi.read s - BitVec.ofNat 64 (1 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (downBase rdi 1 s) : Operand (8 * (rcx.read s).toNat)),
      ((Operand.reg 0 : Operand 8).read s).replicate (rcx.read s).toNat⟩]

@[simp] theorem repStosbDownEffect_components (p : BitVec 64) (s : RamState) :
    (repStosbDownEffect p s).components =
      [.reg 7, .reg 1, .mem (downBase rdi 1 s) (1 * (rcx.read s).toNat), .rip] := by
  simp only [repStosbDownEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 8 * (rcx.read s).toNat / 8 = 1 * (rcx.read s).toNat by omega]

theorem repStosbDownEffect_avoids {p : BitVec 64} {s : RamState} 
    (h : RangeApart (downBase rdi 1 s) (1 * (rcx.read s).toNat) p 2) :
    (repStosbDownEffect p s).Avoids (codeRange p [0xF3, 0xAA]) :=
  Effect.avoids_of_mem (by rw [repStosbDownEffect_components]; simp [Component.isMem]) h rfl

theorem rep_stosb_down_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0xAA]) s) (hpre : RepStosbDownPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0xAA]) t ∧ (repStosbDownEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF3, 0xAA] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repStosbDownEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repStosbDownEffect_avoids hpre.dstCode) hcode, hh.2⟩
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
    have hb : downBase rdi 1 s =
        BitVec.ofNat 64 ((rdi.read s).toNat + 1 - 1 * (c' + 1)) := by
      rw [downBase, hn]
    have hready : RepStosbDownLoop s ((rdi.read s).toNat + 1 - 1 * (c' + 1)) (c' + 1) := by
      have := hpre.dstBase
      have := hpre.dstLow
      refine ⟨h.midRep, hpre.df, hcodeS, hlow, hc, by omega, by omega,
        fun i hi => hb ▸ hpre.dstMem i (by omega), by have := hpre.dstTables; omega,
        hpre.rip ▸ hb ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_stosb_down_loop hstride c' s _ hready
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
      · show memLoad (nextStates (c' + 1) s).external (downBase rdi 1 s)
          (8 * (rcx.read s).toNat) = _
        apply memLoad_eq_of_memByte (by omega)
        intro i hi
        rw [storedByte_replicate _ (by decide) _ i (by omega), hb]
        have hf := hd.fill i (by omega)
        simp only [memByte, PhysicalMemory.read]
        exact congrArg (fun o : Option UInt8 => o.getD 0) hf
    · rw [repStosbDownEffect_components, hn, hb]
      exact hag.mono (by simp)

theorem rep_stosb_down_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepStosbDownPre p) (codeRange p [0xF3, 0xAA]) (Effect.post (repStosbDownEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_stosb_down_steps hstride p s h hcode hpre⟩

attribute [x86_compose] repStosqDownEffect repStosdDownEffect repStoswDownEffect repStosbDownEffect

@[x86_local] theorem repStosqDownEffect_local {p : BitVec 64} : Effect.Local (repStosqDownEffect p) := by
  rep_effect_local [repStosqDownEffect, downBase]

@[x86_local] theorem repStosdDownEffect_local {p : BitVec 64} : Effect.Local (repStosdDownEffect p) := by
  rep_effect_local [repStosdDownEffect, downBase]

@[x86_local] theorem repStoswDownEffect_local {p : BitVec 64} : Effect.Local (repStoswDownEffect p) := by
  rep_effect_local [repStoswDownEffect, downBase]

@[x86_local] theorem repStosbDownEffect_local {p : BitVec 64} : Effect.Local (repStosbDownEffect p) := by
  rep_effect_local [repStosbDownEffect, downBase]

end X86Proofs

