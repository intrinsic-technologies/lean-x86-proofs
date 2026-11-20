import X86Proofs.Instructions.Movs.RepStep
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

/-!
# `rep movsq`: the whole instruction

With RCX = n ≥ 1, `rep movsq` takes n steps, one quadword each, with RIP on the instruction until
the last; with RCX = 0 it takes one step that copies nothing. So it takes `max n 1` steps.

- `ReadyRepLoop rex s count`: the loop invariant: ready to step up to the
  repeat flag, DF clear, the instruction at RIP, RCX = `count`, and the memory conditions for the
  remaining `8 * count` bytes at RSI and RDI. `ReadyRepLoop.next`: one iteration re-establishes it for
  `count - 1`, with the pointers moved on.
- `RepDone s t count`: what `count` iterations from `s` achieve: `t` is ready to step, RIP is past
  the instruction, RCX = 0, RSI and RDI moved on by `8 * count`, the destination bytes are the
  source bytes as they were in `s`, and nothing else changed.
- `rep_movsq_loop`: induction on the count (generalizing the state), building the result one
  quadword at a time from the front.
- `rep_movsq_steps` and `rep_movsq_triple`: the instruction as an `Effect` whose memory write is
  the whole destination range, as one `64 * n`-bit memory operand (`memLoad` and `memStore` work
  at any width; `memByte_of_memLoad_eq` turns the value back into bytes).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-! ### The loop invariant -/

/-- The invariant of the `rep movsq` loop with `count` quadwords left, for the encoding
`F3 rex A5`. -/
structure ReadyRepLoop [Bindings] (rex : UInt8) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, rex, 0xA5]
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

theorem ReadyRepLoop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : ReadyRepLoop rex s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

/-- One iteration from `ReadyRepLoop … count` (`count ≥ 1`) runs normally. -/
theorem ReadyRepLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {rex : UInt8}
    (hrex : RexWPrefix rex.toBitVec) {s : RamState} {count : Nat} (h : ReadyRepLoop rex s count)
    (hpos : 0 < count) : X86.Machine.step s = some (.next (repMovsqAfter s)) := by
  have := h.srcLow
  have := h.dstLow
  exact rep_movsq_step hstride s h.ready rex hrex h.df h.code h.codeLow (h.rcx_ne hpos) (by omega)
    (by omega) (fun i hi => h.srcMem i (by omega)) (fun i hi => h.dstMem i (by omega))

theorem ReadyRepLoop.rcx_after [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : ReadyRepLoop rex s (count + 1)) : rcx.read (repMovsqAfter s) = BitVec.ofNat 64 count := by
  rw [repMovsqAfter_rcx, h.counter, ofNat_succ_sub_one]

/-- The source bytes beyond the first quadword survive an iteration (source and destination are
disjoint). -/
theorem ReadyRepLoop.source_frame [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : ReadyRepLoop rex s count) (j : Nat) (hj : j < 8 * count) :
    (repMovsqAfter s).external[rsi.read s + BitVec.ofNat 64 j]? =
      s.external[rsi.read s + BitVec.ofNat 64 j]? := by
  rw [repMovsqAfter_external]
  apply memStore_getElem?_of_ne
  intro i hi he
  have hn := congrArg BitVec.toNat he
  have := h.srcLow
  have := h.dstLow
  have := h.disjoint
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
  omega

/-- One iteration re-establishes the invariant for one quadword less. -/
theorem ReadyRepLoop.next [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : ReadyRepLoop rex s (count + 2)) : ReadyRepLoop rex (repMovsqAfter s) (count + 1) := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hrip : (repMovsqAfter s).RIP = s.RIP := by
    rw [repMovsqAfter_rip s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : rsi.read (repMovsqAfter s) = rsi.read s + BitVec.ofNat 64 8 := repMovsqAfter_rsi s
  have hd : rdi.read (repMovsqAfter s) = rdi.read s + BitVec.ofNat 64 8 := repMovsqAfter_rdi s
  have hsn : (rsi.read (repMovsqAfter s)).toNat = (rsi.read s).toNat + 8 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repMovsqAfter s)).toNat = (rdi.read s).toNat + 8 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repMovsq (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repMovsqAfter_external, memStore_getElem?_of_ne]
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
    rw [hd, add_ofNat_add_ofNat, repMovsqAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (8 + i) (by omega))
  · rw [hsn, hdn]; have := h.disjoint; omega
  · rw [hdn]; have := h.dstTables; omega
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, hrip]
    exact h.dstCode (8 + i) (by omega) j hj

/-! ### The result of the loop -/

/-- What `count` iterations from `s` achieve, ending in `t`. -/
structure RepDone [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP 3#64
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (8 * count)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (8 * count)
  copy : ∀ i < 8 * count,
    t.external[rdi.read s + BitVec.ofNat 64 i]? = s.external[rsi.read s + BitVec.ofNat 64 i]?
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) (8 * count), .rip]
    (clearRep s) t

/-- The loop: from `ReadyRepLoop … (count + 1)`, `count + 1` steps run the whole instruction. -/
theorem rep_movsq_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {rex : UInt8}
    (hrex : RexWPrefix rex.toBitVec) (count : Nat) (s : RamState) (h : ReadyRepLoop rex s (count + 1)) :
    RepDone s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = repMovsqAfter s := nextState_of_step (h.step hstride hrex (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repMovsqAfter s).Repeat_String_Operation = false := by
      rw [repMovsqAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repMovsq (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repMovsqAfter_rip s h.ready.msr, hc]; rfl
    · rw [repMovsqAfter_rcx, hc]
    · exact repMovsqAfter_rsi s
    · exact repMovsqAfter_rdi s
    · intro i hi
      exact repMovsqAfter_copy s i (by omega) (h.srcMem i (by omega))
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repMovsq s
  | succ k ih =>
    have hnext : nextState s = repMovsqAfter s := nextState_of_step (h.step hstride hrex (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hs : rsi.read (repMovsqAfter s) = rsi.read s + BitVec.ofNat 64 8 := repMovsqAfter_rsi s
    have hd : rdi.read (repMovsqAfter s) = rdi.read s + BitVec.ofNat 64 8 := repMovsqAfter_rdi s
    have hfirst (i : Nat) (hi : i < 8) :
        (repMovsqAfter s).external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[rsi.read s + BitVec.ofNat 64 i]? :=
      repMovsqAfter_copy s i hi (h.srcMem i (by omega))
    have ih' := ih (repMovsqAfter s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repMovsqAfter s).RIP = s.RIP := by
      rw [repMovsqAfter_rip s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := k + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 8
      · -- written by the first iteration, untouched by the rest
        refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst i hsmall)
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
    · refine (AgreesExcept.repMovsq s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (8 * (k + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hd, add_ofNat_add_ofNat] at he
          exact ⟨8 + j, by omega, he⟩

/-! ### The effect and the triple -/

/--
What `rep movsq` at `p` needs besides `ReadyToStep`, with n = RCX: RIP = `p`, DF clear, the
`8 * n` source bytes (at RSI) and destination bytes (at RDI) below 4 GiB and present in RAM (either
may be unaligned and cross a page), the two ranges disjoint, and the destination outside the
page-table entries (`PageTableEntriesApart`) and the instruction's own 3 bytes.
-/
structure RepMovsqPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (rsi.read s).toNat + 8 * (rcx.read s).toNat ≤ 2^32
  dstLow : (rdi.read s).toNat + 8 * (rcx.read s).toNat ≤ 2^32
  srcMem : ∀ i < 8 * (rcx.read s).toNat, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 8 * (rcx.read s).toNat ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 8 * (rcx.read s).toNat ≤ (rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (8 * (rcx.read s).toNat)
  dstCode : RangeApart (rdi.read s) (8 * (rcx.read s).toNat) p 3

/--
The effect of `rep movsq` at `p` from state `s`, with n = RCX: RIP = `p + 3`, RSI and RDI advanced
by `8 * n`, RCX = 0, and the `8 * n` bytes at the old RDI set to the `8 * n` bytes at the old RSI,
written as one `64 * n`-bit memory operand. The flags are untouched.
-/
def repMovsqEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (8 * (rcx.read s).toNat)⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (8 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (rdi.read s) : Operand (64 * (rcx.read s).toNat)),
      (Operand.mem (rsi.read s) : Operand (64 * (rcx.read s).toNat)).read s⟩]

@[simp] theorem repMovsqEffect_components (p : BitVec 64) (s : RamState) :
    (repMovsqEffect p s).components =
      [.reg 6, .reg 7, .reg 1, .mem (rdi.read s) (8 * (rcx.read s).toNat), .rip] := by
  simp only [repMovsqEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 64 * (rcx.read s).toNat / 8 = 8 * (rcx.read s).toNat by omega]

/-- `rep movsq` at `p` does not overwrite its own bytes if the destination misses them. -/
theorem repMovsqEffect_avoids {p : BitVec 64} {s : RamState} (rex : UInt8)
    (h : RangeApart (rdi.read s) (8 * (rcx.read s).toNat) p 3) :
    (repMovsqEffect p s).Avoids (codeRange p [0xF3, rex, 0xA5]) := by
  intro x hx c hc hcov
  rw [repMovsqEffect_components] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hcov
  obtain ⟨i, hi, hxe⟩ := hcov
  obtain ⟨j, hj, hxj⟩ := exists_of_mem_codeRange hx
  exact h i hi j hj (hxe.symm.trans hxj)

/--
`rep movsq` with the step count explicit: from a ready state with `F3 rex A5` at `p` and
`RepMovsqPre p`, `max n 1` steps (n = RCX) reach a ready state with the code still in memory and
the effect `repMovsqEffect p`.
-/
theorem rep_movsq_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, rex, 0xA5]) s) (hpre : RepMovsqPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, rex, 0xA5]) t ∧ (repMovsqEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF3, rex, 0xA5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovsqEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovsqEffect_avoids rex hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | k
  · -- RCX = 0: one step, nothing copied
    have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repMovsqZeroAfter s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsq_step_zero s h.midRep rex hrex hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repMovsqZeroAfter s) :=
      (AgreesExcept.repMovsqZero s).of_clearRep hrep (repMovsqZeroAfter_repeat s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables, ?_, ?_, trivial, ?_⟩
    · rw [repMovsqZeroAfter_rip s h.ready.msr, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hz]
      · apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have hi' : i < 64 * (rcx.read s).toNat := hi
        omega
    · exact hag.mono (by simp)
  · -- RCX = k + 1: the loop
    have hc : rcx.read s = BitVec.ofNat 64 (k + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.srcLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hready : ReadyRepLoop rex s (k + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_movsq_loop hstride hrex k s hready
    have ht : t = nextStates (k + 1) s := by
      simp only [t, hn, show max (k + 1) 1 = k + 1 by omega]
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

/-- The triple for `rep movsq` (`F3 rex A5`, REX.W) at `p`: the effect `repMovsqEffect`. Needs
the stride binding to answer 1 (`Prelude.UnitStringStride`). -/
theorem rep_movsq_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepMovsqPre p) (codeRange p [0xF3, rex, 0xA5]) (Effect.post (repMovsqEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_movsq_steps hstride p rex hrex s h hcode hpre⟩

/-- Reading the effect back as bytes: after `rep movsq` with n = RCX, each of the `8 * n` bytes at
the old RDI is the byte that was at the old RSI. -/
theorem repMovsqEffect_bytes {p : BitVec 64} {s s' : RamState} (h : (repMovsqEffect p s).Holds s s')
    (i : Nat) (hi : i < 8 * (rcx.read s).toNat) :
    memByte s'.external (rdi.read s + BitVec.ofNat 64 i) =
      memByte s.external (rsi.read s + BitVec.ofNat 64 i) :=
  memByte_of_memLoad_eq (n := 64 * (rcx.read s).toNat) h.writes.2.2.2 i (by omega)

attribute [x86_compose] repMovsqEffect

/-- `rep movsq` reads only what `Obs` sees: RSI, RDI, RCX and the bytes it copies (whose number,
`8 * RCX`, is part of the written operand's type, so RCX is rewritten everywhere at once). -/
@[x86_local] theorem repMovsqEffect_local {p : BitVec 64} : Effect.Local (repMovsqEffect p) := by
  refine ⟨fun _ _ _ => rfl, fun t t' h => ?_, fun _ _ _ => rfl, fun t t' h i hi => ?_,
    fun t => ?_⟩
  · have hc : rcx.read t = rcx.read t' := h.read_reg 1
    simp only [repMovsqEffect]
    rw [hc]
    simp only [h.read_reg, h.read_mem]
  · simpa [repMovsqEffect, Effect.flag] using hi
  · intro w hw
    simp only [repMovsqEffect, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · rfl
    · rfl
    · rfl
    · exact mul_mod_eight _ rfl

section Carry

variable {e : Effect} {s s' : RamState}

@[x86_pre] theorem RepMovsqPre.of_holds (h : e.Holds s s') (ho : Obs (e.after s true) s')
    {p : BitVec 64} (hrip : e.rip = p)
    (hdf : (Operand.df : Operand 1).read (e.after s true) = 0#1)
    (hsrcLow : (rsi.read (e.after s true)).toNat + 8 * (rcx.read (e.after s true)).toNat ≤ 2^32)
    (hdstLow : (rdi.read (e.after s true)).toNat + 8 * (rcx.read (e.after s true)).toNat ≤ 2^32)
    (hsrcMem : ∀ i < 8 * (rcx.read (e.after s true)).toNat,
      (s.external[rsi.read (e.after s true) + BitVec.ofNat 64 i]?).isSome)
    (hdstMem : ∀ i < 8 * (rcx.read (e.after s true)).toNat,
      (s.external[rdi.read (e.after s true) + BitVec.ofNat 64 i]?).isSome)
    (hdisjoint : (rsi.read (e.after s true)).toNat + 8 * (rcx.read (e.after s true)).toNat ≤
        (rdi.read (e.after s true)).toNat ∨
      (rdi.read (e.after s true)).toNat + 8 * (rcx.read (e.after s true)).toNat ≤
        (rsi.read (e.after s true)).toNat)
    (hdstTables : PageTableEntriesApart (rdi.read (e.after s true)).toNat
      (8 * (rcx.read (e.after s true)).toNat))
    (hdstCode : RangeApart (rdi.read (e.after s true)) (8 * (rcx.read (e.after s true)).toNat)
      p 3) : RepMovsqPre p s' := by
  have hsi : rsi.read s' = rsi.read (e.after s true) := Obs.back_reg ho 6
  have hdi : rdi.read s' = rdi.read (e.after s true) := Obs.back_reg ho 7
  have hci : rcx.read s' = rcx.read (e.after s true) := Obs.back_reg ho 1
  refine ⟨h.rip_of hrip, DirectionFlagClear.of_obs ho hdf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [hsi, hdi, hci]
  · exact hsrcLow
  · exact hdstLow
  · exact h.present hsrcMem
  · exact h.present hdstMem
  · exact hdisjoint
  · exact hdstTables
  · exact hdstCode

end Carry

end X86Proofs
