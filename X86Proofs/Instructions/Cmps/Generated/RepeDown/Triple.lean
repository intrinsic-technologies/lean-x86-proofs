import X86Proofs.Instructions.Cmps.Generated.RepeDown.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

structure RepeCmpsqDownLoop [Bindings] (rex : UInt8) (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF3, rex, 0xA7]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  srcBase : 8 * m ≤ (rsi.read s).toNat
  srcLow : (rsi.read s).toNat + 8 ≤ 2^32
  dstBase : 8 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 8 ≤ 2^32
  srcMem : ∀ i < 8 * (m + 1),
    (s.external[rsi.read s - BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s - BitVec.ofNat 64 (8 * i)) : Operand 64).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.mem (rsi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = count

theorem RepeCmpsqDownLoop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepeCmpsqDownLoop rex s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) h.countLt

theorem RepeCmpsqDownLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState} {count m : Nat} (h : RepeCmpsqDownLoop rex s count m) :
    X86.Machine.step s = some (.next (repeCmpsDownAfter 64 3 s)) := by
  have hr := hrex.rexPrefix
  have := h.srcLow
  have := h.dstLow
  exact repe_cmpsq_down_step hcm s h.ready [0xF3, rex] (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => by
      have hm := h.srcMem (8 * m + i) (by omega)
      rwa [sub_ofNat_add_ofNat] at hm⟩
    ⟨by omega, fun i hi => by
      have hm := h.dstMem (8 * m + i) (by omega)
      rwa [sub_ofNat_add_ofNat] at hm⟩

theorem RepeCmpsqDownLoop.cont_true [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepeCmpsqDownLoop rex s count (m + 1)) : repeCmpsCont 64 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.sub_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeCmpsCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeCmpsqDownLoop.cont_false [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepeCmpsqDownLoop rex s count 0) : repeCmpsCont 64 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.sub_zero, Nat.zero_add] at hs
  unfold repeCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeCmpsqDownLoop.next [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepeCmpsqDownLoop rex s (count + 1) (m + 1)) : RepeCmpsqDownLoop rex (repeCmpsDownAfter 64 3 s) count m := by
  have hsb := h.srcBase
  have hsl := h.srcLow
  have hdb := h.dstBase
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeCmpsDownAfter 64 3 s).RIP = s.RIP := by
    rw [repeCmpsDownAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeCmpsDownAfter 64 3 s).RFLAGS = s.RFLAGS := by
    rw [repeCmpsDownAfter_rflags, hc]
    rfl
  have hs : rsi.read (repeCmpsDownAfter 64 3 s) = rsi.read s - BitVec.ofNat 64 8 := repeCmpsDownAfter_rsi 64 3 s
  have hd : rdi.read (repeCmpsDownAfter 64 3 s) = rdi.read s - BitVec.ofNat 64 8 := repeCmpsDownAfter_rdi 64 3 s
  have hsn : (rsi.read (repeCmpsDownAfter 64 3 s)).toNat = (rsi.read s).toNat - 8 := by
    rw [hs, toNat_sub_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repeCmpsDownAfter 64 3 s)).toNat = (rdi.read s).toNat - 8 := by
    rw [hd, toNat_sub_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 64).read (repeCmpsDownAfter 64 3 s) = (Operand.mem a : Operand 64).read s := by
    simp only [Operand.read, repeCmpsDownAfter_external]
  refine ⟨h.ready.repeCmpsDown 64 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeCmpsDownAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeCmpsDownAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, sub_ofNat_sub_ofNat, repeCmpsDownAfter_external,
      show 8 + 8 * m = 8 * (m + 1) by omega]
    exact h.srcMem i (by omega)
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, repeCmpsDownAfter_external,
      show 8 + 8 * m = 8 * (m + 1) by omega]
    exact h.dstMem i (by omega)
  · intro i hi
    rw [hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
      show 8 + 8 * i = 8 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
      show 8 + 8 * m = 8 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeCmpsqDownDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rsiAfter : rsi.read t = rsi.read s - BitVec.ofNat 64 (8 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (8 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_cmpsq_down_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeCmpsqDownLoop rex s count m →
      RepeCmpsqDownDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeCmpsDownAfter 64 3 s) := nextState_of_step (h.step hcm hrex )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeCmpsDownAfter 64 3 s).Repeat_String_Operation = false := by
      rw [repeCmpsDownAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeCmpsDown 64 3).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeCmpsDownAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeCmpsDownAfter_rsi]
    · rw [repeCmpsDownAfter_rdi]
    · rw [repeCmpsDownAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeCmpsDownAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.sub_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeCmpsDown 64 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeCmpsDownAfter 64 3 s) := nextState_of_step (h.step hcm hrex )
    have hc := h.cont_true
    have ih' := ih c (repeCmpsDownAfter 64 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repeCmpsDownAfter 64 3 s).RIP = s.RIP := by
      rw [repeCmpsDownAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeCmpsDownAfter 64 3 s).RFLAGS = s.RFLAGS := by
      rw [repeCmpsDownAfter_rflags, hc]
      rfl
    have hs : rsi.read (repeCmpsDownAfter 64 3 s) = rsi.read s - BitVec.ofNat 64 8 := repeCmpsDownAfter_rsi 64 3 s
    have hd : rdi.read (repeCmpsDownAfter 64 3 s) = rdi.read s - BitVec.ofNat 64 8 := repeCmpsDownAfter_rdi 64 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 64).read (repeCmpsDownAfter 64 3 s) = (Operand.mem a : Operand 64).read s := by
      simp only [Operand.read, repeCmpsDownAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
        show 8 + 8 * m = 8 * (m + 1) by omega]
    · refine ((AgreesExcept.repeCmpsDown 64 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeCmpsqDownPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  bound : m < (rcx.read s).toNat
  srcBase : 8 * m ≤ (rsi.read s).toNat
  srcLow : (rsi.read s).toNat + 8 ≤ 2^32
  dstBase : 8 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 8 ≤ 2^32
  srcMem : ∀ i < 8 * (m + 1),
    (s.external[rsi.read s - BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s - BitVec.ofNat 64 (8 * i)) : Operand 64).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.mem (rsi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = (rcx.read s).toNat

def repeCmpsqDownEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s - BitVec.ofNat 64 (8 * (m + 1))⟩,
    ⟨rdi, rdi.read s - BitVec.ofNat 64 (8 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s)))

@[simp] theorem repeCmpsqDownEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeCmpsqDownEffect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repeCmpsqDownEffect, Effect.components]

theorem repe_cmpsq_down_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, rex, 0xA7]) s) (hpre : RepeCmpsqDownPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, rex, 0xA7]) t ∧ (repeCmpsqDownEffect p m s).Holds s t := by
  intro t
  have hloop : RepeCmpsqDownLoop rex s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcBase,
      hpre.srcLow, hpre.dstBase, hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_cmpsq_down_loop hcm hrex m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeCmpsqDownEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeCmpsqDownEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repe_cmpsq_down_triple_of_bytes [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    Triple (RepeCmpsqDownPre p m) (codeRange p [0xF3, rex, 0xA7]) (Effect.post (repeCmpsqDownEffect p m)) :=
  fun s h hcode hpre => ⟨_, repe_cmpsq_down_steps hcm p rex hrex m s h hcode hpre⟩

theorem repe_cmpsq_down_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepeCmpsqDownPre p m) (codeRange p [0xF3, 0x48, 0xA7]) (Effect.post (repeCmpsqDownEffect p m)) :=
  repe_cmpsq_down_triple_of_bytes hcm p 0x48 (by unfold RexWPrefix; decide) m

structure RepeCmpsdDownLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0xA7]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  srcBase : 4 * m ≤ (rsi.read s).toNat
  srcLow : (rsi.read s).toNat + 4 ≤ 2^32
  dstBase : 4 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 4 ≤ 2^32
  srcMem : ∀ i < 4 * (m + 1),
    (s.external[rsi.read s - BitVec.ofNat 64 (4 * m) + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (4 * m) + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s - BitVec.ofNat 64 (4 * i)) : Operand 32).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.mem (rsi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = count

theorem RepeCmpsdDownLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpsdDownLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) h.countLt

theorem RepeCmpsdDownLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {s : RamState} {count m : Nat} (h : RepeCmpsdDownLoop s count m) :
    X86.Machine.step s = some (.next (repeCmpsDownAfter 32 2 s)) := by
  have := h.srcLow
  have := h.dstLow
  exact repe_cmpsd_down_step hcm s h.ready [0xF3] (by simpa using scanPrefix_f3) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => by
      have hm := h.srcMem (4 * m + i) (by omega)
      rwa [sub_ofNat_add_ofNat] at hm⟩
    ⟨by omega, fun i hi => by
      have hm := h.dstMem (4 * m + i) (by omega)
      rwa [sub_ofNat_add_ofNat] at hm⟩

theorem RepeCmpsdDownLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpsdDownLoop s count (m + 1)) : repeCmpsCont 32 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.sub_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeCmpsCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeCmpsdDownLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepeCmpsdDownLoop s count 0) : repeCmpsCont 32 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.sub_zero, Nat.zero_add] at hs
  unfold repeCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeCmpsdDownLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpsdDownLoop s (count + 1) (m + 1)) : RepeCmpsdDownLoop (repeCmpsDownAfter 32 2 s) count m := by
  have hsb := h.srcBase
  have hsl := h.srcLow
  have hdb := h.dstBase
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeCmpsDownAfter 32 2 s).RIP = s.RIP := by
    rw [repeCmpsDownAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeCmpsDownAfter 32 2 s).RFLAGS = s.RFLAGS := by
    rw [repeCmpsDownAfter_rflags, hc]
    rfl
  have hs : rsi.read (repeCmpsDownAfter 32 2 s) = rsi.read s - BitVec.ofNat 64 4 := repeCmpsDownAfter_rsi 32 2 s
  have hd : rdi.read (repeCmpsDownAfter 32 2 s) = rdi.read s - BitVec.ofNat 64 4 := repeCmpsDownAfter_rdi 32 2 s
  have hsn : (rsi.read (repeCmpsDownAfter 32 2 s)).toNat = (rsi.read s).toNat - 4 := by
    rw [hs, toNat_sub_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repeCmpsDownAfter 32 2 s)).toNat = (rdi.read s).toNat - 4 := by
    rw [hd, toNat_sub_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 32).read (repeCmpsDownAfter 32 2 s) = (Operand.mem a : Operand 32).read s := by
    simp only [Operand.read, repeCmpsDownAfter_external]
  refine ⟨h.ready.repeCmpsDown 32 2, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeCmpsDownAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeCmpsDownAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, sub_ofNat_sub_ofNat, repeCmpsDownAfter_external,
      show 4 + 4 * m = 4 * (m + 1) by omega]
    exact h.srcMem i (by omega)
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, repeCmpsDownAfter_external,
      show 4 + 4 * m = 4 * (m + 1) by omega]
    exact h.dstMem i (by omega)
  · intro i hi
    rw [hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
      show 4 + 4 * i = 4 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
      show 4 + 4 * m = 4 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeCmpsdDownDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rsiAfter : rsi.read t = rsi.read s - BitVec.ofNat 64 (4 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (4 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_cmpsd_down_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeCmpsdDownLoop s count m →
      RepeCmpsdDownDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeCmpsDownAfter 32 2 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeCmpsDownAfter 32 2 s).Repeat_String_Operation = false := by
      rw [repeCmpsDownAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeCmpsDown 32 2).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeCmpsDownAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeCmpsDownAfter_rsi]
    · rw [repeCmpsDownAfter_rdi]
    · rw [repeCmpsDownAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeCmpsDownAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.sub_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeCmpsDown 32 2 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeCmpsDownAfter 32 2 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repeCmpsDownAfter 32 2 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repeCmpsDownAfter 32 2 s).RIP = s.RIP := by
      rw [repeCmpsDownAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeCmpsDownAfter 32 2 s).RFLAGS = s.RFLAGS := by
      rw [repeCmpsDownAfter_rflags, hc]
      rfl
    have hs : rsi.read (repeCmpsDownAfter 32 2 s) = rsi.read s - BitVec.ofNat 64 4 := repeCmpsDownAfter_rsi 32 2 s
    have hd : rdi.read (repeCmpsDownAfter 32 2 s) = rdi.read s - BitVec.ofNat 64 4 := repeCmpsDownAfter_rdi 32 2 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 32).read (repeCmpsDownAfter 32 2 s) = (Operand.mem a : Operand 32).read s := by
      simp only [Operand.read, repeCmpsDownAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
        show 4 + 4 * m = 4 * (m + 1) by omega]
    · refine ((AgreesExcept.repeCmpsDown 32 2 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeCmpsdDownPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  bound : m < (rcx.read s).toNat
  srcBase : 4 * m ≤ (rsi.read s).toNat
  srcLow : (rsi.read s).toNat + 4 ≤ 2^32
  dstBase : 4 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 4 ≤ 2^32
  srcMem : ∀ i < 4 * (m + 1),
    (s.external[rsi.read s - BitVec.ofNat 64 (4 * m) + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (4 * m) + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s - BitVec.ofNat 64 (4 * i)) : Operand 32).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.mem (rsi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = (rcx.read s).toNat

def repeCmpsdDownEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rsi, rsi.read s - BitVec.ofNat 64 (4 * (m + 1))⟩,
    ⟨rdi, rdi.read s - BitVec.ofNat 64 (4 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s)))

@[simp] theorem repeCmpsdDownEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeCmpsdDownEffect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repeCmpsdDownEffect, Effect.components]

theorem repe_cmpsd_down_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0xA7]) s) (hpre : RepeCmpsdDownPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0xA7]) t ∧ (repeCmpsdDownEffect p m s).Holds s t := by
  intro t
  have hloop : RepeCmpsdDownLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcBase,
      hpre.srcLow, hpre.dstBase, hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_cmpsd_down_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeCmpsdDownEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeCmpsdDownEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repe_cmpsd_down_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepeCmpsdDownPre p m) (codeRange p [0xF3, 0xA7]) (Effect.post (repeCmpsdDownEffect p m)) :=
  fun s h hcode hpre => ⟨_, repe_cmpsd_down_steps hcm p m s h hcode hpre⟩

structure RepeCmpswDownLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0x66, 0xA7]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  srcBase : 2 * m ≤ (rsi.read s).toNat
  srcLow : (rsi.read s).toNat + 2 ≤ 2^32
  dstBase : 2 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 2 ≤ 2^32
  srcMem : ∀ i < 2 * (m + 1),
    (s.external[rsi.read s - BitVec.ofNat 64 (2 * m) + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 2 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (2 * m) + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s - BitVec.ofNat 64 (2 * i)) : Operand 16).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.mem (rsi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = count

theorem RepeCmpswDownLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpswDownLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) h.countLt

theorem RepeCmpswDownLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {s : RamState} {count m : Nat} (h : RepeCmpswDownLoop s count m) :
    X86.Machine.step s = some (.next (repeCmpsDownAfter 16 3 s)) := by
  have := h.srcLow
  have := h.dstLow
  exact repe_cmpsw_down_step hcm s h.ready [0xF3, 0x66] (by simp [scanPrefix_f3, scanPrefix_66]) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => by
      have hm := h.srcMem (2 * m + i) (by omega)
      rwa [sub_ofNat_add_ofNat] at hm⟩
    ⟨by omega, fun i hi => by
      have hm := h.dstMem (2 * m + i) (by omega)
      rwa [sub_ofNat_add_ofNat] at hm⟩

theorem RepeCmpswDownLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpswDownLoop s count (m + 1)) : repeCmpsCont 16 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.sub_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeCmpsCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeCmpswDownLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepeCmpswDownLoop s count 0) : repeCmpsCont 16 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.sub_zero, Nat.zero_add] at hs
  unfold repeCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeCmpswDownLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpswDownLoop s (count + 1) (m + 1)) : RepeCmpswDownLoop (repeCmpsDownAfter 16 3 s) count m := by
  have hsb := h.srcBase
  have hsl := h.srcLow
  have hdb := h.dstBase
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeCmpsDownAfter 16 3 s).RIP = s.RIP := by
    rw [repeCmpsDownAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeCmpsDownAfter 16 3 s).RFLAGS = s.RFLAGS := by
    rw [repeCmpsDownAfter_rflags, hc]
    rfl
  have hs : rsi.read (repeCmpsDownAfter 16 3 s) = rsi.read s - BitVec.ofNat 64 2 := repeCmpsDownAfter_rsi 16 3 s
  have hd : rdi.read (repeCmpsDownAfter 16 3 s) = rdi.read s - BitVec.ofNat 64 2 := repeCmpsDownAfter_rdi 16 3 s
  have hsn : (rsi.read (repeCmpsDownAfter 16 3 s)).toNat = (rsi.read s).toNat - 2 := by
    rw [hs, toNat_sub_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repeCmpsDownAfter 16 3 s)).toNat = (rdi.read s).toNat - 2 := by
    rw [hd, toNat_sub_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 16).read (repeCmpsDownAfter 16 3 s) = (Operand.mem a : Operand 16).read s := by
    simp only [Operand.read, repeCmpsDownAfter_external]
  refine ⟨h.ready.repeCmpsDown 16 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeCmpsDownAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeCmpsDownAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, sub_ofNat_sub_ofNat, repeCmpsDownAfter_external,
      show 2 + 2 * m = 2 * (m + 1) by omega]
    exact h.srcMem i (by omega)
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, repeCmpsDownAfter_external,
      show 2 + 2 * m = 2 * (m + 1) by omega]
    exact h.dstMem i (by omega)
  · intro i hi
    rw [hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
      show 2 + 2 * i = 2 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
      show 2 + 2 * m = 2 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeCmpswDownDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rsiAfter : rsi.read t = rsi.read s - BitVec.ofNat 64 (2 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (2 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_cmpsw_down_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeCmpswDownLoop s count m →
      RepeCmpswDownDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeCmpsDownAfter 16 3 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeCmpsDownAfter 16 3 s).Repeat_String_Operation = false := by
      rw [repeCmpsDownAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeCmpsDown 16 3).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeCmpsDownAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeCmpsDownAfter_rsi]
    · rw [repeCmpsDownAfter_rdi]
    · rw [repeCmpsDownAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeCmpsDownAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.sub_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeCmpsDown 16 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeCmpsDownAfter 16 3 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repeCmpsDownAfter 16 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repeCmpsDownAfter 16 3 s).RIP = s.RIP := by
      rw [repeCmpsDownAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeCmpsDownAfter 16 3 s).RFLAGS = s.RFLAGS := by
      rw [repeCmpsDownAfter_rflags, hc]
      rfl
    have hs : rsi.read (repeCmpsDownAfter 16 3 s) = rsi.read s - BitVec.ofNat 64 2 := repeCmpsDownAfter_rsi 16 3 s
    have hd : rdi.read (repeCmpsDownAfter 16 3 s) = rdi.read s - BitVec.ofNat 64 2 := repeCmpsDownAfter_rdi 16 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 16).read (repeCmpsDownAfter 16 3 s) = (Operand.mem a : Operand 16).read s := by
      simp only [Operand.read, repeCmpsDownAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
        show 2 + 2 * m = 2 * (m + 1) by omega]
    · refine ((AgreesExcept.repeCmpsDown 16 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeCmpswDownPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  bound : m < (rcx.read s).toNat
  srcBase : 2 * m ≤ (rsi.read s).toNat
  srcLow : (rsi.read s).toNat + 2 ≤ 2^32
  dstBase : 2 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 2 ≤ 2^32
  srcMem : ∀ i < 2 * (m + 1),
    (s.external[rsi.read s - BitVec.ofNat 64 (2 * m) + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 2 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (2 * m) + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s - BitVec.ofNat 64 (2 * i)) : Operand 16).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.mem (rsi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = (rcx.read s).toNat

def repeCmpswDownEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s - BitVec.ofNat 64 (2 * (m + 1))⟩,
    ⟨rdi, rdi.read s - BitVec.ofNat 64 (2 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s)))

@[simp] theorem repeCmpswDownEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeCmpswDownEffect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repeCmpswDownEffect, Effect.components]

theorem repe_cmpsw_down_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0x66, 0xA7]) s) (hpre : RepeCmpswDownPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0x66, 0xA7]) t ∧ (repeCmpswDownEffect p m s).Holds s t := by
  intro t
  have hloop : RepeCmpswDownLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcBase,
      hpre.srcLow, hpre.dstBase, hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_cmpsw_down_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeCmpswDownEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeCmpswDownEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repe_cmpsw_down_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepeCmpswDownPre p m) (codeRange p [0xF3, 0x66, 0xA7]) (Effect.post (repeCmpswDownEffect p m)) :=
  fun s h hcode hpre => ⟨_, repe_cmpsw_down_steps hcm p m s h hcode hpre⟩

structure RepeCmpsbDownLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0xA6]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  srcBase : 1 * m ≤ (rsi.read s).toNat
  srcLow : (rsi.read s).toNat + 1 ≤ 2^32
  dstBase : 1 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 1 ≤ 2^32
  srcMem : ∀ i < 1 * (m + 1),
    (s.external[rsi.read s - BitVec.ofNat 64 (1 * m) + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 1 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (1 * m) + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s - BitVec.ofNat 64 (1 * i)) : Operand 8).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.mem (rsi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = count

theorem RepeCmpsbDownLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpsbDownLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) h.countLt

theorem RepeCmpsbDownLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {s : RamState} {count m : Nat} (h : RepeCmpsbDownLoop s count m) :
    X86.Machine.step s = some (.next (repeCmpsDownAfter 8 2 s)) := by
  have := h.srcLow
  have := h.dstLow
  exact repe_cmpsb_down_step hcm s h.ready [0xF3] (by simpa using scanPrefix_f3) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => by
      have hm := h.srcMem (1 * m + i) (by omega)
      rwa [sub_ofNat_add_ofNat] at hm⟩
    ⟨by omega, fun i hi => by
      have hm := h.dstMem (1 * m + i) (by omega)
      rwa [sub_ofNat_add_ofNat] at hm⟩

theorem RepeCmpsbDownLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpsbDownLoop s count (m + 1)) : repeCmpsCont 8 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.sub_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeCmpsCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeCmpsbDownLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepeCmpsbDownLoop s count 0) : repeCmpsCont 8 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.sub_zero, Nat.zero_add] at hs
  unfold repeCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeCmpsbDownLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpsbDownLoop s (count + 1) (m + 1)) : RepeCmpsbDownLoop (repeCmpsDownAfter 8 2 s) count m := by
  have hsb := h.srcBase
  have hsl := h.srcLow
  have hdb := h.dstBase
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeCmpsDownAfter 8 2 s).RIP = s.RIP := by
    rw [repeCmpsDownAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeCmpsDownAfter 8 2 s).RFLAGS = s.RFLAGS := by
    rw [repeCmpsDownAfter_rflags, hc]
    rfl
  have hs : rsi.read (repeCmpsDownAfter 8 2 s) = rsi.read s - BitVec.ofNat 64 1 := repeCmpsDownAfter_rsi 8 2 s
  have hd : rdi.read (repeCmpsDownAfter 8 2 s) = rdi.read s - BitVec.ofNat 64 1 := repeCmpsDownAfter_rdi 8 2 s
  have hsn : (rsi.read (repeCmpsDownAfter 8 2 s)).toNat = (rsi.read s).toNat - 1 := by
    rw [hs, toNat_sub_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repeCmpsDownAfter 8 2 s)).toNat = (rdi.read s).toNat - 1 := by
    rw [hd, toNat_sub_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 8).read (repeCmpsDownAfter 8 2 s) = (Operand.mem a : Operand 8).read s := by
    simp only [Operand.read, repeCmpsDownAfter_external]
  refine ⟨h.ready.repeCmpsDown 8 2, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeCmpsDownAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeCmpsDownAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, sub_ofNat_sub_ofNat, repeCmpsDownAfter_external,
      show 1 + 1 * m = 1 * (m + 1) by omega]
    exact h.srcMem i (by omega)
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, repeCmpsDownAfter_external,
      show 1 + 1 * m = 1 * (m + 1) by omega]
    exact h.dstMem i (by omega)
  · intro i hi
    rw [hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
      show 1 + 1 * i = 1 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
      show 1 + 1 * m = 1 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeCmpsbDownDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rsiAfter : rsi.read t = rsi.read s - BitVec.ofNat 64 (1 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (1 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_cmpsb_down_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeCmpsbDownLoop s count m →
      RepeCmpsbDownDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeCmpsDownAfter 8 2 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeCmpsDownAfter 8 2 s).Repeat_String_Operation = false := by
      rw [repeCmpsDownAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeCmpsDown 8 2).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeCmpsDownAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeCmpsDownAfter_rsi]
    · rw [repeCmpsDownAfter_rdi]
    · rw [repeCmpsDownAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeCmpsDownAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.sub_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeCmpsDown 8 2 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeCmpsDownAfter 8 2 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repeCmpsDownAfter 8 2 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repeCmpsDownAfter 8 2 s).RIP = s.RIP := by
      rw [repeCmpsDownAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeCmpsDownAfter 8 2 s).RFLAGS = s.RFLAGS := by
      rw [repeCmpsDownAfter_rflags, hc]
      rfl
    have hs : rsi.read (repeCmpsDownAfter 8 2 s) = rsi.read s - BitVec.ofNat 64 1 := repeCmpsDownAfter_rsi 8 2 s
    have hd : rdi.read (repeCmpsDownAfter 8 2 s) = rdi.read s - BitVec.ofNat 64 1 := repeCmpsDownAfter_rdi 8 2 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 8).read (repeCmpsDownAfter 8 2 s) = (Operand.mem a : Operand 8).read s := by
      simp only [Operand.read, repeCmpsDownAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
        show 1 + 1 * m = 1 * (m + 1) by omega]
    · refine ((AgreesExcept.repeCmpsDown 8 2 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeCmpsbDownPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  bound : m < (rcx.read s).toNat
  srcBase : 1 * m ≤ (rsi.read s).toNat
  srcLow : (rsi.read s).toNat + 1 ≤ 2^32
  dstBase : 1 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 1 ≤ 2^32
  srcMem : ∀ i < 1 * (m + 1),
    (s.external[rsi.read s - BitVec.ofNat 64 (1 * m) + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 1 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (1 * m) + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s - BitVec.ofNat 64 (1 * i)) : Operand 8).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.mem (rsi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = (rcx.read s).toNat

def repeCmpsbDownEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rsi, rsi.read s - BitVec.ofNat 64 (1 * (m + 1))⟩,
    ⟨rdi, rdi.read s - BitVec.ofNat 64 (1 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s)))

@[simp] theorem repeCmpsbDownEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeCmpsbDownEffect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repeCmpsbDownEffect, Effect.components]

theorem repe_cmpsb_down_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0xA6]) s) (hpre : RepeCmpsbDownPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0xA6]) t ∧ (repeCmpsbDownEffect p m s).Holds s t := by
  intro t
  have hloop : RepeCmpsbDownLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcBase,
      hpre.srcLow, hpre.dstBase, hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_cmpsb_down_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeCmpsbDownEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeCmpsbDownEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repe_cmpsb_down_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepeCmpsbDownPre p m) (codeRange p [0xF3, 0xA6]) (Effect.post (repeCmpsbDownEffect p m)) :=
  fun s h hcode hpre => ⟨_, repe_cmpsb_down_steps hcm p m s h hcode hpre⟩

attribute [x86_compose] repeCmpsqDownEffect repeCmpsdDownEffect repeCmpswDownEffect repeCmpsbDownEffect

@[x86_local] theorem repeCmpsqDownEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeCmpsqDownEffect p m) := by
  effect_local [repeCmpsqDownEffect]

@[x86_local] theorem repeCmpsdDownEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeCmpsdDownEffect p m) := by
  effect_local [repeCmpsdDownEffect]

@[x86_local] theorem repeCmpswDownEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeCmpswDownEffect p m) := by
  effect_local [repeCmpswDownEffect]

@[x86_local] theorem repeCmpsbDownEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeCmpsbDownEffect p m) := by
  effect_local [repeCmpsbDownEffect]

end X86Proofs

