import X86Proofs.Instructions.Cmps.Generated.RepneDown.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

structure RepneCmpsqDownLoop [Bindings] (rex : UInt8) (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF2, rex, 0xA7]
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
  differ : ∀ i < m, ((Operand.mem (rsi.read s - BitVec.ofNat 64 (8 * i)) : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.mem (rsi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = count

theorem RepneCmpsqDownLoop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepneCmpsqDownLoop rex s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) h.countLt

theorem RepneCmpsqDownLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState} {count m : Nat} (h : RepneCmpsqDownLoop rex s count m) :
    X86.Machine.step s = some (.next (repneCmpsDownAfter 64 3 s)) := by
  have hr := hrex.rexPrefix
  have := h.srcLow
  have := h.dstLow
  exact repne_cmpsq_down_step hcm s h.ready [0xF2, rex] (by simp [scanPrefix_f2, hr.scanPrefix]) (by simp)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => by
      have hm := h.srcMem (8 * m + i) (by omega)
      rwa [sub_ofNat_add_ofNat] at hm⟩
    ⟨by omega, fun i hi => by
      have hm := h.dstMem (8 * m + i) (by omega)
      rwa [sub_ofNat_add_ofNat] at hm⟩

theorem RepneCmpsqDownLoop.cont_true [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepneCmpsqDownLoop rex s count (m + 1)) : repneCmpsCont 64 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.sub_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneCmpsCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneCmpsqDownLoop.cont_false [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepneCmpsqDownLoop rex s count 0) : repneCmpsCont 64 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.sub_zero, Nat.zero_add] at hs
  unfold repneCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneCmpsqDownLoop.next [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepneCmpsqDownLoop rex s (count + 1) (m + 1)) : RepneCmpsqDownLoop rex (repneCmpsDownAfter 64 3 s) count m := by
  have hsb := h.srcBase
  have hsl := h.srcLow
  have hdb := h.dstBase
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneCmpsDownAfter 64 3 s).RIP = s.RIP := by
    rw [repneCmpsDownAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneCmpsDownAfter 64 3 s).RFLAGS = s.RFLAGS := by
    rw [repneCmpsDownAfter_rflags, hc]
    rfl
  have hs : rsi.read (repneCmpsDownAfter 64 3 s) = rsi.read s - BitVec.ofNat 64 8 := repneCmpsDownAfter_rsi 64 3 s
  have hd : rdi.read (repneCmpsDownAfter 64 3 s) = rdi.read s - BitVec.ofNat 64 8 := repneCmpsDownAfter_rdi 64 3 s
  have hsn : (rsi.read (repneCmpsDownAfter 64 3 s)).toNat = (rsi.read s).toNat - 8 := by
    rw [hs, toNat_sub_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repneCmpsDownAfter 64 3 s)).toNat = (rdi.read s).toNat - 8 := by
    rw [hd, toNat_sub_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 64).read (repneCmpsDownAfter 64 3 s) = (Operand.mem a : Operand 64).read s := by
    simp only [Operand.read, repneCmpsDownAfter_external]
  refine ⟨h.ready.repneCmpsDown 64 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneCmpsDownAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneCmpsDownAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, sub_ofNat_sub_ofNat, repneCmpsDownAfter_external,
      show 8 + 8 * m = 8 * (m + 1) by omega]
    exact h.srcMem i (by omega)
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, repneCmpsDownAfter_external,
      show 8 + 8 * m = 8 * (m + 1) by omega]
    exact h.dstMem i (by omega)
  · intro i hi
    rw [hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
      show 8 + 8 * i = 8 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
      show 8 + 8 * m = 8 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneCmpsqDownDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rsiAfter : rsi.read t = rsi.read s - BitVec.ofNat 64 (8 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (8 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_cmpsq_down_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneCmpsqDownLoop rex s count m →
      RepneCmpsqDownDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneCmpsDownAfter 64 3 s) := nextState_of_step (h.step hcm hrex )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneCmpsDownAfter 64 3 s).Repeat_String_Operation = false := by
      rw [repneCmpsDownAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneCmpsDown 64 3).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneCmpsDownAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneCmpsDownAfter_rsi]
    · rw [repneCmpsDownAfter_rdi]
    · rw [repneCmpsDownAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneCmpsDownAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.sub_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneCmpsDown 64 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneCmpsDownAfter 64 3 s) := nextState_of_step (h.step hcm hrex )
    have hc := h.cont_true
    have ih' := ih c (repneCmpsDownAfter 64 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repneCmpsDownAfter 64 3 s).RIP = s.RIP := by
      rw [repneCmpsDownAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneCmpsDownAfter 64 3 s).RFLAGS = s.RFLAGS := by
      rw [repneCmpsDownAfter_rflags, hc]
      rfl
    have hs : rsi.read (repneCmpsDownAfter 64 3 s) = rsi.read s - BitVec.ofNat 64 8 := repneCmpsDownAfter_rsi 64 3 s
    have hd : rdi.read (repneCmpsDownAfter 64 3 s) = rdi.read s - BitVec.ofNat 64 8 := repneCmpsDownAfter_rdi 64 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 64).read (repneCmpsDownAfter 64 3 s) = (Operand.mem a : Operand 64).read s := by
      simp only [Operand.read, repneCmpsDownAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
        show 8 + 8 * m = 8 * (m + 1) by omega]
    · refine ((AgreesExcept.repneCmpsDown 64 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneCmpsqDownPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
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
  differ : ∀ i < m, ((Operand.mem (rsi.read s - BitVec.ofNat 64 (8 * i)) : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.mem (rsi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = (rcx.read s).toNat

def repneCmpsqDownEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s - BitVec.ofNat 64 (8 * (m + 1))⟩,
    ⟨rdi, rdi.read s - BitVec.ofNat 64 (8 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s)))

@[simp] theorem repneCmpsqDownEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneCmpsqDownEffect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repneCmpsqDownEffect, Effect.components]

theorem repne_cmpsq_down_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, rex, 0xA7]) s) (hpre : RepneCmpsqDownPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, rex, 0xA7]) t ∧ (repneCmpsqDownEffect p m s).Holds s t := by
  intro t
  have hloop : RepneCmpsqDownLoop rex s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcBase,
      hpre.srcLow, hpre.dstBase, hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_cmpsq_down_loop hcm hrex m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneCmpsqDownEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneCmpsqDownEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repne_cmpsq_down_triple_of_bytes [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    Triple (RepneCmpsqDownPre p m) (codeRange p [0xF2, rex, 0xA7]) (Effect.post (repneCmpsqDownEffect p m)) :=
  fun s h hcode hpre => ⟨_, repne_cmpsq_down_steps hcm p rex hrex m s h hcode hpre⟩

theorem repne_cmpsq_down_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepneCmpsqDownPre p m) (codeRange p [0xF2, 0x48, 0xA7]) (Effect.post (repneCmpsqDownEffect p m)) :=
  repne_cmpsq_down_triple_of_bytes hcm p 0x48 (by unfold RexWPrefix; decide) m

structure RepneCmpsdDownLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF2, 0xA7]
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
  differ : ∀ i < m, ((Operand.mem (rsi.read s - BitVec.ofNat 64 (4 * i)) : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.mem (rsi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = count

theorem RepneCmpsdDownLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpsdDownLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) h.countLt

theorem RepneCmpsdDownLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {s : RamState} {count m : Nat} (h : RepneCmpsdDownLoop s count m) :
    X86.Machine.step s = some (.next (repneCmpsDownAfter 32 2 s)) := by
  have := h.srcLow
  have := h.dstLow
  exact repne_cmpsd_down_step hcm s h.ready [0xF2] (by simpa using scanPrefix_f2) (by simp)
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

theorem RepneCmpsdDownLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpsdDownLoop s count (m + 1)) : repneCmpsCont 32 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.sub_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneCmpsCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneCmpsdDownLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepneCmpsdDownLoop s count 0) : repneCmpsCont 32 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.sub_zero, Nat.zero_add] at hs
  unfold repneCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneCmpsdDownLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpsdDownLoop s (count + 1) (m + 1)) : RepneCmpsdDownLoop (repneCmpsDownAfter 32 2 s) count m := by
  have hsb := h.srcBase
  have hsl := h.srcLow
  have hdb := h.dstBase
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneCmpsDownAfter 32 2 s).RIP = s.RIP := by
    rw [repneCmpsDownAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneCmpsDownAfter 32 2 s).RFLAGS = s.RFLAGS := by
    rw [repneCmpsDownAfter_rflags, hc]
    rfl
  have hs : rsi.read (repneCmpsDownAfter 32 2 s) = rsi.read s - BitVec.ofNat 64 4 := repneCmpsDownAfter_rsi 32 2 s
  have hd : rdi.read (repneCmpsDownAfter 32 2 s) = rdi.read s - BitVec.ofNat 64 4 := repneCmpsDownAfter_rdi 32 2 s
  have hsn : (rsi.read (repneCmpsDownAfter 32 2 s)).toNat = (rsi.read s).toNat - 4 := by
    rw [hs, toNat_sub_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repneCmpsDownAfter 32 2 s)).toNat = (rdi.read s).toNat - 4 := by
    rw [hd, toNat_sub_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 32).read (repneCmpsDownAfter 32 2 s) = (Operand.mem a : Operand 32).read s := by
    simp only [Operand.read, repneCmpsDownAfter_external]
  refine ⟨h.ready.repneCmpsDown 32 2, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneCmpsDownAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneCmpsDownAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, sub_ofNat_sub_ofNat, repneCmpsDownAfter_external,
      show 4 + 4 * m = 4 * (m + 1) by omega]
    exact h.srcMem i (by omega)
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, repneCmpsDownAfter_external,
      show 4 + 4 * m = 4 * (m + 1) by omega]
    exact h.dstMem i (by omega)
  · intro i hi
    rw [hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
      show 4 + 4 * i = 4 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
      show 4 + 4 * m = 4 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneCmpsdDownDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rsiAfter : rsi.read t = rsi.read s - BitVec.ofNat 64 (4 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (4 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_cmpsd_down_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneCmpsdDownLoop s count m →
      RepneCmpsdDownDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneCmpsDownAfter 32 2 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneCmpsDownAfter 32 2 s).Repeat_String_Operation = false := by
      rw [repneCmpsDownAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneCmpsDown 32 2).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneCmpsDownAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneCmpsDownAfter_rsi]
    · rw [repneCmpsDownAfter_rdi]
    · rw [repneCmpsDownAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneCmpsDownAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.sub_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneCmpsDown 32 2 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneCmpsDownAfter 32 2 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repneCmpsDownAfter 32 2 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repneCmpsDownAfter 32 2 s).RIP = s.RIP := by
      rw [repneCmpsDownAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneCmpsDownAfter 32 2 s).RFLAGS = s.RFLAGS := by
      rw [repneCmpsDownAfter_rflags, hc]
      rfl
    have hs : rsi.read (repneCmpsDownAfter 32 2 s) = rsi.read s - BitVec.ofNat 64 4 := repneCmpsDownAfter_rsi 32 2 s
    have hd : rdi.read (repneCmpsDownAfter 32 2 s) = rdi.read s - BitVec.ofNat 64 4 := repneCmpsDownAfter_rdi 32 2 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 32).read (repneCmpsDownAfter 32 2 s) = (Operand.mem a : Operand 32).read s := by
      simp only [Operand.read, repneCmpsDownAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
        show 4 + 4 * m = 4 * (m + 1) by omega]
    · refine ((AgreesExcept.repneCmpsDown 32 2 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneCmpsdDownPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
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
  differ : ∀ i < m, ((Operand.mem (rsi.read s - BitVec.ofNat 64 (4 * i)) : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.mem (rsi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = (rcx.read s).toNat

def repneCmpsdDownEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rsi, rsi.read s - BitVec.ofNat 64 (4 * (m + 1))⟩,
    ⟨rdi, rdi.read s - BitVec.ofNat 64 (4 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s)))

@[simp] theorem repneCmpsdDownEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneCmpsdDownEffect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repneCmpsdDownEffect, Effect.components]

theorem repne_cmpsd_down_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, 0xA7]) s) (hpre : RepneCmpsdDownPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, 0xA7]) t ∧ (repneCmpsdDownEffect p m s).Holds s t := by
  intro t
  have hloop : RepneCmpsdDownLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcBase,
      hpre.srcLow, hpre.dstBase, hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_cmpsd_down_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneCmpsdDownEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneCmpsdDownEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repne_cmpsd_down_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepneCmpsdDownPre p m) (codeRange p [0xF2, 0xA7]) (Effect.post (repneCmpsdDownEffect p m)) :=
  fun s h hcode hpre => ⟨_, repne_cmpsd_down_steps hcm p m s h hcode hpre⟩

structure RepneCmpswDownLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF2, 0x66, 0xA7]
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
  differ : ∀ i < m, ((Operand.mem (rsi.read s - BitVec.ofNat 64 (2 * i)) : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.mem (rsi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = count

theorem RepneCmpswDownLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpswDownLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) h.countLt

theorem RepneCmpswDownLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {s : RamState} {count m : Nat} (h : RepneCmpswDownLoop s count m) :
    X86.Machine.step s = some (.next (repneCmpsDownAfter 16 3 s)) := by
  have := h.srcLow
  have := h.dstLow
  exact repne_cmpsw_down_step hcm s h.ready [0xF2, 0x66] (by simp [scanPrefix_f2, scanPrefix_66]) (by simp)
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

theorem RepneCmpswDownLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpswDownLoop s count (m + 1)) : repneCmpsCont 16 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.sub_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneCmpsCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneCmpswDownLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepneCmpswDownLoop s count 0) : repneCmpsCont 16 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.sub_zero, Nat.zero_add] at hs
  unfold repneCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneCmpswDownLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpswDownLoop s (count + 1) (m + 1)) : RepneCmpswDownLoop (repneCmpsDownAfter 16 3 s) count m := by
  have hsb := h.srcBase
  have hsl := h.srcLow
  have hdb := h.dstBase
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneCmpsDownAfter 16 3 s).RIP = s.RIP := by
    rw [repneCmpsDownAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneCmpsDownAfter 16 3 s).RFLAGS = s.RFLAGS := by
    rw [repneCmpsDownAfter_rflags, hc]
    rfl
  have hs : rsi.read (repneCmpsDownAfter 16 3 s) = rsi.read s - BitVec.ofNat 64 2 := repneCmpsDownAfter_rsi 16 3 s
  have hd : rdi.read (repneCmpsDownAfter 16 3 s) = rdi.read s - BitVec.ofNat 64 2 := repneCmpsDownAfter_rdi 16 3 s
  have hsn : (rsi.read (repneCmpsDownAfter 16 3 s)).toNat = (rsi.read s).toNat - 2 := by
    rw [hs, toNat_sub_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repneCmpsDownAfter 16 3 s)).toNat = (rdi.read s).toNat - 2 := by
    rw [hd, toNat_sub_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 16).read (repneCmpsDownAfter 16 3 s) = (Operand.mem a : Operand 16).read s := by
    simp only [Operand.read, repneCmpsDownAfter_external]
  refine ⟨h.ready.repneCmpsDown 16 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneCmpsDownAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneCmpsDownAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, sub_ofNat_sub_ofNat, repneCmpsDownAfter_external,
      show 2 + 2 * m = 2 * (m + 1) by omega]
    exact h.srcMem i (by omega)
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, repneCmpsDownAfter_external,
      show 2 + 2 * m = 2 * (m + 1) by omega]
    exact h.dstMem i (by omega)
  · intro i hi
    rw [hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
      show 2 + 2 * i = 2 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
      show 2 + 2 * m = 2 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneCmpswDownDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rsiAfter : rsi.read t = rsi.read s - BitVec.ofNat 64 (2 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (2 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_cmpsw_down_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneCmpswDownLoop s count m →
      RepneCmpswDownDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneCmpsDownAfter 16 3 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneCmpsDownAfter 16 3 s).Repeat_String_Operation = false := by
      rw [repneCmpsDownAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneCmpsDown 16 3).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneCmpsDownAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneCmpsDownAfter_rsi]
    · rw [repneCmpsDownAfter_rdi]
    · rw [repneCmpsDownAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneCmpsDownAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.sub_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneCmpsDown 16 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneCmpsDownAfter 16 3 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repneCmpsDownAfter 16 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repneCmpsDownAfter 16 3 s).RIP = s.RIP := by
      rw [repneCmpsDownAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneCmpsDownAfter 16 3 s).RFLAGS = s.RFLAGS := by
      rw [repneCmpsDownAfter_rflags, hc]
      rfl
    have hs : rsi.read (repneCmpsDownAfter 16 3 s) = rsi.read s - BitVec.ofNat 64 2 := repneCmpsDownAfter_rsi 16 3 s
    have hd : rdi.read (repneCmpsDownAfter 16 3 s) = rdi.read s - BitVec.ofNat 64 2 := repneCmpsDownAfter_rdi 16 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 16).read (repneCmpsDownAfter 16 3 s) = (Operand.mem a : Operand 16).read s := by
      simp only [Operand.read, repneCmpsDownAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
        show 2 + 2 * m = 2 * (m + 1) by omega]
    · refine ((AgreesExcept.repneCmpsDown 16 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneCmpswDownPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
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
  differ : ∀ i < m, ((Operand.mem (rsi.read s - BitVec.ofNat 64 (2 * i)) : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.mem (rsi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = (rcx.read s).toNat

def repneCmpswDownEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s - BitVec.ofNat 64 (2 * (m + 1))⟩,
    ⟨rdi, rdi.read s - BitVec.ofNat 64 (2 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s)))

@[simp] theorem repneCmpswDownEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneCmpswDownEffect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repneCmpswDownEffect, Effect.components]

theorem repne_cmpsw_down_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, 0x66, 0xA7]) s) (hpre : RepneCmpswDownPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, 0x66, 0xA7]) t ∧ (repneCmpswDownEffect p m s).Holds s t := by
  intro t
  have hloop : RepneCmpswDownLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcBase,
      hpre.srcLow, hpre.dstBase, hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_cmpsw_down_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneCmpswDownEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneCmpswDownEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repne_cmpsw_down_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepneCmpswDownPre p m) (codeRange p [0xF2, 0x66, 0xA7]) (Effect.post (repneCmpswDownEffect p m)) :=
  fun s h hcode hpre => ⟨_, repne_cmpsw_down_steps hcm p m s h hcode hpre⟩

structure RepneCmpsbDownLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF2, 0xA6]
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
  differ : ∀ i < m, ((Operand.mem (rsi.read s - BitVec.ofNat 64 (1 * i)) : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.mem (rsi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = count

theorem RepneCmpsbDownLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpsbDownLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) h.countLt

theorem RepneCmpsbDownLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {s : RamState} {count m : Nat} (h : RepneCmpsbDownLoop s count m) :
    X86.Machine.step s = some (.next (repneCmpsDownAfter 8 2 s)) := by
  have := h.srcLow
  have := h.dstLow
  exact repne_cmpsb_down_step hcm s h.ready [0xF2] (by simpa using scanPrefix_f2) (by simp)
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

theorem RepneCmpsbDownLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpsbDownLoop s count (m + 1)) : repneCmpsCont 8 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.sub_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneCmpsCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneCmpsbDownLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepneCmpsbDownLoop s count 0) : repneCmpsCont 8 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.sub_zero, Nat.zero_add] at hs
  unfold repneCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneCmpsbDownLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpsbDownLoop s (count + 1) (m + 1)) : RepneCmpsbDownLoop (repneCmpsDownAfter 8 2 s) count m := by
  have hsb := h.srcBase
  have hsl := h.srcLow
  have hdb := h.dstBase
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneCmpsDownAfter 8 2 s).RIP = s.RIP := by
    rw [repneCmpsDownAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneCmpsDownAfter 8 2 s).RFLAGS = s.RFLAGS := by
    rw [repneCmpsDownAfter_rflags, hc]
    rfl
  have hs : rsi.read (repneCmpsDownAfter 8 2 s) = rsi.read s - BitVec.ofNat 64 1 := repneCmpsDownAfter_rsi 8 2 s
  have hd : rdi.read (repneCmpsDownAfter 8 2 s) = rdi.read s - BitVec.ofNat 64 1 := repneCmpsDownAfter_rdi 8 2 s
  have hsn : (rsi.read (repneCmpsDownAfter 8 2 s)).toNat = (rsi.read s).toNat - 1 := by
    rw [hs, toNat_sub_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repneCmpsDownAfter 8 2 s)).toNat = (rdi.read s).toNat - 1 := by
    rw [hd, toNat_sub_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 8).read (repneCmpsDownAfter 8 2 s) = (Operand.mem a : Operand 8).read s := by
    simp only [Operand.read, repneCmpsDownAfter_external]
  refine ⟨h.ready.repneCmpsDown 8 2, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneCmpsDownAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneCmpsDownAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, sub_ofNat_sub_ofNat, repneCmpsDownAfter_external,
      show 1 + 1 * m = 1 * (m + 1) by omega]
    exact h.srcMem i (by omega)
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, repneCmpsDownAfter_external,
      show 1 + 1 * m = 1 * (m + 1) by omega]
    exact h.dstMem i (by omega)
  · intro i hi
    rw [hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
      show 1 + 1 * i = 1 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
      show 1 + 1 * m = 1 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneCmpsbDownDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rsiAfter : rsi.read t = rsi.read s - BitVec.ofNat 64 (1 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (1 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_cmpsb_down_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneCmpsbDownLoop s count m →
      RepneCmpsbDownDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneCmpsDownAfter 8 2 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneCmpsDownAfter 8 2 s).Repeat_String_Operation = false := by
      rw [repneCmpsDownAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneCmpsDown 8 2).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneCmpsDownAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneCmpsDownAfter_rsi]
    · rw [repneCmpsDownAfter_rdi]
    · rw [repneCmpsDownAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneCmpsDownAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.sub_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneCmpsDown 8 2 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneCmpsDownAfter 8 2 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repneCmpsDownAfter 8 2 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repneCmpsDownAfter 8 2 s).RIP = s.RIP := by
      rw [repneCmpsDownAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneCmpsDownAfter 8 2 s).RFLAGS = s.RFLAGS := by
      rw [repneCmpsDownAfter_rflags, hc]
      rfl
    have hs : rsi.read (repneCmpsDownAfter 8 2 s) = rsi.read s - BitVec.ofNat 64 1 := repneCmpsDownAfter_rsi 8 2 s
    have hd : rdi.read (repneCmpsDownAfter 8 2 s) = rdi.read s - BitVec.ofNat 64 1 := repneCmpsDownAfter_rdi 8 2 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 8).read (repneCmpsDownAfter 8 2 s) = (Operand.mem a : Operand 8).read s := by
      simp only [Operand.read, repneCmpsDownAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, sub_ofNat_sub_ofNat, sub_ofNat_sub_ofNat, hm, hm,
        show 1 + 1 * m = 1 * (m + 1) by omega]
    · refine ((AgreesExcept.repneCmpsDown 8 2 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneCmpsbDownPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
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
  differ : ∀ i < m, ((Operand.mem (rsi.read s - BitVec.ofNat 64 (1 * i)) : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.mem (rsi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = (rcx.read s).toNat

def repneCmpsbDownEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rsi, rsi.read s - BitVec.ofNat 64 (1 * (m + 1))⟩,
    ⟨rdi, rdi.read s - BitVec.ofNat 64 (1 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s)))

@[simp] theorem repneCmpsbDownEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneCmpsbDownEffect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repneCmpsbDownEffect, Effect.components]

theorem repne_cmpsb_down_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, 0xA6]) s) (hpre : RepneCmpsbDownPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, 0xA6]) t ∧ (repneCmpsbDownEffect p m s).Holds s t := by
  intro t
  have hloop : RepneCmpsbDownLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcBase,
      hpre.srcLow, hpre.dstBase, hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_cmpsb_down_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneCmpsbDownEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneCmpsbDownEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repne_cmpsb_down_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepneCmpsbDownPre p m) (codeRange p [0xF2, 0xA6]) (Effect.post (repneCmpsbDownEffect p m)) :=
  fun s h hcode hpre => ⟨_, repne_cmpsb_down_steps hcm p m s h hcode hpre⟩

attribute [x86_compose] repneCmpsqDownEffect repneCmpsdDownEffect repneCmpswDownEffect repneCmpsbDownEffect

@[x86_local] theorem repneCmpsqDownEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneCmpsqDownEffect p m) := by
  effect_local [repneCmpsqDownEffect]

@[x86_local] theorem repneCmpsdDownEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneCmpsdDownEffect p m) := by
  effect_local [repneCmpsdDownEffect]

@[x86_local] theorem repneCmpswDownEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneCmpswDownEffect p m) := by
  effect_local [repneCmpswDownEffect]

@[x86_local] theorem repneCmpsbDownEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneCmpsbDownEffect p m) := by
  effect_local [repneCmpsbDownEffect]

end X86Proofs

