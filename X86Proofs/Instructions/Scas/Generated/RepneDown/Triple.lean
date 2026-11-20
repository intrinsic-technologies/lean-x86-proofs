import X86Proofs.Instructions.Scas.Generated.RepneDown.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

structure RepneScasqDownLoop [Bindings] (rex : UInt8) (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF2, rex, 0xAF]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  dstBase : 8 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 8 ≤ 2^32
  dstMem : ∀ i < 8 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.reg 0 : Operand 64).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = count

theorem RepneScasqDownLoop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepneScasqDownLoop rex s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) h.countLt

theorem RepneScasqDownLoop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState} {count m : Nat} (h : RepneScasqDownLoop rex s count m) :
    X86.Machine.step s = some (.next (repneScasDownAfter 64 3 s)) := by
  have hr := hrex.rexPrefix
  have := h.dstLow
  exact repne_scasq_down_step hstride s h.ready [0xF2, rex] (by simp [scanPrefix_f2, hr.scanPrefix]) (by simp)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => by
      have hm := h.dstMem (8 * m + i) (by omega)
      rwa [sub_ofNat_add_ofNat] at hm⟩

theorem RepneScasqDownLoop.cont_true [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepneScasqDownLoop rex s count (m + 1)) : repneScasCont 64 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.sub_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneScasCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneScasqDownLoop.cont_false [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepneScasqDownLoop rex s count 0) : repneScasCont 64 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.sub_zero, Nat.zero_add] at hs
  unfold repneScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneScasqDownLoop.next [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepneScasqDownLoop rex s (count + 1) (m + 1)) : RepneScasqDownLoop rex (repneScasDownAfter 64 3 s) count m := by
  have hdb := h.dstBase
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneScasDownAfter 64 3 s).RIP = s.RIP := by
    rw [repneScasDownAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneScasDownAfter 64 3 s).RFLAGS = s.RFLAGS := by
    rw [repneScasDownAfter_rflags, hc]
    rfl
  have hd : rdi.read (repneScasDownAfter 64 3 s) = rdi.read s - BitVec.ofNat 64 8 := repneScasDownAfter_rdi 64 3 s
  have hdn : (rdi.read (repneScasDownAfter 64 3 s)).toNat = (rdi.read s).toNat - 8 := by
    rw [hd, toNat_sub_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 64).read (repneScasDownAfter 64 3 s) = (Operand.mem a : Operand 64).read s := by
    simp only [Operand.read, repneScasDownAfter_external]
  have ha := repneScasDownAfter_acc 64 3 s
  refine ⟨h.ready.repneScasDown 64 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneScasDownAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneScasDownAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, repneScasDownAfter_external,
      show 8 + 8 * m = 8 * (m + 1) by omega]
    exact h.dstMem i (by omega)
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, ha, hm,
      show 8 + 8 * i = 8 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hd, sub_ofNat_sub_ofNat, ha, hm,
      show 8 + 8 * m = 8 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneScasqDownDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (8 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 64).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_scasq_down_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneScasqDownLoop rex s count m →
      RepneScasqDownDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneScasDownAfter 64 3 s) := nextState_of_step (h.step hstride hrex )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneScasDownAfter 64 3 s).Repeat_String_Operation = false := by
      rw [repneScasDownAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneScasDown 64 3).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneScasDownAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneScasDownAfter_rdi]
    · rw [repneScasDownAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneScasDownAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.sub_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneScasDown 64 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneScasDownAfter 64 3 s) := nextState_of_step (h.step hstride hrex )
    have hc := h.cont_true
    have ih' := ih c (repneScasDownAfter 64 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repneScasDownAfter 64 3 s).RIP = s.RIP := by
      rw [repneScasDownAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneScasDownAfter 64 3 s).RFLAGS = s.RFLAGS := by
      rw [repneScasDownAfter_rflags, hc]
      rfl
    have ha := repneScasDownAfter_acc 64 3 s
    have hd : rdi.read (repneScasDownAfter 64 3 s) = rdi.read s - BitVec.ofNat 64 8 := repneScasDownAfter_rdi 64 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 64).read (repneScasDownAfter 64 3 s) = (Operand.mem a : Operand 64).read s := by
      simp only [Operand.read, repneScasDownAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, sub_ofNat_sub_ofNat, ha, hm,
        show 8 + 8 * m = 8 * (m + 1) by omega]
    · refine ((AgreesExcept.repneScasDown 64 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneScasqDownPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  bound : m < (rcx.read s).toNat
  dstBase : 8 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 8 ≤ 2^32
  dstMem : ∀ i < 8 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.reg 0 : Operand 64).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = (rcx.read s).toNat

def repneScasqDownEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rdi, rdi.read s - BitVec.ofNat 64 (8 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 64).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s)))

@[simp] theorem repneScasqDownEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneScasqDownEffect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repneScasqDownEffect, Effect.components]

theorem repne_scasq_down_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, rex, 0xAF]) s) (hpre : RepneScasqDownPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, rex, 0xAF]) t ∧ (repneScasqDownEffect p m s).Holds s t := by
  intro t
  have hloop : RepneScasqDownLoop rex s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.dstBase,
      hpre.dstLow, hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_scasq_down_loop hstride hrex m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneScasqDownEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneScasqDownEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repne_scasq_down_triple_of_bytes [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    Triple (RepneScasqDownPre p m) (codeRange p [0xF2, rex, 0xAF]) (Effect.post (repneScasqDownEffect p m)) :=
  fun s h hcode hpre => ⟨_, repne_scasq_down_steps hstride p rex hrex m s h hcode hpre⟩

theorem repne_scasq_down_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepneScasqDownPre p m) (codeRange p [0xF2, 0x48, 0xAF]) (Effect.post (repneScasqDownEffect p m)) :=
  repne_scasq_down_triple_of_bytes hstride p 0x48 (by unfold RexWPrefix; decide) m

structure RepneScasdDownLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF2, 0xAF]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  dstBase : 4 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 4 ≤ 2^32
  dstMem : ∀ i < 4 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (4 * m) + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.reg 0 : Operand 32).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = count

theorem RepneScasdDownLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScasdDownLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) h.countLt

theorem RepneScasdDownLoop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count m : Nat} (h : RepneScasdDownLoop s count m) :
    X86.Machine.step s = some (.next (repneScasDownAfter 32 2 s)) := by
  have := h.dstLow
  exact repne_scasd_down_step hstride s h.ready [0xF2] (by simpa using scanPrefix_f2) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => by
      have hm := h.dstMem (4 * m + i) (by omega)
      rwa [sub_ofNat_add_ofNat] at hm⟩

theorem RepneScasdDownLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScasdDownLoop s count (m + 1)) : repneScasCont 32 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.sub_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneScasCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneScasdDownLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepneScasdDownLoop s count 0) : repneScasCont 32 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.sub_zero, Nat.zero_add] at hs
  unfold repneScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneScasdDownLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScasdDownLoop s (count + 1) (m + 1)) : RepneScasdDownLoop (repneScasDownAfter 32 2 s) count m := by
  have hdb := h.dstBase
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneScasDownAfter 32 2 s).RIP = s.RIP := by
    rw [repneScasDownAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneScasDownAfter 32 2 s).RFLAGS = s.RFLAGS := by
    rw [repneScasDownAfter_rflags, hc]
    rfl
  have hd : rdi.read (repneScasDownAfter 32 2 s) = rdi.read s - BitVec.ofNat 64 4 := repneScasDownAfter_rdi 32 2 s
  have hdn : (rdi.read (repneScasDownAfter 32 2 s)).toNat = (rdi.read s).toNat - 4 := by
    rw [hd, toNat_sub_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 32).read (repneScasDownAfter 32 2 s) = (Operand.mem a : Operand 32).read s := by
    simp only [Operand.read, repneScasDownAfter_external]
  have ha := repneScasDownAfter_acc 32 2 s
  refine ⟨h.ready.repneScasDown 32 2, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneScasDownAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneScasDownAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, repneScasDownAfter_external,
      show 4 + 4 * m = 4 * (m + 1) by omega]
    exact h.dstMem i (by omega)
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, ha, hm,
      show 4 + 4 * i = 4 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hd, sub_ofNat_sub_ofNat, ha, hm,
      show 4 + 4 * m = 4 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneScasdDownDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (4 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 32).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_scasd_down_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneScasdDownLoop s count m →
      RepneScasdDownDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneScasDownAfter 32 2 s) := nextState_of_step (h.step hstride )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneScasDownAfter 32 2 s).Repeat_String_Operation = false := by
      rw [repneScasDownAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneScasDown 32 2).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneScasDownAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneScasDownAfter_rdi]
    · rw [repneScasDownAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneScasDownAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.sub_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneScasDown 32 2 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneScasDownAfter 32 2 s) := nextState_of_step (h.step hstride )
    have hc := h.cont_true
    have ih' := ih c (repneScasDownAfter 32 2 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repneScasDownAfter 32 2 s).RIP = s.RIP := by
      rw [repneScasDownAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneScasDownAfter 32 2 s).RFLAGS = s.RFLAGS := by
      rw [repneScasDownAfter_rflags, hc]
      rfl
    have ha := repneScasDownAfter_acc 32 2 s
    have hd : rdi.read (repneScasDownAfter 32 2 s) = rdi.read s - BitVec.ofNat 64 4 := repneScasDownAfter_rdi 32 2 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 32).read (repneScasDownAfter 32 2 s) = (Operand.mem a : Operand 32).read s := by
      simp only [Operand.read, repneScasDownAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, sub_ofNat_sub_ofNat, ha, hm,
        show 4 + 4 * m = 4 * (m + 1) by omega]
    · refine ((AgreesExcept.repneScasDown 32 2 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneScasdDownPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  bound : m < (rcx.read s).toNat
  dstBase : 4 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 4 ≤ 2^32
  dstMem : ∀ i < 4 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (4 * m) + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.reg 0 : Operand 32).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = (rcx.read s).toNat

def repneScasdDownEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rdi, rdi.read s - BitVec.ofNat 64 (4 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 32).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s)))

@[simp] theorem repneScasdDownEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneScasdDownEffect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repneScasdDownEffect, Effect.components]

theorem repne_scasd_down_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, 0xAF]) s) (hpre : RepneScasdDownPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, 0xAF]) t ∧ (repneScasdDownEffect p m s).Holds s t := by
  intro t
  have hloop : RepneScasdDownLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.dstBase,
      hpre.dstLow, hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_scasd_down_loop hstride m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneScasdDownEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneScasdDownEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repne_scasd_down_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepneScasdDownPre p m) (codeRange p [0xF2, 0xAF]) (Effect.post (repneScasdDownEffect p m)) :=
  fun s h hcode hpre => ⟨_, repne_scasd_down_steps hstride p m s h hcode hpre⟩

structure RepneScaswDownLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF2, 0x66, 0xAF]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  dstBase : 2 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 2 ≤ 2^32
  dstMem : ∀ i < 2 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (2 * m) + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.reg 0 : Operand 16).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = count

theorem RepneScaswDownLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScaswDownLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) h.countLt

theorem RepneScaswDownLoop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count m : Nat} (h : RepneScaswDownLoop s count m) :
    X86.Machine.step s = some (.next (repneScasDownAfter 16 3 s)) := by
  have := h.dstLow
  exact repne_scasw_down_step hstride s h.ready [0xF2, 0x66] (by simp [scanPrefix_f2, scanPrefix_66]) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => by
      have hm := h.dstMem (2 * m + i) (by omega)
      rwa [sub_ofNat_add_ofNat] at hm⟩

theorem RepneScaswDownLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScaswDownLoop s count (m + 1)) : repneScasCont 16 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.sub_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneScasCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneScaswDownLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepneScaswDownLoop s count 0) : repneScasCont 16 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.sub_zero, Nat.zero_add] at hs
  unfold repneScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneScaswDownLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScaswDownLoop s (count + 1) (m + 1)) : RepneScaswDownLoop (repneScasDownAfter 16 3 s) count m := by
  have hdb := h.dstBase
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneScasDownAfter 16 3 s).RIP = s.RIP := by
    rw [repneScasDownAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneScasDownAfter 16 3 s).RFLAGS = s.RFLAGS := by
    rw [repneScasDownAfter_rflags, hc]
    rfl
  have hd : rdi.read (repneScasDownAfter 16 3 s) = rdi.read s - BitVec.ofNat 64 2 := repneScasDownAfter_rdi 16 3 s
  have hdn : (rdi.read (repneScasDownAfter 16 3 s)).toNat = (rdi.read s).toNat - 2 := by
    rw [hd, toNat_sub_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 16).read (repneScasDownAfter 16 3 s) = (Operand.mem a : Operand 16).read s := by
    simp only [Operand.read, repneScasDownAfter_external]
  have ha := repneScasDownAfter_acc 16 3 s
  refine ⟨h.ready.repneScasDown 16 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneScasDownAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneScasDownAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, repneScasDownAfter_external,
      show 2 + 2 * m = 2 * (m + 1) by omega]
    exact h.dstMem i (by omega)
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, ha, hm,
      show 2 + 2 * i = 2 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hd, sub_ofNat_sub_ofNat, ha, hm,
      show 2 + 2 * m = 2 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneScaswDownDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (2 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 16).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_scasw_down_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneScaswDownLoop s count m →
      RepneScaswDownDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneScasDownAfter 16 3 s) := nextState_of_step (h.step hstride )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneScasDownAfter 16 3 s).Repeat_String_Operation = false := by
      rw [repneScasDownAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneScasDown 16 3).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneScasDownAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneScasDownAfter_rdi]
    · rw [repneScasDownAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneScasDownAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.sub_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneScasDown 16 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneScasDownAfter 16 3 s) := nextState_of_step (h.step hstride )
    have hc := h.cont_true
    have ih' := ih c (repneScasDownAfter 16 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repneScasDownAfter 16 3 s).RIP = s.RIP := by
      rw [repneScasDownAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneScasDownAfter 16 3 s).RFLAGS = s.RFLAGS := by
      rw [repneScasDownAfter_rflags, hc]
      rfl
    have ha := repneScasDownAfter_acc 16 3 s
    have hd : rdi.read (repneScasDownAfter 16 3 s) = rdi.read s - BitVec.ofNat 64 2 := repneScasDownAfter_rdi 16 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 16).read (repneScasDownAfter 16 3 s) = (Operand.mem a : Operand 16).read s := by
      simp only [Operand.read, repneScasDownAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, sub_ofNat_sub_ofNat, ha, hm,
        show 2 + 2 * m = 2 * (m + 1) by omega]
    · refine ((AgreesExcept.repneScasDown 16 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneScaswDownPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  bound : m < (rcx.read s).toNat
  dstBase : 2 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 2 ≤ 2^32
  dstMem : ∀ i < 2 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (2 * m) + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.reg 0 : Operand 16).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = (rcx.read s).toNat

def repneScaswDownEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rdi, rdi.read s - BitVec.ofNat 64 (2 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 16).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s)))

@[simp] theorem repneScaswDownEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneScaswDownEffect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repneScaswDownEffect, Effect.components]

theorem repne_scasw_down_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, 0x66, 0xAF]) s) (hpre : RepneScaswDownPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, 0x66, 0xAF]) t ∧ (repneScaswDownEffect p m s).Holds s t := by
  intro t
  have hloop : RepneScaswDownLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.dstBase,
      hpre.dstLow, hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_scasw_down_loop hstride m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneScaswDownEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneScaswDownEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repne_scasw_down_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepneScaswDownPre p m) (codeRange p [0xF2, 0x66, 0xAF]) (Effect.post (repneScaswDownEffect p m)) :=
  fun s h hcode hpre => ⟨_, repne_scasw_down_steps hstride p m s h hcode hpre⟩

structure RepneScasbDownLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF2, 0xAE]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  dstBase : 1 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 1 ≤ 2^32
  dstMem : ∀ i < 1 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (1 * m) + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.reg 0 : Operand 8).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = count

theorem RepneScasbDownLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScasbDownLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) h.countLt

theorem RepneScasbDownLoop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count m : Nat} (h : RepneScasbDownLoop s count m) :
    X86.Machine.step s = some (.next (repneScasDownAfter 8 2 s)) := by
  have := h.dstLow
  exact repne_scasb_down_step hstride s h.ready [0xF2] (by simpa using scanPrefix_f2) (by simp)
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => by
      have hm := h.dstMem (1 * m + i) (by omega)
      rwa [sub_ofNat_add_ofNat] at hm⟩

theorem RepneScasbDownLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScasbDownLoop s count (m + 1)) : repneScasCont 8 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.sub_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneScasCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneScasbDownLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepneScasbDownLoop s count 0) : repneScasCont 8 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.sub_zero, Nat.zero_add] at hs
  unfold repneScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneScasbDownLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScasbDownLoop s (count + 1) (m + 1)) : RepneScasbDownLoop (repneScasDownAfter 8 2 s) count m := by
  have hdb := h.dstBase
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneScasDownAfter 8 2 s).RIP = s.RIP := by
    rw [repneScasDownAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneScasDownAfter 8 2 s).RFLAGS = s.RFLAGS := by
    rw [repneScasDownAfter_rflags, hc]
    rfl
  have hd : rdi.read (repneScasDownAfter 8 2 s) = rdi.read s - BitVec.ofNat 64 1 := repneScasDownAfter_rdi 8 2 s
  have hdn : (rdi.read (repneScasDownAfter 8 2 s)).toNat = (rdi.read s).toNat - 1 := by
    rw [hd, toNat_sub_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 8).read (repneScasDownAfter 8 2 s) = (Operand.mem a : Operand 8).read s := by
    simp only [Operand.read, repneScasDownAfter_external]
  have ha := repneScasDownAfter_acc 8 2 s
  refine ⟨h.ready.repneScasDown 8 2, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneScasDownAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneScasDownAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, repneScasDownAfter_external,
      show 1 + 1 * m = 1 * (m + 1) by omega]
    exact h.dstMem i (by omega)
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, ha, hm,
      show 1 + 1 * i = 1 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hd, sub_ofNat_sub_ofNat, ha, hm,
      show 1 + 1 * m = 1 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneScasbDownDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (1 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 8).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_scasb_down_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneScasbDownLoop s count m →
      RepneScasbDownDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneScasDownAfter 8 2 s) := nextState_of_step (h.step hstride )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneScasDownAfter 8 2 s).Repeat_String_Operation = false := by
      rw [repneScasDownAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneScasDown 8 2).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneScasDownAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneScasDownAfter_rdi]
    · rw [repneScasDownAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneScasDownAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.sub_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneScasDown 8 2 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneScasDownAfter 8 2 s) := nextState_of_step (h.step hstride )
    have hc := h.cont_true
    have ih' := ih c (repneScasDownAfter 8 2 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repneScasDownAfter 8 2 s).RIP = s.RIP := by
      rw [repneScasDownAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneScasDownAfter 8 2 s).RFLAGS = s.RFLAGS := by
      rw [repneScasDownAfter_rflags, hc]
      rfl
    have ha := repneScasDownAfter_acc 8 2 s
    have hd : rdi.read (repneScasDownAfter 8 2 s) = rdi.read s - BitVec.ofNat 64 1 := repneScasDownAfter_rdi 8 2 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 8).read (repneScasDownAfter 8 2 s) = (Operand.mem a : Operand 8).read s := by
      simp only [Operand.read, repneScasDownAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, sub_ofNat_sub_ofNat, ha, hm,
        show 1 + 1 * m = 1 * (m + 1) by omega]
    · refine ((AgreesExcept.repneScasDown 8 2 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneScasbDownPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  bound : m < (rcx.read s).toNat
  dstBase : 1 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 1 ≤ 2^32
  dstMem : ∀ i < 1 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (1 * m) + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.reg 0 : Operand 8).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = (rcx.read s).toNat

def repneScasbDownEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rdi, rdi.read s - BitVec.ofNat 64 (1 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 8).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s)))

@[simp] theorem repneScasbDownEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneScasbDownEffect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repneScasbDownEffect, Effect.components]

theorem repne_scasb_down_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, 0xAE]) s) (hpre : RepneScasbDownPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, 0xAE]) t ∧ (repneScasbDownEffect p m s).Holds s t := by
  intro t
  have hloop : RepneScasbDownLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.dstBase,
      hpre.dstLow, hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_scasb_down_loop hstride m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneScasbDownEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneScasbDownEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repne_scasb_down_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepneScasbDownPre p m) (codeRange p [0xF2, 0xAE]) (Effect.post (repneScasbDownEffect p m)) :=
  fun s h hcode hpre => ⟨_, repne_scasb_down_steps hstride p m s h hcode hpre⟩

attribute [x86_compose] repneScasqDownEffect repneScasdDownEffect repneScaswDownEffect repneScasbDownEffect

@[x86_local] theorem repneScasqDownEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneScasqDownEffect p m) := by
  effect_local [repneScasqDownEffect]

@[x86_local] theorem repneScasdDownEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneScasdDownEffect p m) := by
  effect_local [repneScasdDownEffect]

@[x86_local] theorem repneScaswDownEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneScaswDownEffect p m) := by
  effect_local [repneScaswDownEffect]

@[x86_local] theorem repneScasbDownEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneScasbDownEffect p m) := by
  effect_local [repneScasbDownEffect]

end X86Proofs

