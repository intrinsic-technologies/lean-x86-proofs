import X86Proofs.Instructions.Scas.Generated.RepeDown.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

structure RepeScasqDownLoop [Bindings] (rex : UInt8) (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF3, rex, 0xAF]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  dstBase : 8 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 8 ≤ 2^32
  dstMem : ∀ i < 8 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 64).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.reg 0 : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = count

theorem RepeScasqDownLoop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepeScasqDownLoop rex s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) h.countLt

theorem RepeScasqDownLoop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState} {count m : Nat} (h : RepeScasqDownLoop rex s count m) :
    X86.Machine.step s = some (.next (repeScasDownAfter 64 3 s)) := by
  have hr := hrex.rexPrefix
  have := h.dstLow
  exact repe_scasq_down_step hstride s h.ready [0xF3, rex] (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => by
      have hm := h.dstMem (8 * m + i) (by omega)
      rwa [sub_ofNat_add_ofNat] at hm⟩

theorem RepeScasqDownLoop.cont_true [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepeScasqDownLoop rex s count (m + 1)) : repeScasCont 64 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.sub_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeScasCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeScasqDownLoop.cont_false [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepeScasqDownLoop rex s count 0) : repeScasCont 64 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.sub_zero, Nat.zero_add] at hs
  unfold repeScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeScasqDownLoop.next [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepeScasqDownLoop rex s (count + 1) (m + 1)) : RepeScasqDownLoop rex (repeScasDownAfter 64 3 s) count m := by
  have hdb := h.dstBase
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeScasDownAfter 64 3 s).RIP = s.RIP := by
    rw [repeScasDownAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeScasDownAfter 64 3 s).RFLAGS = s.RFLAGS := by
    rw [repeScasDownAfter_rflags, hc]
    rfl
  have hd : rdi.read (repeScasDownAfter 64 3 s) = rdi.read s - BitVec.ofNat 64 8 := repeScasDownAfter_rdi 64 3 s
  have hdn : (rdi.read (repeScasDownAfter 64 3 s)).toNat = (rdi.read s).toNat - 8 := by
    rw [hd, toNat_sub_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 64).read (repeScasDownAfter 64 3 s) = (Operand.mem a : Operand 64).read s := by
    simp only [Operand.read, repeScasDownAfter_external]
  have ha := repeScasDownAfter_acc 64 3 s
  refine ⟨h.ready.repeScasDown 64 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeScasDownAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeScasDownAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, repeScasDownAfter_external,
      show 8 + 8 * m = 8 * (m + 1) by omega]
    exact h.dstMem i (by omega)
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, ha, hm,
      show 8 + 8 * i = 8 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hd, sub_ofNat_sub_ofNat, ha, hm,
      show 8 + 8 * m = 8 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeScasqDownDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (8 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 64).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_scasq_down_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeScasqDownLoop rex s count m →
      RepeScasqDownDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeScasDownAfter 64 3 s) := nextState_of_step (h.step hstride hrex )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeScasDownAfter 64 3 s).Repeat_String_Operation = false := by
      rw [repeScasDownAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeScasDown 64 3).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeScasDownAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeScasDownAfter_rdi]
    · rw [repeScasDownAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeScasDownAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.sub_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeScasDown 64 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeScasDownAfter 64 3 s) := nextState_of_step (h.step hstride hrex )
    have hc := h.cont_true
    have ih' := ih c (repeScasDownAfter 64 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repeScasDownAfter 64 3 s).RIP = s.RIP := by
      rw [repeScasDownAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeScasDownAfter 64 3 s).RFLAGS = s.RFLAGS := by
      rw [repeScasDownAfter_rflags, hc]
      rfl
    have ha := repeScasDownAfter_acc 64 3 s
    have hd : rdi.read (repeScasDownAfter 64 3 s) = rdi.read s - BitVec.ofNat 64 8 := repeScasDownAfter_rdi 64 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 64).read (repeScasDownAfter 64 3 s) = (Operand.mem a : Operand 64).read s := by
      simp only [Operand.read, repeScasDownAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, sub_ofNat_sub_ofNat, ha, hm,
        show 8 + 8 * m = 8 * (m + 1) by omega]
    · refine ((AgreesExcept.repeScasDown 64 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeScasqDownPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  bound : m < (rcx.read s).toNat
  dstBase : 8 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 8 ≤ 2^32
  dstMem : ∀ i < 8 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 64).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.reg 0 : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = (rcx.read s).toNat

def repeScasqDownEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rdi, rdi.read s - BitVec.ofNat 64 (8 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 64).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (8 * m)) : Operand 64).read s)))

@[simp] theorem repeScasqDownEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeScasqDownEffect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repeScasqDownEffect, Effect.components]

theorem repe_scasq_down_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, rex, 0xAF]) s) (hpre : RepeScasqDownPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, rex, 0xAF]) t ∧ (repeScasqDownEffect p m s).Holds s t := by
  intro t
  have hloop : RepeScasqDownLoop rex s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.dstBase,
      hpre.dstLow, hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_scasq_down_loop hstride hrex m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeScasqDownEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeScasqDownEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repe_scasq_down_triple_of_bytes [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    Triple (RepeScasqDownPre p m) (codeRange p [0xF3, rex, 0xAF]) (Effect.post (repeScasqDownEffect p m)) :=
  fun s h hcode hpre => ⟨_, repe_scasq_down_steps hstride p rex hrex m s h hcode hpre⟩

theorem repe_scasq_down_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepeScasqDownPre p m) (codeRange p [0xF3, 0x48, 0xAF]) (Effect.post (repeScasqDownEffect p m)) :=
  repe_scasq_down_triple_of_bytes hstride p 0x48 (by unfold RexWPrefix; decide) m

structure RepeScasdDownLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0xAF]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  dstBase : 4 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 4 ≤ 2^32
  dstMem : ∀ i < 4 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (4 * m) + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 32).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.reg 0 : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = count

theorem RepeScasdDownLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScasdDownLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) h.countLt

theorem RepeScasdDownLoop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count m : Nat} (h : RepeScasdDownLoop s count m) :
    X86.Machine.step s = some (.next (repeScasDownAfter 32 2 s)) := by
  have := h.dstLow
  exact repe_scasd_down_step hstride s h.ready [0xF3] (by simpa using scanPrefix_f3) (by simp)
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

theorem RepeScasdDownLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScasdDownLoop s count (m + 1)) : repeScasCont 32 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.sub_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeScasCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeScasdDownLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepeScasdDownLoop s count 0) : repeScasCont 32 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.sub_zero, Nat.zero_add] at hs
  unfold repeScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeScasdDownLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScasdDownLoop s (count + 1) (m + 1)) : RepeScasdDownLoop (repeScasDownAfter 32 2 s) count m := by
  have hdb := h.dstBase
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeScasDownAfter 32 2 s).RIP = s.RIP := by
    rw [repeScasDownAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeScasDownAfter 32 2 s).RFLAGS = s.RFLAGS := by
    rw [repeScasDownAfter_rflags, hc]
    rfl
  have hd : rdi.read (repeScasDownAfter 32 2 s) = rdi.read s - BitVec.ofNat 64 4 := repeScasDownAfter_rdi 32 2 s
  have hdn : (rdi.read (repeScasDownAfter 32 2 s)).toNat = (rdi.read s).toNat - 4 := by
    rw [hd, toNat_sub_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 32).read (repeScasDownAfter 32 2 s) = (Operand.mem a : Operand 32).read s := by
    simp only [Operand.read, repeScasDownAfter_external]
  have ha := repeScasDownAfter_acc 32 2 s
  refine ⟨h.ready.repeScasDown 32 2, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeScasDownAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeScasDownAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, repeScasDownAfter_external,
      show 4 + 4 * m = 4 * (m + 1) by omega]
    exact h.dstMem i (by omega)
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, ha, hm,
      show 4 + 4 * i = 4 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hd, sub_ofNat_sub_ofNat, ha, hm,
      show 4 + 4 * m = 4 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeScasdDownDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (4 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 32).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_scasd_down_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeScasdDownLoop s count m →
      RepeScasdDownDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeScasDownAfter 32 2 s) := nextState_of_step (h.step hstride )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeScasDownAfter 32 2 s).Repeat_String_Operation = false := by
      rw [repeScasDownAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeScasDown 32 2).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeScasDownAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeScasDownAfter_rdi]
    · rw [repeScasDownAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeScasDownAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.sub_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeScasDown 32 2 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeScasDownAfter 32 2 s) := nextState_of_step (h.step hstride )
    have hc := h.cont_true
    have ih' := ih c (repeScasDownAfter 32 2 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repeScasDownAfter 32 2 s).RIP = s.RIP := by
      rw [repeScasDownAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeScasDownAfter 32 2 s).RFLAGS = s.RFLAGS := by
      rw [repeScasDownAfter_rflags, hc]
      rfl
    have ha := repeScasDownAfter_acc 32 2 s
    have hd : rdi.read (repeScasDownAfter 32 2 s) = rdi.read s - BitVec.ofNat 64 4 := repeScasDownAfter_rdi 32 2 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 32).read (repeScasDownAfter 32 2 s) = (Operand.mem a : Operand 32).read s := by
      simp only [Operand.read, repeScasDownAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, sub_ofNat_sub_ofNat, ha, hm,
        show 4 + 4 * m = 4 * (m + 1) by omega]
    · refine ((AgreesExcept.repeScasDown 32 2 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeScasdDownPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  bound : m < (rcx.read s).toNat
  dstBase : 4 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 4 ≤ 2^32
  dstMem : ∀ i < 4 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (4 * m) + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 32).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.reg 0 : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = (rcx.read s).toNat

def repeScasdDownEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rdi, rdi.read s - BitVec.ofNat 64 (4 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 32).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (4 * m)) : Operand 32).read s)))

@[simp] theorem repeScasdDownEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeScasdDownEffect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repeScasdDownEffect, Effect.components]

theorem repe_scasd_down_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0xAF]) s) (hpre : RepeScasdDownPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0xAF]) t ∧ (repeScasdDownEffect p m s).Holds s t := by
  intro t
  have hloop : RepeScasdDownLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.dstBase,
      hpre.dstLow, hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_scasd_down_loop hstride m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeScasdDownEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeScasdDownEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repe_scasd_down_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepeScasdDownPre p m) (codeRange p [0xF3, 0xAF]) (Effect.post (repeScasdDownEffect p m)) :=
  fun s h hcode hpre => ⟨_, repe_scasd_down_steps hstride p m s h hcode hpre⟩

structure RepeScaswDownLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0x66, 0xAF]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  dstBase : 2 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 2 ≤ 2^32
  dstMem : ∀ i < 2 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (2 * m) + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 16).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.reg 0 : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = count

theorem RepeScaswDownLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScaswDownLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) h.countLt

theorem RepeScaswDownLoop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count m : Nat} (h : RepeScaswDownLoop s count m) :
    X86.Machine.step s = some (.next (repeScasDownAfter 16 3 s)) := by
  have := h.dstLow
  exact repe_scasw_down_step hstride s h.ready [0xF3, 0x66] (by simp [scanPrefix_f3, scanPrefix_66]) (by simp)
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

theorem RepeScaswDownLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScaswDownLoop s count (m + 1)) : repeScasCont 16 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.sub_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeScasCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeScaswDownLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepeScaswDownLoop s count 0) : repeScasCont 16 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.sub_zero, Nat.zero_add] at hs
  unfold repeScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeScaswDownLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScaswDownLoop s (count + 1) (m + 1)) : RepeScaswDownLoop (repeScasDownAfter 16 3 s) count m := by
  have hdb := h.dstBase
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeScasDownAfter 16 3 s).RIP = s.RIP := by
    rw [repeScasDownAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeScasDownAfter 16 3 s).RFLAGS = s.RFLAGS := by
    rw [repeScasDownAfter_rflags, hc]
    rfl
  have hd : rdi.read (repeScasDownAfter 16 3 s) = rdi.read s - BitVec.ofNat 64 2 := repeScasDownAfter_rdi 16 3 s
  have hdn : (rdi.read (repeScasDownAfter 16 3 s)).toNat = (rdi.read s).toNat - 2 := by
    rw [hd, toNat_sub_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 16).read (repeScasDownAfter 16 3 s) = (Operand.mem a : Operand 16).read s := by
    simp only [Operand.read, repeScasDownAfter_external]
  have ha := repeScasDownAfter_acc 16 3 s
  refine ⟨h.ready.repeScasDown 16 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeScasDownAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeScasDownAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, repeScasDownAfter_external,
      show 2 + 2 * m = 2 * (m + 1) by omega]
    exact h.dstMem i (by omega)
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, ha, hm,
      show 2 + 2 * i = 2 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hd, sub_ofNat_sub_ofNat, ha, hm,
      show 2 + 2 * m = 2 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeScaswDownDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (2 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 16).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_scasw_down_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeScaswDownLoop s count m →
      RepeScaswDownDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeScasDownAfter 16 3 s) := nextState_of_step (h.step hstride )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeScasDownAfter 16 3 s).Repeat_String_Operation = false := by
      rw [repeScasDownAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeScasDown 16 3).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeScasDownAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeScasDownAfter_rdi]
    · rw [repeScasDownAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeScasDownAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.sub_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeScasDown 16 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeScasDownAfter 16 3 s) := nextState_of_step (h.step hstride )
    have hc := h.cont_true
    have ih' := ih c (repeScasDownAfter 16 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repeScasDownAfter 16 3 s).RIP = s.RIP := by
      rw [repeScasDownAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeScasDownAfter 16 3 s).RFLAGS = s.RFLAGS := by
      rw [repeScasDownAfter_rflags, hc]
      rfl
    have ha := repeScasDownAfter_acc 16 3 s
    have hd : rdi.read (repeScasDownAfter 16 3 s) = rdi.read s - BitVec.ofNat 64 2 := repeScasDownAfter_rdi 16 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 16).read (repeScasDownAfter 16 3 s) = (Operand.mem a : Operand 16).read s := by
      simp only [Operand.read, repeScasDownAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, sub_ofNat_sub_ofNat, ha, hm,
        show 2 + 2 * m = 2 * (m + 1) by omega]
    · refine ((AgreesExcept.repeScasDown 16 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeScaswDownPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  bound : m < (rcx.read s).toNat
  dstBase : 2 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 2 ≤ 2^32
  dstMem : ∀ i < 2 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (2 * m) + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 16).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.reg 0 : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = (rcx.read s).toNat

def repeScaswDownEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rdi, rdi.read s - BitVec.ofNat 64 (2 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 16).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (2 * m)) : Operand 16).read s)))

@[simp] theorem repeScaswDownEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeScaswDownEffect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repeScaswDownEffect, Effect.components]

theorem repe_scasw_down_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0x66, 0xAF]) s) (hpre : RepeScaswDownPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0x66, 0xAF]) t ∧ (repeScaswDownEffect p m s).Holds s t := by
  intro t
  have hloop : RepeScaswDownLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.dstBase,
      hpre.dstLow, hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_scasw_down_loop hstride m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeScaswDownEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeScaswDownEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repe_scasw_down_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepeScaswDownPre p m) (codeRange p [0xF3, 0x66, 0xAF]) (Effect.post (repeScaswDownEffect p m)) :=
  fun s h hcode hpre => ⟨_, repe_scasw_down_steps hstride p m s h hcode hpre⟩

structure RepeScasbDownLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0xAE]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  dstBase : 1 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 1 ≤ 2^32
  dstMem : ∀ i < 1 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (1 * m) + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 8).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.reg 0 : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = count

theorem RepeScasbDownLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScasbDownLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) h.countLt

theorem RepeScasbDownLoop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count m : Nat} (h : RepeScasbDownLoop s count m) :
    X86.Machine.step s = some (.next (repeScasDownAfter 8 2 s)) := by
  have := h.dstLow
  exact repe_scasb_down_step hstride s h.ready [0xF3] (by simpa using scanPrefix_f3) (by simp)
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => by
      have hm := h.dstMem (1 * m + i) (by omega)
      rwa [sub_ofNat_add_ofNat] at hm⟩

theorem RepeScasbDownLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScasbDownLoop s count (m + 1)) : repeScasCont 8 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.sub_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeScasCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeScasbDownLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepeScasbDownLoop s count 0) : repeScasCont 8 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.sub_zero, Nat.zero_add] at hs
  unfold repeScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeScasbDownLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScasbDownLoop s (count + 1) (m + 1)) : RepeScasbDownLoop (repeScasDownAfter 8 2 s) count m := by
  have hdb := h.dstBase
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeScasDownAfter 8 2 s).RIP = s.RIP := by
    rw [repeScasDownAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeScasDownAfter 8 2 s).RFLAGS = s.RFLAGS := by
    rw [repeScasDownAfter_rflags, hc]
    rfl
  have hd : rdi.read (repeScasDownAfter 8 2 s) = rdi.read s - BitVec.ofNat 64 1 := repeScasDownAfter_rdi 8 2 s
  have hdn : (rdi.read (repeScasDownAfter 8 2 s)).toNat = (rdi.read s).toNat - 1 := by
    rw [hd, toNat_sub_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 8).read (repeScasDownAfter 8 2 s) = (Operand.mem a : Operand 8).read s := by
    simp only [Operand.read, repeScasDownAfter_external]
  have ha := repeScasDownAfter_acc 8 2 s
  refine ⟨h.ready.repeScasDown 8 2, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeScasDownAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeScasDownAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, repeScasDownAfter_external,
      show 1 + 1 * m = 1 * (m + 1) by omega]
    exact h.dstMem i (by omega)
  · intro i hi
    rw [hd, sub_ofNat_sub_ofNat, ha, hm,
      show 1 + 1 * i = 1 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hd, sub_ofNat_sub_ofNat, ha, hm,
      show 1 + 1 * m = 1 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeScasbDownDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rdiAfter : rdi.read t = rdi.read s - BitVec.ofNat 64 (1 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 8).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_scasb_down_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeScasbDownLoop s count m →
      RepeScasbDownDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeScasDownAfter 8 2 s) := nextState_of_step (h.step hstride )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeScasDownAfter 8 2 s).Repeat_String_Operation = false := by
      rw [repeScasDownAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeScasDown 8 2).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeScasDownAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeScasDownAfter_rdi]
    · rw [repeScasDownAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeScasDownAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.sub_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeScasDown 8 2 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeScasDownAfter 8 2 s) := nextState_of_step (h.step hstride )
    have hc := h.cont_true
    have ih' := ih c (repeScasDownAfter 8 2 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repeScasDownAfter 8 2 s).RIP = s.RIP := by
      rw [repeScasDownAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeScasDownAfter 8 2 s).RFLAGS = s.RFLAGS := by
      rw [repeScasDownAfter_rflags, hc]
      rfl
    have ha := repeScasDownAfter_acc 8 2 s
    have hd : rdi.read (repeScasDownAfter 8 2 s) = rdi.read s - BitVec.ofNat 64 1 := repeScasDownAfter_rdi 8 2 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 8).read (repeScasDownAfter 8 2 s) = (Operand.mem a : Operand 8).read s := by
      simp only [Operand.read, repeScasDownAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, sub_ofNat_sub_ofNat, ha, hm,
        show 1 + 1 * m = 1 * (m + 1) by omega]
    · refine ((AgreesExcept.repeScasDown 8 2 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeScasbDownPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  bound : m < (rcx.read s).toNat
  dstBase : 1 * m ≤ (rdi.read s).toNat
  dstLow : (rdi.read s).toNat + 1 ≤ 2^32
  dstMem : ∀ i < 1 * (m + 1),
    (s.external[rdi.read s - BitVec.ofNat 64 (1 * m) + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 8).read s) =
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.reg 0 : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = (rcx.read s).toNat

def repeScasbDownEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rdi, rdi.read s - BitVec.ofNat 64 (1 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 8).read s)
    ((Operand.mem (rdi.read s - BitVec.ofNat 64 (1 * m)) : Operand 8).read s)))

@[simp] theorem repeScasbDownEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeScasbDownEffect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repeScasbDownEffect, Effect.components]

theorem repe_scasb_down_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0xAE]) s) (hpre : RepeScasbDownPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0xAE]) t ∧ (repeScasbDownEffect p m s).Holds s t := by
  intro t
  have hloop : RepeScasbDownLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.dstBase,
      hpre.dstLow, hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_scasb_down_loop hstride m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeScasbDownEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeScasbDownEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repe_scasb_down_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepeScasbDownPre p m) (codeRange p [0xF3, 0xAE]) (Effect.post (repeScasbDownEffect p m)) :=
  fun s h hcode hpre => ⟨_, repe_scasb_down_steps hstride p m s h hcode hpre⟩

attribute [x86_compose] repeScasqDownEffect repeScasdDownEffect repeScaswDownEffect repeScasbDownEffect

@[x86_local] theorem repeScasqDownEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeScasqDownEffect p m) := by
  effect_local [repeScasqDownEffect]

@[x86_local] theorem repeScasdDownEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeScasdDownEffect p m) := by
  effect_local [repeScasdDownEffect]

@[x86_local] theorem repeScaswDownEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeScaswDownEffect p m) := by
  effect_local [repeScaswDownEffect]

@[x86_local] theorem repeScasbDownEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeScasbDownEffect p m) := by
  effect_local [repeScasbDownEffect]

end X86Proofs

