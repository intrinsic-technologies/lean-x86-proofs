
import X86Proofs.Instructions.Scas.Generated.Repe.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

structure RepeScasqLoop [Bindings] (rex : UInt8) (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, rex, 0xAF]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  dstLow : (rdi.read s).toNat + 8 * (m + 1) ≤ 2^32
  dstMem : ∀ i < 8 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 64).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.reg 0 : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = count

theorem RepeScasqLoop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepeScasqLoop rex s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepeScasqLoop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState} {count m : Nat} (h : RepeScasqLoop rex s count m) :
    X86.Machine.step s = some (.next (repeScasAfter 64 3 s)) := by
  have hr := hrex.rexPrefix
  have := h.dstLow
  exact repe_scasq_step hstride s h.ready [0xF3, rex] (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.dstMem i (by omega)⟩

theorem RepeScasqLoop.cont_true [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepeScasqLoop rex s count (m + 1)) : repeScasCont 64 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeScasCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeScasqLoop.cont_false [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepeScasqLoop rex s count 0) : repeScasCont 64 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repeScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeScasqLoop.next [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepeScasqLoop rex s (count + 1) (m + 1)) : RepeScasqLoop rex (repeScasAfter 64 3 s) count m := by
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeScasAfter 64 3 s).RIP = s.RIP := by
    rw [repeScasAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeScasAfter 64 3 s).RFLAGS = s.RFLAGS := by
    rw [repeScasAfter_rflags, hc]
    rfl
  have hd : rdi.read (repeScasAfter 64 3 s) = rdi.read s + BitVec.ofNat 64 8 := repeScasAfter_rdi 64 3 s
  have hdn : (rdi.read (repeScasAfter 64 3 s)).toNat = (rdi.read s).toNat + 8 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 64).read (repeScasAfter 64 3 s) = (Operand.mem a : Operand 64).read s := by
    simp only [Operand.read, repeScasAfter_external]
  have ha := repeScasAfter_acc 64 3 s
  refine ⟨h.ready.repeScas 64 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeScasAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeScasAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repeScasAfter_external]
    exact h.dstMem (8 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 8 + 8 * i = 8 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 8 + 8 * m = 8 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeScasqDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (8 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 64).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_scasq_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeScasqLoop rex s count m →
      RepeScasqDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeScasAfter 64 3 s) := nextState_of_step (h.step hstride hrex )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeScasAfter 64 3 s).Repeat_String_Operation = false := by
      rw [repeScasAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeScas 64 3).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeScasAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeScasAfter_rdi]
    · rw [repeScasAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeScasAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeScas 64 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeScasAfter 64 3 s) := nextState_of_step (h.step hstride hrex )
    have hc := h.cont_true
    have ih' := ih c (repeScasAfter 64 3 s) h.next
    rw [nextStates_succ, hnext]
    have hdl := h.dstLow
    have hrip : (repeScasAfter 64 3 s).RIP = s.RIP := by
      rw [repeScasAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeScasAfter 64 3 s).RFLAGS = s.RFLAGS := by
      rw [repeScasAfter_rflags, hc]
      rfl
    have ha := repeScasAfter_acc 64 3 s
    have hd : rdi.read (repeScasAfter 64 3 s) = rdi.read s + BitVec.ofNat 64 8 := repeScasAfter_rdi 64 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 64).read (repeScasAfter 64 3 s) = (Operand.mem a : Operand 64).read s := by
      simp only [Operand.read, repeScasAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, add_ofNat_add_ofNat, ha, hm,
        show 8 + 8 * m = 8 * (m + 1) by omega]
    · refine ((AgreesExcept.repeScas 64 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeScasqPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  dstLow : (rdi.read s).toNat + 8 * (m + 1) ≤ 2^32
  dstMem : ∀ i < 8 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 64).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.reg 0 : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = (rcx.read s).toNat

def repeScasqEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (8 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 64).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)))

@[simp] theorem repeScasqEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeScasqEffect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repeScasqEffect, Effect.components]

theorem repe_scasq_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, rex, 0xAF]) s) (hpre : RepeScasqPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, rex, 0xAF]) t ∧ (repeScasqEffect p m s).Holds s t := by
  intro t
  have hloop : RepeScasqLoop rex s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.dstLow,
      hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_scasq_loop hstride hrex m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeScasqEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeScasqEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repe_scasq_triple_of_bytes [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    Triple (RepeScasqPre p m) (codeRange p [0xF3, rex, 0xAF]) (Effect.post (repeScasqEffect p m)) :=
  fun s h hcode hpre => ⟨_, repe_scasq_steps hstride p rex hrex m s h hcode hpre⟩

theorem repe_scasq_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepeScasqPre p m) (codeRange p [0xF3, 0x48, 0xAF]) (Effect.post (repeScasqEffect p m)) :=
  repe_scasq_triple_of_bytes hstride p 0x48 (by unfold RexWPrefix; decide) m

theorem repe_scasq_zero_triple_of_bytes [Bindings] (p : BitVec 64)
    (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepZeroPre p) (codeRange p [0xF3, rex, 0xAF]) (Effect.post (repZeroEffect p 3)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hr := hrex.rexPrefix
    have hcodeS : BytesAt s s.RIP [0xF3, rex, 0xAF] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repe_scasq_step_zero s h.midRep [0xF3, rex] (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp)
      (by rw [scanContext_f3_rex _ _ hr]; rfl)
      (by rw [scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
      (by rw [scanContext_f3_rex _ _ hr]; rfl)
      (by rw [scanContext_f3_rex _ _ hr]; rfl)
      (by rw [scanContext_f3_rex _ _ hr]; rfl)
      hcodeS hlow hpre.rcxZero

theorem repe_scasq_zero_triple [Bindings] (p : BitVec 64) :
    Triple (RepZeroPre p) (codeRange p [0xF3, 0x48, 0xAF]) (Effect.post (repZeroEffect p 3)) :=
  repe_scasq_zero_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide)

structure RepeScasdLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0xAF]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  dstLow : (rdi.read s).toNat + 4 * (m + 1) ≤ 2^32
  dstMem : ∀ i < 4 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 32).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.reg 0 : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = count

theorem RepeScasdLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScasdLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepeScasdLoop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count m : Nat} (h : RepeScasdLoop s count m) :
    X86.Machine.step s = some (.next (repeScasAfter 32 2 s)) := by
  have := h.dstLow
  exact repe_scasd_step hstride s h.ready [0xF3] (by simpa using scanPrefix_f3) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.dstMem i (by omega)⟩

theorem RepeScasdLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScasdLoop s count (m + 1)) : repeScasCont 32 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeScasCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeScasdLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepeScasdLoop s count 0) : repeScasCont 32 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repeScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeScasdLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScasdLoop s (count + 1) (m + 1)) : RepeScasdLoop (repeScasAfter 32 2 s) count m := by
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeScasAfter 32 2 s).RIP = s.RIP := by
    rw [repeScasAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeScasAfter 32 2 s).RFLAGS = s.RFLAGS := by
    rw [repeScasAfter_rflags, hc]
    rfl
  have hd : rdi.read (repeScasAfter 32 2 s) = rdi.read s + BitVec.ofNat 64 4 := repeScasAfter_rdi 32 2 s
  have hdn : (rdi.read (repeScasAfter 32 2 s)).toNat = (rdi.read s).toNat + 4 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 32).read (repeScasAfter 32 2 s) = (Operand.mem a : Operand 32).read s := by
    simp only [Operand.read, repeScasAfter_external]
  have ha := repeScasAfter_acc 32 2 s
  refine ⟨h.ready.repeScas 32 2, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeScasAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeScasAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repeScasAfter_external]
    exact h.dstMem (4 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 4 + 4 * i = 4 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 4 + 4 * m = 4 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeScasdDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (4 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 32).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_scasd_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeScasdLoop s count m →
      RepeScasdDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeScasAfter 32 2 s) := nextState_of_step (h.step hstride )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeScasAfter 32 2 s).Repeat_String_Operation = false := by
      rw [repeScasAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeScas 32 2).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeScasAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeScasAfter_rdi]
    · rw [repeScasAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeScasAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeScas 32 2 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeScasAfter 32 2 s) := nextState_of_step (h.step hstride )
    have hc := h.cont_true
    have ih' := ih c (repeScasAfter 32 2 s) h.next
    rw [nextStates_succ, hnext]
    have hdl := h.dstLow
    have hrip : (repeScasAfter 32 2 s).RIP = s.RIP := by
      rw [repeScasAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeScasAfter 32 2 s).RFLAGS = s.RFLAGS := by
      rw [repeScasAfter_rflags, hc]
      rfl
    have ha := repeScasAfter_acc 32 2 s
    have hd : rdi.read (repeScasAfter 32 2 s) = rdi.read s + BitVec.ofNat 64 4 := repeScasAfter_rdi 32 2 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 32).read (repeScasAfter 32 2 s) = (Operand.mem a : Operand 32).read s := by
      simp only [Operand.read, repeScasAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, add_ofNat_add_ofNat, ha, hm,
        show 4 + 4 * m = 4 * (m + 1) by omega]
    · refine ((AgreesExcept.repeScas 32 2 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeScasdPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  dstLow : (rdi.read s).toNat + 4 * (m + 1) ≤ 2^32
  dstMem : ∀ i < 4 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 32).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.reg 0 : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = (rcx.read s).toNat

def repeScasdEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (4 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 32).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)))

@[simp] theorem repeScasdEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeScasdEffect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repeScasdEffect, Effect.components]

theorem repe_scasd_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0xAF]) s) (hpre : RepeScasdPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0xAF]) t ∧ (repeScasdEffect p m s).Holds s t := by
  intro t
  have hloop : RepeScasdLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.dstLow,
      hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_scasd_loop hstride m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeScasdEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeScasdEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repe_scasd_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepeScasdPre p m) (codeRange p [0xF3, 0xAF]) (Effect.post (repeScasdEffect p m)) :=
  fun s h hcode hpre => ⟨_, repe_scasd_steps hstride p m s h hcode hpre⟩

theorem repe_scasd_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0xF3, 0xAF]) (Effect.post (repZeroEffect p 2)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0xF3, 0xAF] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repe_scasd_step_zero s h.midRep [0xF3] (by simpa using scanPrefix_f3) (by simp)
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      hcodeS hlow hpre.rcxZero

structure RepeScaswLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0x66, 0xAF]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  dstLow : (rdi.read s).toNat + 2 * (m + 1) ≤ 2^32
  dstMem : ∀ i < 2 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 16).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.reg 0 : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = count

theorem RepeScaswLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScaswLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepeScaswLoop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count m : Nat} (h : RepeScaswLoop s count m) :
    X86.Machine.step s = some (.next (repeScasAfter 16 3 s)) := by
  have := h.dstLow
  exact repe_scasw_step hstride s h.ready [0xF3, 0x66] (by simp [scanPrefix_f3, scanPrefix_66]) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.dstMem i (by omega)⟩

theorem RepeScaswLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScaswLoop s count (m + 1)) : repeScasCont 16 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeScasCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeScaswLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepeScaswLoop s count 0) : repeScasCont 16 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repeScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeScaswLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScaswLoop s (count + 1) (m + 1)) : RepeScaswLoop (repeScasAfter 16 3 s) count m := by
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeScasAfter 16 3 s).RIP = s.RIP := by
    rw [repeScasAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeScasAfter 16 3 s).RFLAGS = s.RFLAGS := by
    rw [repeScasAfter_rflags, hc]
    rfl
  have hd : rdi.read (repeScasAfter 16 3 s) = rdi.read s + BitVec.ofNat 64 2 := repeScasAfter_rdi 16 3 s
  have hdn : (rdi.read (repeScasAfter 16 3 s)).toNat = (rdi.read s).toNat + 2 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 16).read (repeScasAfter 16 3 s) = (Operand.mem a : Operand 16).read s := by
    simp only [Operand.read, repeScasAfter_external]
  have ha := repeScasAfter_acc 16 3 s
  refine ⟨h.ready.repeScas 16 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeScasAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeScasAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repeScasAfter_external]
    exact h.dstMem (2 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 2 + 2 * i = 2 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 2 + 2 * m = 2 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeScaswDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (2 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 16).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_scasw_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeScaswLoop s count m →
      RepeScaswDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeScasAfter 16 3 s) := nextState_of_step (h.step hstride )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeScasAfter 16 3 s).Repeat_String_Operation = false := by
      rw [repeScasAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeScas 16 3).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeScasAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeScasAfter_rdi]
    · rw [repeScasAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeScasAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeScas 16 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeScasAfter 16 3 s) := nextState_of_step (h.step hstride )
    have hc := h.cont_true
    have ih' := ih c (repeScasAfter 16 3 s) h.next
    rw [nextStates_succ, hnext]
    have hdl := h.dstLow
    have hrip : (repeScasAfter 16 3 s).RIP = s.RIP := by
      rw [repeScasAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeScasAfter 16 3 s).RFLAGS = s.RFLAGS := by
      rw [repeScasAfter_rflags, hc]
      rfl
    have ha := repeScasAfter_acc 16 3 s
    have hd : rdi.read (repeScasAfter 16 3 s) = rdi.read s + BitVec.ofNat 64 2 := repeScasAfter_rdi 16 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 16).read (repeScasAfter 16 3 s) = (Operand.mem a : Operand 16).read s := by
      simp only [Operand.read, repeScasAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, add_ofNat_add_ofNat, ha, hm,
        show 2 + 2 * m = 2 * (m + 1) by omega]
    · refine ((AgreesExcept.repeScas 16 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeScaswPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  dstLow : (rdi.read s).toNat + 2 * (m + 1) ≤ 2^32
  dstMem : ∀ i < 2 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 16).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.reg 0 : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = (rcx.read s).toNat

def repeScaswEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (2 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 16).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)))

@[simp] theorem repeScaswEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeScaswEffect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repeScaswEffect, Effect.components]

theorem repe_scasw_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0x66, 0xAF]) s) (hpre : RepeScaswPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0x66, 0xAF]) t ∧ (repeScaswEffect p m s).Holds s t := by
  intro t
  have hloop : RepeScaswLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.dstLow,
      hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_scasw_loop hstride m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeScaswEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeScaswEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repe_scasw_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepeScaswPre p m) (codeRange p [0xF3, 0x66, 0xAF]) (Effect.post (repeScaswEffect p m)) :=
  fun s h hcode hpre => ⟨_, repe_scasw_steps hstride p m s h hcode hpre⟩

theorem repe_scasw_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0xF3, 0x66, 0xAF]) (Effect.post (repZeroEffect p 3)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0xF3, 0x66, 0xAF] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repe_scasw_step_zero s h.midRep [0xF3, 0x66] (by simp [scanPrefix_f3, scanPrefix_66]) (by simp)
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      hcodeS hlow hpre.rcxZero

structure RepeScasbLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0xAE]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  dstLow : (rdi.read s).toNat + 1 * (m + 1) ≤ 2^32
  dstMem : ∀ i < 1 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 8).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.reg 0 : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = count

theorem RepeScasbLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScasbLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepeScasbLoop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count m : Nat} (h : RepeScasbLoop s count m) :
    X86.Machine.step s = some (.next (repeScasAfter 8 2 s)) := by
  have := h.dstLow
  exact repe_scasb_step hstride s h.ready [0xF3] (by simpa using scanPrefix_f3) (by simp)
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.dstMem i (by omega)⟩

theorem RepeScasbLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScasbLoop s count (m + 1)) : repeScasCont 8 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeScasCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeScasbLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepeScasbLoop s count 0) : repeScasCont 8 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repeScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeScasbLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScasbLoop s (count + 1) (m + 1)) : RepeScasbLoop (repeScasAfter 8 2 s) count m := by
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeScasAfter 8 2 s).RIP = s.RIP := by
    rw [repeScasAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeScasAfter 8 2 s).RFLAGS = s.RFLAGS := by
    rw [repeScasAfter_rflags, hc]
    rfl
  have hd : rdi.read (repeScasAfter 8 2 s) = rdi.read s + BitVec.ofNat 64 1 := repeScasAfter_rdi 8 2 s
  have hdn : (rdi.read (repeScasAfter 8 2 s)).toNat = (rdi.read s).toNat + 1 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 8).read (repeScasAfter 8 2 s) = (Operand.mem a : Operand 8).read s := by
    simp only [Operand.read, repeScasAfter_external]
  have ha := repeScasAfter_acc 8 2 s
  refine ⟨h.ready.repeScas 8 2, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeScasAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeScasAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repeScasAfter_external]
    exact h.dstMem (1 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 1 + 1 * i = 1 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 1 + 1 * m = 1 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeScasbDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (1 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 8).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_scasb_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeScasbLoop s count m →
      RepeScasbDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeScasAfter 8 2 s) := nextState_of_step (h.step hstride )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeScasAfter 8 2 s).Repeat_String_Operation = false := by
      rw [repeScasAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeScas 8 2).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeScasAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeScasAfter_rdi]
    · rw [repeScasAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeScasAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeScas 8 2 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeScasAfter 8 2 s) := nextState_of_step (h.step hstride )
    have hc := h.cont_true
    have ih' := ih c (repeScasAfter 8 2 s) h.next
    rw [nextStates_succ, hnext]
    have hdl := h.dstLow
    have hrip : (repeScasAfter 8 2 s).RIP = s.RIP := by
      rw [repeScasAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeScasAfter 8 2 s).RFLAGS = s.RFLAGS := by
      rw [repeScasAfter_rflags, hc]
      rfl
    have ha := repeScasAfter_acc 8 2 s
    have hd : rdi.read (repeScasAfter 8 2 s) = rdi.read s + BitVec.ofNat 64 1 := repeScasAfter_rdi 8 2 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 8).read (repeScasAfter 8 2 s) = (Operand.mem a : Operand 8).read s := by
      simp only [Operand.read, repeScasAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, add_ofNat_add_ofNat, ha, hm,
        show 1 + 1 * m = 1 * (m + 1) by omega]
    · refine ((AgreesExcept.repeScas 8 2 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeScasbPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  dstLow : (rdi.read s).toNat + 1 * (m + 1) ≤ 2^32
  dstMem : ∀ i < 1 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 8).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.reg 0 : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = (rcx.read s).toNat

def repeScasbEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (1 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 8).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)))

@[simp] theorem repeScasbEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeScasbEffect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repeScasbEffect, Effect.components]

theorem repe_scasb_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0xAE]) s) (hpre : RepeScasbPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0xAE]) t ∧ (repeScasbEffect p m s).Holds s t := by
  intro t
  have hloop : RepeScasbLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.dstLow,
      hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_scasb_loop hstride m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeScasbEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeScasbEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repe_scasb_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepeScasbPre p m) (codeRange p [0xF3, 0xAE]) (Effect.post (repeScasbEffect p m)) :=
  fun s h hcode hpre => ⟨_, repe_scasb_steps hstride p m s h hcode hpre⟩

theorem repe_scasb_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0xF3, 0xAE]) (Effect.post (repZeroEffect p 2)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0xF3, 0xAE] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repe_scasb_step_zero s h.midRep [0xF3] (by simpa using scanPrefix_f3) (by simp)
      rfl
      rfl
      rfl
      rfl
      hcodeS hlow hpre.rcxZero

structure RepeScasqA32Loop [Bindings] (rex : UInt8) (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF3, rex, 0xAF]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^32
  bound : m < count
  dstLow : (rdi.read s).toNat + 8 * (m + 1) < 2^32
  dstMem : ∀ i < 8 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 64).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.reg 0 : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = count

theorem RepeScasqA32Loop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepeScasqA32Loop rex s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepeScasqA32Loop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState} {count m : Nat} (h : RepeScasqA32Loop rex s count m) :
    X86.Machine.step s = some (.next (repeScasAfter 64 4 s)) := by
  have hr := hrex.rexPrefix
  have := h.dstLow
  exact repe_scasq_a32_step hstride s h.ready [0x67, 0xF3, rex] (scanPrefix_asz_cons (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.dstMem i (by omega)⟩
    (by omega)
    (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.countLt; omega)]; exact h.countLt)

theorem RepeScasqA32Loop.cont_true [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepeScasqA32Loop rex s count (m + 1)) : repeScasCont 64 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeScasCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeScasqA32Loop.cont_false [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepeScasqA32Loop rex s count 0) : repeScasCont 64 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repeScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeScasqA32Loop.next [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepeScasqA32Loop rex s (count + 1) (m + 1)) : RepeScasqA32Loop rex (repeScasAfter 64 4 s) count m := by
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeScasAfter 64 4 s).RIP = s.RIP := by
    rw [repeScasAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeScasAfter 64 4 s).RFLAGS = s.RFLAGS := by
    rw [repeScasAfter_rflags, hc]
    rfl
  have hd : rdi.read (repeScasAfter 64 4 s) = rdi.read s + BitVec.ofNat 64 8 := repeScasAfter_rdi 64 4 s
  have hdn : (rdi.read (repeScasAfter 64 4 s)).toNat = (rdi.read s).toNat + 8 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 64).read (repeScasAfter 64 4 s) = (Operand.mem a : Operand 64).read s := by
    simp only [Operand.read, repeScasAfter_external]
  have ha := repeScasAfter_acc 64 4 s
  refine ⟨h.ready.repeScas 64 4, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeScasAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeScasAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repeScasAfter_external]
    exact h.dstMem (8 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 8 + 8 * i = 8 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 8 + 8 * m = 8 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeScasqA32Done [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 4)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (8 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 64).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_scasq_a32_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeScasqA32Loop rex s count m →
      RepeScasqA32Done s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeScasAfter 64 4 s) := nextState_of_step (h.step hstride hrex )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeScasAfter 64 4 s).Repeat_String_Operation = false := by
      rw [repeScasAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeScas 64 4).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeScasAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeScasAfter_rdi]
    · rw [repeScasAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeScasAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeScas 64 4 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeScasAfter 64 4 s) := nextState_of_step (h.step hstride hrex )
    have hc := h.cont_true
    have ih' := ih c (repeScasAfter 64 4 s) h.next
    rw [nextStates_succ, hnext]
    have hdl := h.dstLow
    have hrip : (repeScasAfter 64 4 s).RIP = s.RIP := by
      rw [repeScasAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeScasAfter 64 4 s).RFLAGS = s.RFLAGS := by
      rw [repeScasAfter_rflags, hc]
      rfl
    have ha := repeScasAfter_acc 64 4 s
    have hd : rdi.read (repeScasAfter 64 4 s) = rdi.read s + BitVec.ofNat 64 8 := repeScasAfter_rdi 64 4 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 64).read (repeScasAfter 64 4 s) = (Operand.mem a : Operand 64).read s := by
      simp only [Operand.read, repeScasAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, add_ofNat_add_ofNat, ha, hm,
        show 8 + 8 * m = 8 * (m + 1) by omega]
    · refine ((AgreesExcept.repeScas 64 4 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeScasqA32Pre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  rcxLow : (rcx.read s).toNat < 2^32
  dstLow : (rdi.read s).toNat + 8 * (m + 1) < 2^32
  dstMem : ∀ i < 8 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 64).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.reg 0 : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = (rcx.read s).toNat

def repeScasqA32Effect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 4
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (8 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 64).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)))

@[simp] theorem repeScasqA32Effect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeScasqA32Effect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repeScasqA32Effect, Effect.components]

theorem repe_scasq_a32_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF3, rex, 0xAF]) s) (hpre : RepeScasqA32Pre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF3, rex, 0xAF]) t ∧ (repeScasqA32Effect p m s).Holds s t := by
  intro t
  have hloop : RepeScasqA32Loop rex s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hpre.rcxLow, hpre.bound, hpre.dstLow,
      hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_scasq_a32_loop hstride hrex m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeScasqA32Effect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeScasqA32Effect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repe_scasq_a32_triple_of_bytes [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    Triple (RepeScasqA32Pre p m) (codeRange p [0x67, 0xF3, rex, 0xAF]) (Effect.post (repeScasqA32Effect p m)) :=
  fun s h hcode hpre => ⟨_, repe_scasq_a32_steps hstride p rex hrex m s h hcode hpre⟩

theorem repe_scasq_a32_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepeScasqA32Pre p m) (codeRange p [0x67, 0xF3, 0x48, 0xAF]) (Effect.post (repeScasqA32Effect p m)) :=
  repe_scasq_a32_triple_of_bytes hstride p 0x48 (by unfold RexWPrefix; decide) m

theorem repe_scasq_a32_zero_triple_of_bytes [Bindings] (p : BitVec 64)
    (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepZeroPre p) (codeRange p [0x67, 0xF3, rex, 0xAF]) (Effect.post (repZeroEffect p 4)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hr := hrex.rexPrefix
    have hcodeS : BytesAt s s.RIP [0x67, 0xF3, rex, 0xAF] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repe_scasq_a32_step_zero s h.midRep [0x67, 0xF3, rex] (scanPrefix_asz_cons (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp)
      (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
      (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
      (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
      (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
      (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
      hcodeS hlow hpre.rcxZero

theorem repe_scasq_a32_zero_triple [Bindings] (p : BitVec 64) :
    Triple (RepZeroPre p) (codeRange p [0x67, 0xF3, 0x48, 0xAF]) (Effect.post (repZeroEffect p 4)) :=
  repe_scasq_a32_zero_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide)

structure RepeScasdA32Loop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF3, 0xAF]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^32
  bound : m < count
  dstLow : (rdi.read s).toNat + 4 * (m + 1) < 2^32
  dstMem : ∀ i < 4 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 32).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.reg 0 : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = count

theorem RepeScasdA32Loop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScasdA32Loop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepeScasdA32Loop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count m : Nat} (h : RepeScasdA32Loop s count m) :
    X86.Machine.step s = some (.next (repeScasAfter 32 3 s)) := by
  have := h.dstLow
  exact repe_scasd_a32_step hstride s h.ready [0x67, 0xF3] (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.dstMem i (by omega)⟩
    (by omega)
    (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.countLt; omega)]; exact h.countLt)

theorem RepeScasdA32Loop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScasdA32Loop s count (m + 1)) : repeScasCont 32 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeScasCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeScasdA32Loop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepeScasdA32Loop s count 0) : repeScasCont 32 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repeScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeScasdA32Loop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScasdA32Loop s (count + 1) (m + 1)) : RepeScasdA32Loop (repeScasAfter 32 3 s) count m := by
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeScasAfter 32 3 s).RIP = s.RIP := by
    rw [repeScasAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeScasAfter 32 3 s).RFLAGS = s.RFLAGS := by
    rw [repeScasAfter_rflags, hc]
    rfl
  have hd : rdi.read (repeScasAfter 32 3 s) = rdi.read s + BitVec.ofNat 64 4 := repeScasAfter_rdi 32 3 s
  have hdn : (rdi.read (repeScasAfter 32 3 s)).toNat = (rdi.read s).toNat + 4 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 32).read (repeScasAfter 32 3 s) = (Operand.mem a : Operand 32).read s := by
    simp only [Operand.read, repeScasAfter_external]
  have ha := repeScasAfter_acc 32 3 s
  refine ⟨h.ready.repeScas 32 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeScasAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeScasAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repeScasAfter_external]
    exact h.dstMem (4 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 4 + 4 * i = 4 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 4 + 4 * m = 4 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeScasdA32Done [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (4 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 32).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_scasd_a32_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeScasdA32Loop s count m →
      RepeScasdA32Done s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeScasAfter 32 3 s) := nextState_of_step (h.step hstride )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeScasAfter 32 3 s).Repeat_String_Operation = false := by
      rw [repeScasAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeScas 32 3).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeScasAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeScasAfter_rdi]
    · rw [repeScasAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeScasAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeScas 32 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeScasAfter 32 3 s) := nextState_of_step (h.step hstride )
    have hc := h.cont_true
    have ih' := ih c (repeScasAfter 32 3 s) h.next
    rw [nextStates_succ, hnext]
    have hdl := h.dstLow
    have hrip : (repeScasAfter 32 3 s).RIP = s.RIP := by
      rw [repeScasAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeScasAfter 32 3 s).RFLAGS = s.RFLAGS := by
      rw [repeScasAfter_rflags, hc]
      rfl
    have ha := repeScasAfter_acc 32 3 s
    have hd : rdi.read (repeScasAfter 32 3 s) = rdi.read s + BitVec.ofNat 64 4 := repeScasAfter_rdi 32 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 32).read (repeScasAfter 32 3 s) = (Operand.mem a : Operand 32).read s := by
      simp only [Operand.read, repeScasAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, add_ofNat_add_ofNat, ha, hm,
        show 4 + 4 * m = 4 * (m + 1) by omega]
    · refine ((AgreesExcept.repeScas 32 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeScasdA32Pre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  rcxLow : (rcx.read s).toNat < 2^32
  dstLow : (rdi.read s).toNat + 4 * (m + 1) < 2^32
  dstMem : ∀ i < 4 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 32).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.reg 0 : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = (rcx.read s).toNat

def repeScasdA32Effect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (4 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 32).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)))

@[simp] theorem repeScasdA32Effect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeScasdA32Effect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repeScasdA32Effect, Effect.components]

theorem repe_scasd_a32_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF3, 0xAF]) s) (hpre : RepeScasdA32Pre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF3, 0xAF]) t ∧ (repeScasdA32Effect p m s).Holds s t := by
  intro t
  have hloop : RepeScasdA32Loop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hpre.rcxLow, hpre.bound, hpre.dstLow,
      hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_scasd_a32_loop hstride m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeScasdA32Effect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeScasdA32Effect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repe_scasd_a32_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepeScasdA32Pre p m) (codeRange p [0x67, 0xF3, 0xAF]) (Effect.post (repeScasdA32Effect p m)) :=
  fun s h hcode hpre => ⟨_, repe_scasd_a32_steps hstride p m s h hcode hpre⟩

theorem repe_scasd_a32_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0x67, 0xF3, 0xAF]) (Effect.post (repZeroEffect p 3)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0x67, 0xF3, 0xAF] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repe_scasd_a32_step_zero s h.midRep [0x67, 0xF3] (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      hcodeS hlow hpre.rcxZero

structure RepeScaswA32Loop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF3, 0x66, 0xAF]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^32
  bound : m < count
  dstLow : (rdi.read s).toNat + 2 * (m + 1) < 2^32
  dstMem : ∀ i < 2 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 16).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.reg 0 : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = count

theorem RepeScaswA32Loop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScaswA32Loop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepeScaswA32Loop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count m : Nat} (h : RepeScaswA32Loop s count m) :
    X86.Machine.step s = some (.next (repeScasAfter 16 4 s)) := by
  have := h.dstLow
  exact repe_scasw_a32_step hstride s h.ready [0x67, 0xF3, 0x66] (scanPrefix_asz_cons (by simp [scanPrefix_f3, scanPrefix_66])) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.dstMem i (by omega)⟩
    (by omega)
    (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.countLt; omega)]; exact h.countLt)

theorem RepeScaswA32Loop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScaswA32Loop s count (m + 1)) : repeScasCont 16 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeScasCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeScaswA32Loop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepeScaswA32Loop s count 0) : repeScasCont 16 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repeScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeScaswA32Loop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScaswA32Loop s (count + 1) (m + 1)) : RepeScaswA32Loop (repeScasAfter 16 4 s) count m := by
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeScasAfter 16 4 s).RIP = s.RIP := by
    rw [repeScasAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeScasAfter 16 4 s).RFLAGS = s.RFLAGS := by
    rw [repeScasAfter_rflags, hc]
    rfl
  have hd : rdi.read (repeScasAfter 16 4 s) = rdi.read s + BitVec.ofNat 64 2 := repeScasAfter_rdi 16 4 s
  have hdn : (rdi.read (repeScasAfter 16 4 s)).toNat = (rdi.read s).toNat + 2 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 16).read (repeScasAfter 16 4 s) = (Operand.mem a : Operand 16).read s := by
    simp only [Operand.read, repeScasAfter_external]
  have ha := repeScasAfter_acc 16 4 s
  refine ⟨h.ready.repeScas 16 4, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeScasAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeScasAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repeScasAfter_external]
    exact h.dstMem (2 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 2 + 2 * i = 2 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 2 + 2 * m = 2 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeScaswA32Done [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 4)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (2 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 16).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_scasw_a32_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeScaswA32Loop s count m →
      RepeScaswA32Done s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeScasAfter 16 4 s) := nextState_of_step (h.step hstride )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeScasAfter 16 4 s).Repeat_String_Operation = false := by
      rw [repeScasAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeScas 16 4).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeScasAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeScasAfter_rdi]
    · rw [repeScasAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeScasAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeScas 16 4 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeScasAfter 16 4 s) := nextState_of_step (h.step hstride )
    have hc := h.cont_true
    have ih' := ih c (repeScasAfter 16 4 s) h.next
    rw [nextStates_succ, hnext]
    have hdl := h.dstLow
    have hrip : (repeScasAfter 16 4 s).RIP = s.RIP := by
      rw [repeScasAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeScasAfter 16 4 s).RFLAGS = s.RFLAGS := by
      rw [repeScasAfter_rflags, hc]
      rfl
    have ha := repeScasAfter_acc 16 4 s
    have hd : rdi.read (repeScasAfter 16 4 s) = rdi.read s + BitVec.ofNat 64 2 := repeScasAfter_rdi 16 4 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 16).read (repeScasAfter 16 4 s) = (Operand.mem a : Operand 16).read s := by
      simp only [Operand.read, repeScasAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, add_ofNat_add_ofNat, ha, hm,
        show 2 + 2 * m = 2 * (m + 1) by omega]
    · refine ((AgreesExcept.repeScas 16 4 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeScaswA32Pre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  rcxLow : (rcx.read s).toNat < 2^32
  dstLow : (rdi.read s).toNat + 2 * (m + 1) < 2^32
  dstMem : ∀ i < 2 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 16).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.reg 0 : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = (rcx.read s).toNat

def repeScaswA32Effect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 4
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (2 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 16).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)))

@[simp] theorem repeScaswA32Effect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeScaswA32Effect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repeScaswA32Effect, Effect.components]

theorem repe_scasw_a32_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF3, 0x66, 0xAF]) s) (hpre : RepeScaswA32Pre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF3, 0x66, 0xAF]) t ∧ (repeScaswA32Effect p m s).Holds s t := by
  intro t
  have hloop : RepeScaswA32Loop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hpre.rcxLow, hpre.bound, hpre.dstLow,
      hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_scasw_a32_loop hstride m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeScaswA32Effect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeScaswA32Effect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repe_scasw_a32_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepeScaswA32Pre p m) (codeRange p [0x67, 0xF3, 0x66, 0xAF]) (Effect.post (repeScaswA32Effect p m)) :=
  fun s h hcode hpre => ⟨_, repe_scasw_a32_steps hstride p m s h hcode hpre⟩

theorem repe_scasw_a32_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0x67, 0xF3, 0x66, 0xAF]) (Effect.post (repZeroEffect p 4)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0x67, 0xF3, 0x66, 0xAF] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repe_scasw_a32_step_zero s h.midRep [0x67, 0xF3, 0x66] (scanPrefix_asz_cons (by simp [scanPrefix_f3, scanPrefix_66])) (by simp)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      hcodeS hlow hpre.rcxZero

structure RepeScasbA32Loop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF3, 0xAE]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^32
  bound : m < count
  dstLow : (rdi.read s).toNat + 1 * (m + 1) < 2^32
  dstMem : ∀ i < 1 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 8).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.reg 0 : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = count

theorem RepeScasbA32Loop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScasbA32Loop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepeScasbA32Loop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count m : Nat} (h : RepeScasbA32Loop s count m) :
    X86.Machine.step s = some (.next (repeScasAfter 8 3 s)) := by
  have := h.dstLow
  exact repe_scasb_a32_step hstride s h.ready [0x67, 0xF3] (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.dstMem i (by omega)⟩
    (by omega)
    (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.countLt; omega)]; exact h.countLt)

theorem RepeScasbA32Loop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScasbA32Loop s count (m + 1)) : repeScasCont 8 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeScasCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeScasbA32Loop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepeScasbA32Loop s count 0) : repeScasCont 8 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repeScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeScasbA32Loop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepeScasbA32Loop s (count + 1) (m + 1)) : RepeScasbA32Loop (repeScasAfter 8 3 s) count m := by
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeScasAfter 8 3 s).RIP = s.RIP := by
    rw [repeScasAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeScasAfter 8 3 s).RFLAGS = s.RFLAGS := by
    rw [repeScasAfter_rflags, hc]
    rfl
  have hd : rdi.read (repeScasAfter 8 3 s) = rdi.read s + BitVec.ofNat 64 1 := repeScasAfter_rdi 8 3 s
  have hdn : (rdi.read (repeScasAfter 8 3 s)).toNat = (rdi.read s).toNat + 1 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 8).read (repeScasAfter 8 3 s) = (Operand.mem a : Operand 8).read s := by
    simp only [Operand.read, repeScasAfter_external]
  have ha := repeScasAfter_acc 8 3 s
  refine ⟨h.ready.repeScas 8 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeScasAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeScasAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repeScasAfter_external]
    exact h.dstMem (1 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 1 + 1 * i = 1 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 1 + 1 * m = 1 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeScasbA32Done [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (1 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 8).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_scasb_a32_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeScasbA32Loop s count m →
      RepeScasbA32Done s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeScasAfter 8 3 s) := nextState_of_step (h.step hstride )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeScasAfter 8 3 s).Repeat_String_Operation = false := by
      rw [repeScasAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeScas 8 3).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeScasAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeScasAfter_rdi]
    · rw [repeScasAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeScasAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeScas 8 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeScasAfter 8 3 s) := nextState_of_step (h.step hstride )
    have hc := h.cont_true
    have ih' := ih c (repeScasAfter 8 3 s) h.next
    rw [nextStates_succ, hnext]
    have hdl := h.dstLow
    have hrip : (repeScasAfter 8 3 s).RIP = s.RIP := by
      rw [repeScasAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeScasAfter 8 3 s).RFLAGS = s.RFLAGS := by
      rw [repeScasAfter_rflags, hc]
      rfl
    have ha := repeScasAfter_acc 8 3 s
    have hd : rdi.read (repeScasAfter 8 3 s) = rdi.read s + BitVec.ofNat 64 1 := repeScasAfter_rdi 8 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 8).read (repeScasAfter 8 3 s) = (Operand.mem a : Operand 8).read s := by
      simp only [Operand.read, repeScasAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, add_ofNat_add_ofNat, ha, hm,
        show 1 + 1 * m = 1 * (m + 1) by omega]
    · refine ((AgreesExcept.repeScas 8 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeScasbA32Pre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  rcxLow : (rcx.read s).toNat < 2^32
  dstLow : (rdi.read s).toNat + 1 * (m + 1) < 2^32
  dstMem : ∀ i < 1 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.reg 0 : Operand 8).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.reg 0 : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = (rcx.read s).toNat

def repeScasbA32Effect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (1 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 8).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)))

@[simp] theorem repeScasbA32Effect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeScasbA32Effect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repeScasbA32Effect, Effect.components]

theorem repe_scasb_a32_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF3, 0xAE]) s) (hpre : RepeScasbA32Pre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF3, 0xAE]) t ∧ (repeScasbA32Effect p m s).Holds s t := by
  intro t
  have hloop : RepeScasbA32Loop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hpre.rcxLow, hpre.bound, hpre.dstLow,
      hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_scasb_a32_loop hstride m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeScasbA32Effect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeScasbA32Effect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repe_scasb_a32_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepeScasbA32Pre p m) (codeRange p [0x67, 0xF3, 0xAE]) (Effect.post (repeScasbA32Effect p m)) :=
  fun s h hcode hpre => ⟨_, repe_scasb_a32_steps hstride p m s h hcode hpre⟩

theorem repe_scasb_a32_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0x67, 0xF3, 0xAE]) (Effect.post (repZeroEffect p 3)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0x67, 0xF3, 0xAE] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repe_scasb_a32_step_zero s h.midRep [0x67, 0xF3] (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      hcodeS hlow hpre.rcxZero

attribute [x86_compose] repeScasqEffect repeScasdEffect repeScaswEffect repeScasbEffect repeScasqA32Effect repeScasdA32Effect repeScaswA32Effect repeScasbA32Effect

@[x86_local] theorem repeScasqEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeScasqEffect p m) := by
  effect_local [repeScasqEffect]

@[x86_local] theorem repeScasdEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeScasdEffect p m) := by
  effect_local [repeScasdEffect]

@[x86_local] theorem repeScaswEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeScaswEffect p m) := by
  effect_local [repeScaswEffect]

@[x86_local] theorem repeScasbEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeScasbEffect p m) := by
  effect_local [repeScasbEffect]

@[x86_local] theorem repeScasqA32Effect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeScasqA32Effect p m) := by
  effect_local [repeScasqA32Effect]

@[x86_local] theorem repeScasdA32Effect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeScasdA32Effect p m) := by
  effect_local [repeScasdA32Effect]

@[x86_local] theorem repeScaswA32Effect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeScaswA32Effect p m) := by
  effect_local [repeScaswA32Effect]

@[x86_local] theorem repeScasbA32Effect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeScasbA32Effect p m) := by
  effect_local [repeScasbA32Effect]

end X86Proofs
