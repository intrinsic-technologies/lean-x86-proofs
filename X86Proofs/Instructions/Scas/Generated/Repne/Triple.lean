
import X86Proofs.Instructions.Scas.Generated.Repne.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

structure RepneScasqLoop [Bindings] (rex : UInt8) (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF2, rex, 0xAF]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  dstLow : (rdi.read s).toNat + 8 * (m + 1) ≤ 2^32
  dstMem : ∀ i < 8 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.reg 0 : Operand 64).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = count

theorem RepneScasqLoop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepneScasqLoop rex s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepneScasqLoop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState} {count m : Nat} (h : RepneScasqLoop rex s count m) :
    X86.Machine.step s = some (.next (repneScasAfter 64 3 s)) := by
  have hr := hrex.rexPrefix
  have := h.dstLow
  exact repne_scasq_step hstride s h.ready [0xF2, rex] (by simp [scanPrefix_f2, hr.scanPrefix]) (by simp)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.dstMem i (by omega)⟩

theorem RepneScasqLoop.cont_true [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepneScasqLoop rex s count (m + 1)) : repneScasCont 64 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneScasCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneScasqLoop.cont_false [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepneScasqLoop rex s count 0) : repneScasCont 64 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repneScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneScasqLoop.next [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepneScasqLoop rex s (count + 1) (m + 1)) : RepneScasqLoop rex (repneScasAfter 64 3 s) count m := by
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneScasAfter 64 3 s).RIP = s.RIP := by
    rw [repneScasAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneScasAfter 64 3 s).RFLAGS = s.RFLAGS := by
    rw [repneScasAfter_rflags, hc]
    rfl
  have hd : rdi.read (repneScasAfter 64 3 s) = rdi.read s + BitVec.ofNat 64 8 := repneScasAfter_rdi 64 3 s
  have hdn : (rdi.read (repneScasAfter 64 3 s)).toNat = (rdi.read s).toNat + 8 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 64).read (repneScasAfter 64 3 s) = (Operand.mem a : Operand 64).read s := by
    simp only [Operand.read, repneScasAfter_external]
  have ha := repneScasAfter_acc 64 3 s
  refine ⟨h.ready.repneScas 64 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneScasAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneScasAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repneScasAfter_external]
    exact h.dstMem (8 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 8 + 8 * i = 8 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 8 + 8 * m = 8 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneScasqDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (8 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 64).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_scasq_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneScasqLoop rex s count m →
      RepneScasqDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneScasAfter 64 3 s) := nextState_of_step (h.step hstride hrex )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneScasAfter 64 3 s).Repeat_String_Operation = false := by
      rw [repneScasAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneScas 64 3).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneScasAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneScasAfter_rdi]
    · rw [repneScasAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneScasAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneScas 64 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneScasAfter 64 3 s) := nextState_of_step (h.step hstride hrex )
    have hc := h.cont_true
    have ih' := ih c (repneScasAfter 64 3 s) h.next
    rw [nextStates_succ, hnext]
    have hdl := h.dstLow
    have hrip : (repneScasAfter 64 3 s).RIP = s.RIP := by
      rw [repneScasAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneScasAfter 64 3 s).RFLAGS = s.RFLAGS := by
      rw [repneScasAfter_rflags, hc]
      rfl
    have ha := repneScasAfter_acc 64 3 s
    have hd : rdi.read (repneScasAfter 64 3 s) = rdi.read s + BitVec.ofNat 64 8 := repneScasAfter_rdi 64 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 64).read (repneScasAfter 64 3 s) = (Operand.mem a : Operand 64).read s := by
      simp only [Operand.read, repneScasAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, add_ofNat_add_ofNat, ha, hm,
        show 8 + 8 * m = 8 * (m + 1) by omega]
    · refine ((AgreesExcept.repneScas 64 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneScasqPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  dstLow : (rdi.read s).toNat + 8 * (m + 1) ≤ 2^32
  dstMem : ∀ i < 8 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.reg 0 : Operand 64).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = (rcx.read s).toNat

def repneScasqEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (8 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 64).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)))

@[simp] theorem repneScasqEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneScasqEffect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repneScasqEffect, Effect.components]

theorem repne_scasq_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, rex, 0xAF]) s) (hpre : RepneScasqPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, rex, 0xAF]) t ∧ (repneScasqEffect p m s).Holds s t := by
  intro t
  have hloop : RepneScasqLoop rex s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.dstLow,
      hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_scasq_loop hstride hrex m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneScasqEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneScasqEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repne_scasq_triple_of_bytes [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    Triple (RepneScasqPre p m) (codeRange p [0xF2, rex, 0xAF]) (Effect.post (repneScasqEffect p m)) :=
  fun s h hcode hpre => ⟨_, repne_scasq_steps hstride p rex hrex m s h hcode hpre⟩

theorem repne_scasq_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepneScasqPre p m) (codeRange p [0xF2, 0x48, 0xAF]) (Effect.post (repneScasqEffect p m)) :=
  repne_scasq_triple_of_bytes hstride p 0x48 (by unfold RexWPrefix; decide) m

theorem repne_scasq_zero_triple_of_bytes [Bindings] (p : BitVec 64)
    (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepZeroPre p) (codeRange p [0xF2, rex, 0xAF]) (Effect.post (repZeroEffect p 3)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hr := hrex.rexPrefix
    have hcodeS : BytesAt s s.RIP [0xF2, rex, 0xAF] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repne_scasq_step_zero s h.midRep [0xF2, rex] (by simp [scanPrefix_f2, hr.scanPrefix]) (by simp)
      (by rw [scanContext_f2_rex _ _ hr]; rfl)
      (by rw [scanContext_f2_rex _ _ hr]; exact hrex.rex_w s.DS)
      (by rw [scanContext_f2_rex _ _ hr]; rfl)
      (by rw [scanContext_f2_rex _ _ hr]; rfl)
      (by rw [scanContext_f2_rex _ _ hr]; rfl)
      hcodeS hlow hpre.rcxZero

theorem repne_scasq_zero_triple [Bindings] (p : BitVec 64) :
    Triple (RepZeroPre p) (codeRange p [0xF2, 0x48, 0xAF]) (Effect.post (repZeroEffect p 3)) :=
  repne_scasq_zero_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide)

structure RepneScasdLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF2, 0xAF]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  dstLow : (rdi.read s).toNat + 4 * (m + 1) ≤ 2^32
  dstMem : ∀ i < 4 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.reg 0 : Operand 32).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = count

theorem RepneScasdLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScasdLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepneScasdLoop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count m : Nat} (h : RepneScasdLoop s count m) :
    X86.Machine.step s = some (.next (repneScasAfter 32 2 s)) := by
  have := h.dstLow
  exact repne_scasd_step hstride s h.ready [0xF2] (by simpa using scanPrefix_f2) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.dstMem i (by omega)⟩

theorem RepneScasdLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScasdLoop s count (m + 1)) : repneScasCont 32 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneScasCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneScasdLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepneScasdLoop s count 0) : repneScasCont 32 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repneScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneScasdLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScasdLoop s (count + 1) (m + 1)) : RepneScasdLoop (repneScasAfter 32 2 s) count m := by
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneScasAfter 32 2 s).RIP = s.RIP := by
    rw [repneScasAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneScasAfter 32 2 s).RFLAGS = s.RFLAGS := by
    rw [repneScasAfter_rflags, hc]
    rfl
  have hd : rdi.read (repneScasAfter 32 2 s) = rdi.read s + BitVec.ofNat 64 4 := repneScasAfter_rdi 32 2 s
  have hdn : (rdi.read (repneScasAfter 32 2 s)).toNat = (rdi.read s).toNat + 4 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 32).read (repneScasAfter 32 2 s) = (Operand.mem a : Operand 32).read s := by
    simp only [Operand.read, repneScasAfter_external]
  have ha := repneScasAfter_acc 32 2 s
  refine ⟨h.ready.repneScas 32 2, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneScasAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneScasAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repneScasAfter_external]
    exact h.dstMem (4 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 4 + 4 * i = 4 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 4 + 4 * m = 4 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneScasdDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (4 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 32).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_scasd_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneScasdLoop s count m →
      RepneScasdDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneScasAfter 32 2 s) := nextState_of_step (h.step hstride )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneScasAfter 32 2 s).Repeat_String_Operation = false := by
      rw [repneScasAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneScas 32 2).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneScasAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneScasAfter_rdi]
    · rw [repneScasAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneScasAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneScas 32 2 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneScasAfter 32 2 s) := nextState_of_step (h.step hstride )
    have hc := h.cont_true
    have ih' := ih c (repneScasAfter 32 2 s) h.next
    rw [nextStates_succ, hnext]
    have hdl := h.dstLow
    have hrip : (repneScasAfter 32 2 s).RIP = s.RIP := by
      rw [repneScasAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneScasAfter 32 2 s).RFLAGS = s.RFLAGS := by
      rw [repneScasAfter_rflags, hc]
      rfl
    have ha := repneScasAfter_acc 32 2 s
    have hd : rdi.read (repneScasAfter 32 2 s) = rdi.read s + BitVec.ofNat 64 4 := repneScasAfter_rdi 32 2 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 32).read (repneScasAfter 32 2 s) = (Operand.mem a : Operand 32).read s := by
      simp only [Operand.read, repneScasAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, add_ofNat_add_ofNat, ha, hm,
        show 4 + 4 * m = 4 * (m + 1) by omega]
    · refine ((AgreesExcept.repneScas 32 2 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneScasdPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  dstLow : (rdi.read s).toNat + 4 * (m + 1) ≤ 2^32
  dstMem : ∀ i < 4 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.reg 0 : Operand 32).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = (rcx.read s).toNat

def repneScasdEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (4 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 32).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)))

@[simp] theorem repneScasdEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneScasdEffect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repneScasdEffect, Effect.components]

theorem repne_scasd_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, 0xAF]) s) (hpre : RepneScasdPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, 0xAF]) t ∧ (repneScasdEffect p m s).Holds s t := by
  intro t
  have hloop : RepneScasdLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.dstLow,
      hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_scasd_loop hstride m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneScasdEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneScasdEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repne_scasd_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepneScasdPre p m) (codeRange p [0xF2, 0xAF]) (Effect.post (repneScasdEffect p m)) :=
  fun s h hcode hpre => ⟨_, repne_scasd_steps hstride p m s h hcode hpre⟩

theorem repne_scasd_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0xF2, 0xAF]) (Effect.post (repZeroEffect p 2)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0xF2, 0xAF] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repne_scasd_step_zero s h.midRep [0xF2] (by simpa using scanPrefix_f2) (by simp)
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      hcodeS hlow hpre.rcxZero

structure RepneScaswLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF2, 0x66, 0xAF]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  dstLow : (rdi.read s).toNat + 2 * (m + 1) ≤ 2^32
  dstMem : ∀ i < 2 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.reg 0 : Operand 16).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = count

theorem RepneScaswLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScaswLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepneScaswLoop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count m : Nat} (h : RepneScaswLoop s count m) :
    X86.Machine.step s = some (.next (repneScasAfter 16 3 s)) := by
  have := h.dstLow
  exact repne_scasw_step hstride s h.ready [0xF2, 0x66] (by simp [scanPrefix_f2, scanPrefix_66]) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.dstMem i (by omega)⟩

theorem RepneScaswLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScaswLoop s count (m + 1)) : repneScasCont 16 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneScasCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneScaswLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepneScaswLoop s count 0) : repneScasCont 16 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repneScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneScaswLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScaswLoop s (count + 1) (m + 1)) : RepneScaswLoop (repneScasAfter 16 3 s) count m := by
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneScasAfter 16 3 s).RIP = s.RIP := by
    rw [repneScasAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneScasAfter 16 3 s).RFLAGS = s.RFLAGS := by
    rw [repneScasAfter_rflags, hc]
    rfl
  have hd : rdi.read (repneScasAfter 16 3 s) = rdi.read s + BitVec.ofNat 64 2 := repneScasAfter_rdi 16 3 s
  have hdn : (rdi.read (repneScasAfter 16 3 s)).toNat = (rdi.read s).toNat + 2 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 16).read (repneScasAfter 16 3 s) = (Operand.mem a : Operand 16).read s := by
    simp only [Operand.read, repneScasAfter_external]
  have ha := repneScasAfter_acc 16 3 s
  refine ⟨h.ready.repneScas 16 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneScasAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneScasAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repneScasAfter_external]
    exact h.dstMem (2 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 2 + 2 * i = 2 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 2 + 2 * m = 2 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneScaswDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (2 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 16).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_scasw_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneScaswLoop s count m →
      RepneScaswDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneScasAfter 16 3 s) := nextState_of_step (h.step hstride )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneScasAfter 16 3 s).Repeat_String_Operation = false := by
      rw [repneScasAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneScas 16 3).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneScasAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneScasAfter_rdi]
    · rw [repneScasAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneScasAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneScas 16 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneScasAfter 16 3 s) := nextState_of_step (h.step hstride )
    have hc := h.cont_true
    have ih' := ih c (repneScasAfter 16 3 s) h.next
    rw [nextStates_succ, hnext]
    have hdl := h.dstLow
    have hrip : (repneScasAfter 16 3 s).RIP = s.RIP := by
      rw [repneScasAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneScasAfter 16 3 s).RFLAGS = s.RFLAGS := by
      rw [repneScasAfter_rflags, hc]
      rfl
    have ha := repneScasAfter_acc 16 3 s
    have hd : rdi.read (repneScasAfter 16 3 s) = rdi.read s + BitVec.ofNat 64 2 := repneScasAfter_rdi 16 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 16).read (repneScasAfter 16 3 s) = (Operand.mem a : Operand 16).read s := by
      simp only [Operand.read, repneScasAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, add_ofNat_add_ofNat, ha, hm,
        show 2 + 2 * m = 2 * (m + 1) by omega]
    · refine ((AgreesExcept.repneScas 16 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneScaswPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  dstLow : (rdi.read s).toNat + 2 * (m + 1) ≤ 2^32
  dstMem : ∀ i < 2 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.reg 0 : Operand 16).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = (rcx.read s).toNat

def repneScaswEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (2 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 16).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)))

@[simp] theorem repneScaswEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneScaswEffect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repneScaswEffect, Effect.components]

theorem repne_scasw_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, 0x66, 0xAF]) s) (hpre : RepneScaswPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, 0x66, 0xAF]) t ∧ (repneScaswEffect p m s).Holds s t := by
  intro t
  have hloop : RepneScaswLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.dstLow,
      hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_scasw_loop hstride m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneScaswEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneScaswEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repne_scasw_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepneScaswPre p m) (codeRange p [0xF2, 0x66, 0xAF]) (Effect.post (repneScaswEffect p m)) :=
  fun s h hcode hpre => ⟨_, repne_scasw_steps hstride p m s h hcode hpre⟩

theorem repne_scasw_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0xF2, 0x66, 0xAF]) (Effect.post (repZeroEffect p 3)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0xF2, 0x66, 0xAF] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repne_scasw_step_zero s h.midRep [0xF2, 0x66] (by simp [scanPrefix_f2, scanPrefix_66]) (by simp)
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      hcodeS hlow hpre.rcxZero

structure RepneScasbLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF2, 0xAE]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  dstLow : (rdi.read s).toNat + 1 * (m + 1) ≤ 2^32
  dstMem : ∀ i < 1 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.reg 0 : Operand 8).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = count

theorem RepneScasbLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScasbLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepneScasbLoop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count m : Nat} (h : RepneScasbLoop s count m) :
    X86.Machine.step s = some (.next (repneScasAfter 8 2 s)) := by
  have := h.dstLow
  exact repne_scasb_step hstride s h.ready [0xF2] (by simpa using scanPrefix_f2) (by simp)
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.dstMem i (by omega)⟩

theorem RepneScasbLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScasbLoop s count (m + 1)) : repneScasCont 8 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneScasCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneScasbLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepneScasbLoop s count 0) : repneScasCont 8 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repneScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneScasbLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScasbLoop s (count + 1) (m + 1)) : RepneScasbLoop (repneScasAfter 8 2 s) count m := by
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneScasAfter 8 2 s).RIP = s.RIP := by
    rw [repneScasAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneScasAfter 8 2 s).RFLAGS = s.RFLAGS := by
    rw [repneScasAfter_rflags, hc]
    rfl
  have hd : rdi.read (repneScasAfter 8 2 s) = rdi.read s + BitVec.ofNat 64 1 := repneScasAfter_rdi 8 2 s
  have hdn : (rdi.read (repneScasAfter 8 2 s)).toNat = (rdi.read s).toNat + 1 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 8).read (repneScasAfter 8 2 s) = (Operand.mem a : Operand 8).read s := by
    simp only [Operand.read, repneScasAfter_external]
  have ha := repneScasAfter_acc 8 2 s
  refine ⟨h.ready.repneScas 8 2, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneScasAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneScasAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repneScasAfter_external]
    exact h.dstMem (1 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 1 + 1 * i = 1 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 1 + 1 * m = 1 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneScasbDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (1 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 8).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_scasb_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneScasbLoop s count m →
      RepneScasbDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneScasAfter 8 2 s) := nextState_of_step (h.step hstride )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneScasAfter 8 2 s).Repeat_String_Operation = false := by
      rw [repneScasAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneScas 8 2).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneScasAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneScasAfter_rdi]
    · rw [repneScasAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneScasAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneScas 8 2 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneScasAfter 8 2 s) := nextState_of_step (h.step hstride )
    have hc := h.cont_true
    have ih' := ih c (repneScasAfter 8 2 s) h.next
    rw [nextStates_succ, hnext]
    have hdl := h.dstLow
    have hrip : (repneScasAfter 8 2 s).RIP = s.RIP := by
      rw [repneScasAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneScasAfter 8 2 s).RFLAGS = s.RFLAGS := by
      rw [repneScasAfter_rflags, hc]
      rfl
    have ha := repneScasAfter_acc 8 2 s
    have hd : rdi.read (repneScasAfter 8 2 s) = rdi.read s + BitVec.ofNat 64 1 := repneScasAfter_rdi 8 2 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 8).read (repneScasAfter 8 2 s) = (Operand.mem a : Operand 8).read s := by
      simp only [Operand.read, repneScasAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, add_ofNat_add_ofNat, ha, hm,
        show 1 + 1 * m = 1 * (m + 1) by omega]
    · refine ((AgreesExcept.repneScas 8 2 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneScasbPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  dstLow : (rdi.read s).toNat + 1 * (m + 1) ≤ 2^32
  dstMem : ∀ i < 1 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.reg 0 : Operand 8).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = (rcx.read s).toNat

def repneScasbEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (1 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 8).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)))

@[simp] theorem repneScasbEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneScasbEffect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repneScasbEffect, Effect.components]

theorem repne_scasb_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, 0xAE]) s) (hpre : RepneScasbPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, 0xAE]) t ∧ (repneScasbEffect p m s).Holds s t := by
  intro t
  have hloop : RepneScasbLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.dstLow,
      hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_scasb_loop hstride m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneScasbEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneScasbEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repne_scasb_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepneScasbPre p m) (codeRange p [0xF2, 0xAE]) (Effect.post (repneScasbEffect p m)) :=
  fun s h hcode hpre => ⟨_, repne_scasb_steps hstride p m s h hcode hpre⟩

theorem repne_scasb_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0xF2, 0xAE]) (Effect.post (repZeroEffect p 2)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0xF2, 0xAE] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repne_scasb_step_zero s h.midRep [0xF2] (by simpa using scanPrefix_f2) (by simp)
      rfl
      rfl
      rfl
      rfl
      hcodeS hlow hpre.rcxZero

structure RepneScasqA32Loop [Bindings] (rex : UInt8) (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF2, rex, 0xAF]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^32
  bound : m < count
  dstLow : (rdi.read s).toNat + 8 * (m + 1) < 2^32
  dstMem : ∀ i < 8 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.reg 0 : Operand 64).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = count

theorem RepneScasqA32Loop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepneScasqA32Loop rex s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepneScasqA32Loop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState} {count m : Nat} (h : RepneScasqA32Loop rex s count m) :
    X86.Machine.step s = some (.next (repneScasAfter 64 4 s)) := by
  have hr := hrex.rexPrefix
  have := h.dstLow
  exact repne_scasq_a32_step hstride s h.ready [0x67, 0xF2, rex] (scanPrefix_asz_cons (by simp [scanPrefix_f2, hr.scanPrefix])) (by simp)
    (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; rfl)
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.dstMem i (by omega)⟩
    (by omega)
    (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.countLt; omega)]; exact h.countLt)

theorem RepneScasqA32Loop.cont_true [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepneScasqA32Loop rex s count (m + 1)) : repneScasCont 64 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneScasCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneScasqA32Loop.cont_false [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepneScasqA32Loop rex s count 0) : repneScasCont 64 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repneScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneScasqA32Loop.next [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepneScasqA32Loop rex s (count + 1) (m + 1)) : RepneScasqA32Loop rex (repneScasAfter 64 4 s) count m := by
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneScasAfter 64 4 s).RIP = s.RIP := by
    rw [repneScasAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneScasAfter 64 4 s).RFLAGS = s.RFLAGS := by
    rw [repneScasAfter_rflags, hc]
    rfl
  have hd : rdi.read (repneScasAfter 64 4 s) = rdi.read s + BitVec.ofNat 64 8 := repneScasAfter_rdi 64 4 s
  have hdn : (rdi.read (repneScasAfter 64 4 s)).toNat = (rdi.read s).toNat + 8 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 64).read (repneScasAfter 64 4 s) = (Operand.mem a : Operand 64).read s := by
    simp only [Operand.read, repneScasAfter_external]
  have ha := repneScasAfter_acc 64 4 s
  refine ⟨h.ready.repneScas 64 4, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneScasAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneScasAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repneScasAfter_external]
    exact h.dstMem (8 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 8 + 8 * i = 8 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 8 + 8 * m = 8 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneScasqA32Done [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 4)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (8 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 64).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_scasq_a32_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneScasqA32Loop rex s count m →
      RepneScasqA32Done s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneScasAfter 64 4 s) := nextState_of_step (h.step hstride hrex )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneScasAfter 64 4 s).Repeat_String_Operation = false := by
      rw [repneScasAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneScas 64 4).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneScasAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneScasAfter_rdi]
    · rw [repneScasAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneScasAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneScas 64 4 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneScasAfter 64 4 s) := nextState_of_step (h.step hstride hrex )
    have hc := h.cont_true
    have ih' := ih c (repneScasAfter 64 4 s) h.next
    rw [nextStates_succ, hnext]
    have hdl := h.dstLow
    have hrip : (repneScasAfter 64 4 s).RIP = s.RIP := by
      rw [repneScasAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneScasAfter 64 4 s).RFLAGS = s.RFLAGS := by
      rw [repneScasAfter_rflags, hc]
      rfl
    have ha := repneScasAfter_acc 64 4 s
    have hd : rdi.read (repneScasAfter 64 4 s) = rdi.read s + BitVec.ofNat 64 8 := repneScasAfter_rdi 64 4 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 64).read (repneScasAfter 64 4 s) = (Operand.mem a : Operand 64).read s := by
      simp only [Operand.read, repneScasAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, add_ofNat_add_ofNat, ha, hm,
        show 8 + 8 * m = 8 * (m + 1) by omega]
    · refine ((AgreesExcept.repneScas 64 4 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneScasqA32Pre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  rcxLow : (rcx.read s).toNat < 2^32
  dstLow : (rdi.read s).toNat + 8 * (m + 1) < 2^32
  dstMem : ∀ i < 8 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.reg 0 : Operand 64).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = (rcx.read s).toNat

def repneScasqA32Effect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 4
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (8 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 64).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)))

@[simp] theorem repneScasqA32Effect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneScasqA32Effect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repneScasqA32Effect, Effect.components]

theorem repne_scasq_a32_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF2, rex, 0xAF]) s) (hpre : RepneScasqA32Pre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF2, rex, 0xAF]) t ∧ (repneScasqA32Effect p m s).Holds s t := by
  intro t
  have hloop : RepneScasqA32Loop rex s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hpre.rcxLow, hpre.bound, hpre.dstLow,
      hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_scasq_a32_loop hstride hrex m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneScasqA32Effect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneScasqA32Effect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repne_scasq_a32_triple_of_bytes [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    Triple (RepneScasqA32Pre p m) (codeRange p [0x67, 0xF2, rex, 0xAF]) (Effect.post (repneScasqA32Effect p m)) :=
  fun s h hcode hpre => ⟨_, repne_scasq_a32_steps hstride p rex hrex m s h hcode hpre⟩

theorem repne_scasq_a32_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepneScasqA32Pre p m) (codeRange p [0x67, 0xF2, 0x48, 0xAF]) (Effect.post (repneScasqA32Effect p m)) :=
  repne_scasq_a32_triple_of_bytes hstride p 0x48 (by unfold RexWPrefix; decide) m

theorem repne_scasq_a32_zero_triple_of_bytes [Bindings] (p : BitVec 64)
    (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepZeroPre p) (codeRange p [0x67, 0xF2, rex, 0xAF]) (Effect.post (repZeroEffect p 4)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hr := hrex.rexPrefix
    have hcodeS : BytesAt s s.RIP [0x67, 0xF2, rex, 0xAF] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repne_scasq_a32_step_zero s h.midRep [0x67, 0xF2, rex] (scanPrefix_asz_cons (by simp [scanPrefix_f2, hr.scanPrefix])) (by simp)
      (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; rfl)
      (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; exact hrex.rex_w s.DS)
      (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; rfl)
      (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; rfl)
      (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; rfl)
      hcodeS hlow hpre.rcxZero

theorem repne_scasq_a32_zero_triple [Bindings] (p : BitVec 64) :
    Triple (RepZeroPre p) (codeRange p [0x67, 0xF2, 0x48, 0xAF]) (Effect.post (repZeroEffect p 4)) :=
  repne_scasq_a32_zero_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide)

structure RepneScasdA32Loop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF2, 0xAF]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^32
  bound : m < count
  dstLow : (rdi.read s).toNat + 4 * (m + 1) < 2^32
  dstMem : ∀ i < 4 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.reg 0 : Operand 32).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = count

theorem RepneScasdA32Loop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScasdA32Loop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepneScasdA32Loop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count m : Nat} (h : RepneScasdA32Loop s count m) :
    X86.Machine.step s = some (.next (repneScasAfter 32 3 s)) := by
  have := h.dstLow
  exact repne_scasd_a32_step hstride s h.ready [0x67, 0xF2] (scanPrefix_asz_cons (by simpa using scanPrefix_f2)) (by simp)
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

theorem RepneScasdA32Loop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScasdA32Loop s count (m + 1)) : repneScasCont 32 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneScasCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneScasdA32Loop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepneScasdA32Loop s count 0) : repneScasCont 32 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repneScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneScasdA32Loop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScasdA32Loop s (count + 1) (m + 1)) : RepneScasdA32Loop (repneScasAfter 32 3 s) count m := by
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneScasAfter 32 3 s).RIP = s.RIP := by
    rw [repneScasAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneScasAfter 32 3 s).RFLAGS = s.RFLAGS := by
    rw [repneScasAfter_rflags, hc]
    rfl
  have hd : rdi.read (repneScasAfter 32 3 s) = rdi.read s + BitVec.ofNat 64 4 := repneScasAfter_rdi 32 3 s
  have hdn : (rdi.read (repneScasAfter 32 3 s)).toNat = (rdi.read s).toNat + 4 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 32).read (repneScasAfter 32 3 s) = (Operand.mem a : Operand 32).read s := by
    simp only [Operand.read, repneScasAfter_external]
  have ha := repneScasAfter_acc 32 3 s
  refine ⟨h.ready.repneScas 32 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneScasAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneScasAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repneScasAfter_external]
    exact h.dstMem (4 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 4 + 4 * i = 4 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 4 + 4 * m = 4 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneScasdA32Done [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (4 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 32).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_scasd_a32_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneScasdA32Loop s count m →
      RepneScasdA32Done s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneScasAfter 32 3 s) := nextState_of_step (h.step hstride )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneScasAfter 32 3 s).Repeat_String_Operation = false := by
      rw [repneScasAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneScas 32 3).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneScasAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneScasAfter_rdi]
    · rw [repneScasAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneScasAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneScas 32 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneScasAfter 32 3 s) := nextState_of_step (h.step hstride )
    have hc := h.cont_true
    have ih' := ih c (repneScasAfter 32 3 s) h.next
    rw [nextStates_succ, hnext]
    have hdl := h.dstLow
    have hrip : (repneScasAfter 32 3 s).RIP = s.RIP := by
      rw [repneScasAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneScasAfter 32 3 s).RFLAGS = s.RFLAGS := by
      rw [repneScasAfter_rflags, hc]
      rfl
    have ha := repneScasAfter_acc 32 3 s
    have hd : rdi.read (repneScasAfter 32 3 s) = rdi.read s + BitVec.ofNat 64 4 := repneScasAfter_rdi 32 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 32).read (repneScasAfter 32 3 s) = (Operand.mem a : Operand 32).read s := by
      simp only [Operand.read, repneScasAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, add_ofNat_add_ofNat, ha, hm,
        show 4 + 4 * m = 4 * (m + 1) by omega]
    · refine ((AgreesExcept.repneScas 32 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneScasdA32Pre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  rcxLow : (rcx.read s).toNat < 2^32
  dstLow : (rdi.read s).toNat + 4 * (m + 1) < 2^32
  dstMem : ∀ i < 4 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.reg 0 : Operand 32).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = (rcx.read s).toNat

def repneScasdA32Effect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (4 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 32).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)))

@[simp] theorem repneScasdA32Effect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneScasdA32Effect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repneScasdA32Effect, Effect.components]

theorem repne_scasd_a32_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF2, 0xAF]) s) (hpre : RepneScasdA32Pre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF2, 0xAF]) t ∧ (repneScasdA32Effect p m s).Holds s t := by
  intro t
  have hloop : RepneScasdA32Loop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hpre.rcxLow, hpre.bound, hpre.dstLow,
      hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_scasd_a32_loop hstride m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneScasdA32Effect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneScasdA32Effect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repne_scasd_a32_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepneScasdA32Pre p m) (codeRange p [0x67, 0xF2, 0xAF]) (Effect.post (repneScasdA32Effect p m)) :=
  fun s h hcode hpre => ⟨_, repne_scasd_a32_steps hstride p m s h hcode hpre⟩

theorem repne_scasd_a32_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0x67, 0xF2, 0xAF]) (Effect.post (repZeroEffect p 3)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0x67, 0xF2, 0xAF] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repne_scasd_a32_step_zero s h.midRep [0x67, 0xF2] (scanPrefix_asz_cons (by simpa using scanPrefix_f2)) (by simp)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      hcodeS hlow hpre.rcxZero

structure RepneScaswA32Loop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF2, 0x66, 0xAF]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^32
  bound : m < count
  dstLow : (rdi.read s).toNat + 2 * (m + 1) < 2^32
  dstMem : ∀ i < 2 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.reg 0 : Operand 16).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = count

theorem RepneScaswA32Loop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScaswA32Loop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepneScaswA32Loop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count m : Nat} (h : RepneScaswA32Loop s count m) :
    X86.Machine.step s = some (.next (repneScasAfter 16 4 s)) := by
  have := h.dstLow
  exact repne_scasw_a32_step hstride s h.ready [0x67, 0xF2, 0x66] (scanPrefix_asz_cons (by simp [scanPrefix_f2, scanPrefix_66])) (by simp)
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

theorem RepneScaswA32Loop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScaswA32Loop s count (m + 1)) : repneScasCont 16 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneScasCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneScaswA32Loop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepneScaswA32Loop s count 0) : repneScasCont 16 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repneScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneScaswA32Loop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScaswA32Loop s (count + 1) (m + 1)) : RepneScaswA32Loop (repneScasAfter 16 4 s) count m := by
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneScasAfter 16 4 s).RIP = s.RIP := by
    rw [repneScasAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneScasAfter 16 4 s).RFLAGS = s.RFLAGS := by
    rw [repneScasAfter_rflags, hc]
    rfl
  have hd : rdi.read (repneScasAfter 16 4 s) = rdi.read s + BitVec.ofNat 64 2 := repneScasAfter_rdi 16 4 s
  have hdn : (rdi.read (repneScasAfter 16 4 s)).toNat = (rdi.read s).toNat + 2 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 16).read (repneScasAfter 16 4 s) = (Operand.mem a : Operand 16).read s := by
    simp only [Operand.read, repneScasAfter_external]
  have ha := repneScasAfter_acc 16 4 s
  refine ⟨h.ready.repneScas 16 4, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneScasAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneScasAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repneScasAfter_external]
    exact h.dstMem (2 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 2 + 2 * i = 2 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 2 + 2 * m = 2 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneScaswA32Done [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 4)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (2 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 16).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_scasw_a32_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneScaswA32Loop s count m →
      RepneScaswA32Done s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneScasAfter 16 4 s) := nextState_of_step (h.step hstride )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneScasAfter 16 4 s).Repeat_String_Operation = false := by
      rw [repneScasAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneScas 16 4).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneScasAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneScasAfter_rdi]
    · rw [repneScasAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneScasAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneScas 16 4 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneScasAfter 16 4 s) := nextState_of_step (h.step hstride )
    have hc := h.cont_true
    have ih' := ih c (repneScasAfter 16 4 s) h.next
    rw [nextStates_succ, hnext]
    have hdl := h.dstLow
    have hrip : (repneScasAfter 16 4 s).RIP = s.RIP := by
      rw [repneScasAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneScasAfter 16 4 s).RFLAGS = s.RFLAGS := by
      rw [repneScasAfter_rflags, hc]
      rfl
    have ha := repneScasAfter_acc 16 4 s
    have hd : rdi.read (repneScasAfter 16 4 s) = rdi.read s + BitVec.ofNat 64 2 := repneScasAfter_rdi 16 4 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 16).read (repneScasAfter 16 4 s) = (Operand.mem a : Operand 16).read s := by
      simp only [Operand.read, repneScasAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, add_ofNat_add_ofNat, ha, hm,
        show 2 + 2 * m = 2 * (m + 1) by omega]
    · refine ((AgreesExcept.repneScas 16 4 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneScaswA32Pre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  rcxLow : (rcx.read s).toNat < 2^32
  dstLow : (rdi.read s).toNat + 2 * (m + 1) < 2^32
  dstMem : ∀ i < 2 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.reg 0 : Operand 16).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = (rcx.read s).toNat

def repneScaswA32Effect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 4
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (2 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 16).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)))

@[simp] theorem repneScaswA32Effect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneScaswA32Effect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repneScaswA32Effect, Effect.components]

theorem repne_scasw_a32_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF2, 0x66, 0xAF]) s) (hpre : RepneScaswA32Pre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF2, 0x66, 0xAF]) t ∧ (repneScaswA32Effect p m s).Holds s t := by
  intro t
  have hloop : RepneScaswA32Loop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hpre.rcxLow, hpre.bound, hpre.dstLow,
      hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_scasw_a32_loop hstride m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneScaswA32Effect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneScaswA32Effect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repne_scasw_a32_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepneScaswA32Pre p m) (codeRange p [0x67, 0xF2, 0x66, 0xAF]) (Effect.post (repneScaswA32Effect p m)) :=
  fun s h hcode hpre => ⟨_, repne_scasw_a32_steps hstride p m s h hcode hpre⟩

theorem repne_scasw_a32_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0x67, 0xF2, 0x66, 0xAF]) (Effect.post (repZeroEffect p 4)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0x67, 0xF2, 0x66, 0xAF] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repne_scasw_a32_step_zero s h.midRep [0x67, 0xF2, 0x66] (scanPrefix_asz_cons (by simp [scanPrefix_f2, scanPrefix_66])) (by simp)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      hcodeS hlow hpre.rcxZero

structure RepneScasbA32Loop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF2, 0xAE]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^32
  bound : m < count
  dstLow : (rdi.read s).toNat + 1 * (m + 1) < 2^32
  dstMem : ∀ i < 1 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.reg 0 : Operand 8).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = count

theorem RepneScasbA32Loop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScasbA32Loop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepneScasbA32Loop.step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count m : Nat} (h : RepneScasbA32Loop s count m) :
    X86.Machine.step s = some (.next (repneScasAfter 8 3 s)) := by
  have := h.dstLow
  exact repne_scasb_a32_step hstride s h.ready [0x67, 0xF2] (scanPrefix_asz_cons (by simpa using scanPrefix_f2)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.dstMem i (by omega)⟩
    (by omega)
    (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.countLt; omega)]; exact h.countLt)

theorem RepneScasbA32Loop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScasbA32Loop s count (m + 1)) : repneScasCont 8 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneScasCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneScasbA32Loop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepneScasbA32Loop s count 0) : repneScasCont 8 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repneScasCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneScasbA32Loop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepneScasbA32Loop s (count + 1) (m + 1)) : RepneScasbA32Loop (repneScasAfter 8 3 s) count m := by
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneScasAfter 8 3 s).RIP = s.RIP := by
    rw [repneScasAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneScasAfter 8 3 s).RFLAGS = s.RFLAGS := by
    rw [repneScasAfter_rflags, hc]
    rfl
  have hd : rdi.read (repneScasAfter 8 3 s) = rdi.read s + BitVec.ofNat 64 1 := repneScasAfter_rdi 8 3 s
  have hdn : (rdi.read (repneScasAfter 8 3 s)).toNat = (rdi.read s).toNat + 1 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 8).read (repneScasAfter 8 3 s) = (Operand.mem a : Operand 8).read s := by
    simp only [Operand.read, repneScasAfter_external]
  have ha := repneScasAfter_acc 8 3 s
  refine ⟨h.ready.repneScas 8 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneScasAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneScasAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hdn]; omega
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repneScasAfter_external]
    exact h.dstMem (1 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 1 + 1 * i = 1 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hd, add_ofNat_add_ofNat, ha, hm,
      show 1 + 1 * m = 1 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneScasbA32Done [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (1 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.reg 0 : Operand 8).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_scasb_a32_loop [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneScasbA32Loop s count m →
      RepneScasbA32Done s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneScasAfter 8 3 s) := nextState_of_step (h.step hstride )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneScasAfter 8 3 s).Repeat_String_Operation = false := by
      rw [repneScasAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneScas 8 3).ready hflag, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneScasAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneScasAfter_rdi]
    · rw [repneScasAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneScasAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneScas 8 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneScasAfter 8 3 s) := nextState_of_step (h.step hstride )
    have hc := h.cont_true
    have ih' := ih c (repneScasAfter 8 3 s) h.next
    rw [nextStates_succ, hnext]
    have hdl := h.dstLow
    have hrip : (repneScasAfter 8 3 s).RIP = s.RIP := by
      rw [repneScasAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneScasAfter 8 3 s).RFLAGS = s.RFLAGS := by
      rw [repneScasAfter_rflags, hc]
      rfl
    have ha := repneScasAfter_acc 8 3 s
    have hd : rdi.read (repneScasAfter 8 3 s) = rdi.read s + BitVec.ofNat 64 1 := repneScasAfter_rdi 8 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 8).read (repneScasAfter 8 3 s) = (Operand.mem a : Operand 8).read s := by
      simp only [Operand.read, repneScasAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hd, add_ofNat_add_ofNat, ha, hm,
        show 1 + 1 * m = 1 * (m + 1) by omega]
    · refine ((AgreesExcept.repneScas 8 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneScasbA32Pre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  rcxLow : (rcx.read s).toNat < 2^32
  dstLow : (rdi.read s).toNat + 1 * (m + 1) < 2^32
  dstMem : ∀ i < 1 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.reg 0 : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.reg 0 : Operand 8).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = (rcx.read s).toNat

def repneScasbA32Effect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rdi, rdi.read s + BitVec.ofNat 64 (1 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 8).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)))

@[simp] theorem repneScasbA32Effect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneScasbA32Effect p m s).components = [.reg 7, .reg 1, .flags, .rip] := by
  simp [repneScasbA32Effect, Effect.components]

theorem repne_scasb_a32_steps [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF2, 0xAE]) s) (hpre : RepneScasbA32Pre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF2, 0xAE]) t ∧ (repneScasbA32Effect p m s).Holds s t := by
  intro t
  have hloop : RepneScasbA32Loop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hpre.rcxLow, hpre.bound, hpre.dstLow,
      hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_scasb_a32_loop hstride m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneScasbA32Effect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneScasbA32Effect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem repne_scasb_a32_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (m : Nat) :
    Triple (RepneScasbA32Pre p m) (codeRange p [0x67, 0xF2, 0xAE]) (Effect.post (repneScasbA32Effect p m)) :=
  fun s h hcode hpre => ⟨_, repne_scasb_a32_steps hstride p m s h hcode hpre⟩

theorem repne_scasb_a32_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0x67, 0xF2, 0xAE]) (Effect.post (repZeroEffect p 3)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0x67, 0xF2, 0xAE] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repne_scasb_a32_step_zero s h.midRep [0x67, 0xF2] (scanPrefix_asz_cons (by simpa using scanPrefix_f2)) (by simp)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      hcodeS hlow hpre.rcxZero

attribute [x86_compose] repneScasqEffect repneScasdEffect repneScaswEffect repneScasbEffect repneScasqA32Effect repneScasdA32Effect repneScaswA32Effect repneScasbA32Effect

@[x86_local] theorem repneScasqEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneScasqEffect p m) := by
  effect_local [repneScasqEffect]

@[x86_local] theorem repneScasdEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneScasdEffect p m) := by
  effect_local [repneScasdEffect]

@[x86_local] theorem repneScaswEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneScaswEffect p m) := by
  effect_local [repneScaswEffect]

@[x86_local] theorem repneScasbEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneScasbEffect p m) := by
  effect_local [repneScasbEffect]

@[x86_local] theorem repneScasqA32Effect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneScasqA32Effect p m) := by
  effect_local [repneScasqA32Effect]

@[x86_local] theorem repneScasdA32Effect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneScasdA32Effect p m) := by
  effect_local [repneScasdA32Effect]

@[x86_local] theorem repneScaswA32Effect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneScaswA32Effect p m) := by
  effect_local [repneScaswA32Effect]

@[x86_local] theorem repneScasbA32Effect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneScasbA32Effect p m) := by
  effect_local [repneScasbA32Effect]

end X86Proofs
