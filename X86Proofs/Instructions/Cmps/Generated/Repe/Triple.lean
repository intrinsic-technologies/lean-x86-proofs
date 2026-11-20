
import X86Proofs.Instructions.Cmps.Generated.Repe.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

structure RepeCmpsqLoop [Bindings] (rex : UInt8) (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, rex, 0xA7]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  srcLow : (rsi.read s).toNat + 8 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 8 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 8 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = count

theorem RepeCmpsqLoop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepeCmpsqLoop rex s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepeCmpsqLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState} {count m : Nat} (h : RepeCmpsqLoop rex s count m) :
    X86.Machine.step s = some (.next (repeCmpsAfter 64 3 s)) := by
  have hr := hrex.rexPrefix
  have := h.srcLow
  have := h.dstLow
  exact repe_cmpsq_step hcm s h.ready [0xF3, rex] (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩ ⟨by omega, fun i hi => h.dstMem i (by omega)⟩

theorem RepeCmpsqLoop.cont_true [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepeCmpsqLoop rex s count (m + 1)) : repeCmpsCont 64 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeCmpsCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeCmpsqLoop.cont_false [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepeCmpsqLoop rex s count 0) : repeCmpsCont 64 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repeCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeCmpsqLoop.next [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepeCmpsqLoop rex s (count + 1) (m + 1)) : RepeCmpsqLoop rex (repeCmpsAfter 64 3 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeCmpsAfter 64 3 s).RIP = s.RIP := by
    rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeCmpsAfter 64 3 s).RFLAGS = s.RFLAGS := by
    rw [repeCmpsAfter_rflags, hc]
    rfl
  have hs : rsi.read (repeCmpsAfter 64 3 s) = rsi.read s + BitVec.ofNat 64 8 := repeCmpsAfter_rsi 64 3 s
  have hd : rdi.read (repeCmpsAfter 64 3 s) = rdi.read s + BitVec.ofNat 64 8 := repeCmpsAfter_rdi 64 3 s
  have hsn : (rsi.read (repeCmpsAfter 64 3 s)).toNat = (rsi.read s).toNat + 8 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repeCmpsAfter 64 3 s)).toNat = (rdi.read s).toNat + 8 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 64).read (repeCmpsAfter 64 3 s) = (Operand.mem a : Operand 64).read s := by
    simp only [Operand.read, repeCmpsAfter_external]
  refine ⟨h.ready.repeCmps 64 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeCmpsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeCmpsAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repeCmpsAfter_external]
    exact h.srcMem (8 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repeCmpsAfter_external]
    exact h.dstMem (8 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 8 + 8 * i = 8 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 8 + 8 * m = 8 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeCmpsqDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (8 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (8 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_cmpsq_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeCmpsqLoop rex s count m →
      RepeCmpsqDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeCmpsAfter 64 3 s) := nextState_of_step (h.step hcm hrex )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeCmpsAfter 64 3 s).Repeat_String_Operation = false := by
      rw [repeCmpsAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeCmps 64 3).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeCmpsAfter_rsi]
    · rw [repeCmpsAfter_rdi]
    · rw [repeCmpsAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeCmpsAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeCmps 64 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeCmpsAfter 64 3 s) := nextState_of_step (h.step hcm hrex )
    have hc := h.cont_true
    have ih' := ih c (repeCmpsAfter 64 3 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repeCmpsAfter 64 3 s).RIP = s.RIP := by
      rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeCmpsAfter 64 3 s).RFLAGS = s.RFLAGS := by
      rw [repeCmpsAfter_rflags, hc]
      rfl
    have hs : rsi.read (repeCmpsAfter 64 3 s) = rsi.read s + BitVec.ofNat 64 8 := repeCmpsAfter_rsi 64 3 s
    have hd : rdi.read (repeCmpsAfter 64 3 s) = rdi.read s + BitVec.ofNat 64 8 := repeCmpsAfter_rdi 64 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 64).read (repeCmpsAfter 64 3 s) = (Operand.mem a : Operand 64).read s := by
      simp only [Operand.read, repeCmpsAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 8 + 8 * m = 8 * (m + 1) by omega]
    · refine ((AgreesExcept.repeCmps 64 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeCmpsqPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  srcLow : (rsi.read s).toNat + 8 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 8 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 8 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = (rcx.read s).toNat

def repeCmpsqEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (8 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (8 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)))

@[simp] theorem repeCmpsqEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeCmpsqEffect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repeCmpsqEffect, Effect.components]

theorem repe_cmpsq_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, rex, 0xA7]) s) (hpre : RepeCmpsqPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, rex, 0xA7]) t ∧ (repeCmpsqEffect p m s).Holds s t := by
  intro t
  have hloop : RepeCmpsqLoop rex s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_cmpsq_loop hcm hrex m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeCmpsqEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeCmpsqEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repe_cmpsq_triple_of_bytes [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    Triple (RepeCmpsqPre p m) (codeRange p [0xF3, rex, 0xA7]) (Effect.post (repeCmpsqEffect p m)) :=
  fun s h hcode hpre => ⟨_, repe_cmpsq_steps hcm p rex hrex m s h hcode hpre⟩

theorem repe_cmpsq_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepeCmpsqPre p m) (codeRange p [0xF3, 0x48, 0xA7]) (Effect.post (repeCmpsqEffect p m)) :=
  repe_cmpsq_triple_of_bytes hcm p 0x48 (by unfold RexWPrefix; decide) m

structure RepeCmpsqSegLoop [Bindings] (r : SegReg) (base : BitVec 64) (rex : UInt8) (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF3, rex, 0xA7]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  srcLow : (base + rsi.read s).toNat + 8 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 8 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 8 * (m + 1), (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = count
  seg : r.Ready base s

theorem RepeCmpsqSegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepeCmpsqSegLoop r base rex s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepeCmpsqSegLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {r : SegReg} {base : BitVec 64} {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState} {count m : Nat} (h : RepeCmpsqSegLoop r base rex s count m) :
    X86.Machine.step s = some (.next (repeCmpsSegAfter base 64 4 s)) := by
  have hr := hrex.rexPrefix
  have := h.srcLow
  have := h.dstLow
  have hsrc : MemReadable s (base + rsi.read s) 8 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3, rex] =
      withSeg (repRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3, rex] (noSegPrefix_cons noSegPrefix_f3 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_f3_rex _ _ hr]
  have hstep := repe_cmpsq_seg_step hcm s h.ready [r.prefixByte, 0xF3, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hrex.rex_w s.DS)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    h.df h.code h.codeLow h.rcx_ne (by rw [hsc]; exact hsrc)
    ⟨by omega, fun i hi => h.dstMem i (by omega)⟩
  rw [hsc] at hstep
  exact hstep

theorem RepeCmpsqSegLoop.cont_true [Bindings] {r : SegReg} {base : BitVec 64} {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepeCmpsqSegLoop r base rex s count (m + 1)) : repeCmpsSegCont base 64 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeCmpsSegCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeCmpsqSegLoop.cont_false [Bindings] {r : SegReg} {base : BitVec 64} {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepeCmpsqSegLoop r base rex s count 0) : repeCmpsSegCont base 64 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repeCmpsSegCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeCmpsqSegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepeCmpsqSegLoop r base rex s (count + 1) (m + 1)) : RepeCmpsqSegLoop r base rex (repeCmpsSegAfter base 64 4 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeCmpsSegAfter base 64 4 s).RIP = s.RIP := by
    rw [repeCmpsSegAfter_rip base _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeCmpsSegAfter base 64 4 s).RFLAGS = s.RFLAGS := by
    rw [repeCmpsSegAfter_rflags, hc]
    rfl
  have hs : base + rsi.read (repeCmpsSegAfter base 64 4 s) = base + rsi.read s + BitVec.ofNat 64 8 := by
    rw [repeCmpsSegAfter_rsi base 64 4 s, BitVec.add_assoc]
  have hd : rdi.read (repeCmpsSegAfter base 64 4 s) = rdi.read s + BitVec.ofNat 64 8 := repeCmpsSegAfter_rdi base 64 4 s
  have hsn : (base + rsi.read (repeCmpsSegAfter base 64 4 s)).toNat = (base + rsi.read s).toNat + 8 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repeCmpsSegAfter base 64 4 s)).toNat = (rdi.read s).toNat + 8 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 64).read (repeCmpsSegAfter base 64 4 s) = (Operand.mem a : Operand 64).read s := by
    simp only [Operand.read, repeCmpsSegAfter_external]
  refine ⟨h.ready.repeCmpsSeg base 64 4, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    repeCmpsSegAfter_segReady base 64 4 s h.seg⟩
  · intro i hi
    rw [hrip, repeCmpsSegAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeCmpsSegAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repeCmpsSegAfter_external]
    exact h.srcMem (8 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repeCmpsSegAfter_external]
    exact h.dstMem (8 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 8 + 8 * i = 8 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 8 + 8 * m = 8 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeCmpsqSegDone [Bindings] (base : BitVec 64) (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 4)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (8 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (8 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_cmpsq_seg_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {r : SegReg} {base : BitVec 64} {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeCmpsqSegLoop r base rex s count m →
      RepeCmpsqSegDone base s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeCmpsSegAfter base 64 4 s) := nextState_of_step (h.step hcm hrex )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeCmpsSegAfter base 64 4 s).Repeat_String_Operation = false := by
      rw [repeCmpsSegAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeCmpsSeg base 64 4).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeCmpsSegAfter_rip base _ _ s h.ready.msr, hc]; rfl
    · rw [repeCmpsSegAfter_rsi]
    · rw [repeCmpsSegAfter_rdi]
    · rw [repeCmpsSegAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeCmpsSegAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeCmpsSeg base 64 4 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeCmpsSegAfter base 64 4 s) := nextState_of_step (h.step hcm hrex )
    have hc := h.cont_true
    have ih' := ih c (repeCmpsSegAfter base 64 4 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repeCmpsSegAfter base 64 4 s).RIP = s.RIP := by
      rw [repeCmpsSegAfter_rip base _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeCmpsSegAfter base 64 4 s).RFLAGS = s.RFLAGS := by
      rw [repeCmpsSegAfter_rflags, hc]
      rfl
    have hsreg : rsi.read (repeCmpsSegAfter base 64 4 s) = rsi.read s + BitVec.ofNat 64 8 :=
      repeCmpsSegAfter_rsi base 64 4 s
    have hs : base + rsi.read (repeCmpsSegAfter base 64 4 s) = base + rsi.read s + BitVec.ofNat 64 8 := by
      rw [hsreg, BitVec.add_assoc]
    have hd : rdi.read (repeCmpsSegAfter base 64 4 s) = rdi.read s + BitVec.ofNat 64 8 := repeCmpsSegAfter_rdi base 64 4 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 64).read (repeCmpsSegAfter base 64 4 s) = (Operand.mem a : Operand 64).read s := by
      simp only [Operand.read, repeCmpsSegAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hsreg, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 8 + 8 * m = 8 * (m + 1) by omega]
    · refine ((AgreesExcept.repeCmpsSeg base 64 4 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeCmpsqSegPre (p : BitVec 64) (r : SegReg) (base : BitVec 64) (m : Nat)
    (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  srcLow : (base + rsi.read s).toNat + 8 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 8 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 8 * (m + 1), (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = (rcx.read s).toNat
  seg : r.Ready base s

def repeCmpsqSegEffect (p base : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 4
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (8 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (8 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)))

@[simp] theorem repeCmpsqSegEffect_components (p base : BitVec 64) (m : Nat) (s : RamState) :
    (repeCmpsqSegEffect p base m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repeCmpsqSegEffect, Effect.components]

theorem repe_cmpsq_seg_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF3, rex, 0xA7]) s) (hpre : RepeCmpsqSegPre p r base m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF3, rex, 0xA7]) t ∧ (repeCmpsqSegEffect p base m s).Holds s t := by
  intro t
  have hloop : RepeCmpsqSegLoop r base rex s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.equal, hpre.stop, hpre.seg⟩
  have hd := repe_cmpsq_seg_loop hcm hrex m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeCmpsqSegEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeCmpsqSegEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repe_cmpsq_seg_triple_of_bytes [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    Triple (RepeCmpsqSegPre p r base m) (codeRange p [r.prefixByte, 0xF3, rex, 0xA7]) (Effect.post (repeCmpsqSegEffect p base m)) :=
  fun s h hcode hpre => ⟨_, repe_cmpsq_seg_steps hcm p r base rex hrex m s h hcode hpre⟩

theorem repe_cmpsq_seg_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (m : Nat) :
    Triple (RepeCmpsqSegPre p r base m) (codeRange p [r.prefixByte, 0xF3, 0x48, 0xA7]) (Effect.post (repeCmpsqSegEffect p base m)) :=
  repe_cmpsq_seg_triple_of_bytes hcm p r base 0x48 (by unfold RexWPrefix; decide) m

theorem repe_cmpsq_zero_triple_of_bytes [Bindings] (p : BitVec 64)
    (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepZeroPre p) (codeRange p [0xF3, rex, 0xA7]) (Effect.post (repZeroEffect p 3)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hr := hrex.rexPrefix
    have hcodeS : BytesAt s s.RIP [0xF3, rex, 0xA7] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repe_cmpsq_step_zero s h.midRep [0xF3, rex] (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp)
      (by rw [scanContext_f3_rex _ _ hr]; rfl)
      (by rw [scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
      (by rw [scanContext_f3_rex _ _ hr]; rfl)
      (by rw [scanContext_f3_rex _ _ hr]; rfl)
      (by rw [scanContext_f3_rex _ _ hr]; rfl)
      (by rw [scanContext_f3_rex _ _ hr]; rfl)
      hcodeS hlow hpre.rcxZero

theorem repe_cmpsq_zero_triple [Bindings] (p : BitVec 64) :
    Triple (RepZeroPre p) (codeRange p [0xF3, 0x48, 0xA7]) (Effect.post (repZeroEffect p 3)) :=
  repe_cmpsq_zero_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide)

theorem repe_cmpsq_seg_zero_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepZeroPre p) (codeRange p [r.prefixByte, 0xF3, rex, 0xA7]) (Effect.post (repZeroEffect p 4)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hr := hrex.rexPrefix
    have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF3, rex, 0xA7] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3, rex] =
        withSeg (repRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
      rw [scanContext_seg_cons _ _ r [0xF3, rex] (noSegPrefix_cons noSegPrefix_f3 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_f3_rex _ _ hr]
    exact repe_cmpsq_step_zero s h.midRep [r.prefixByte, 0xF3, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp)
      (by rw [hsc]; rfl)
      (by rw [hsc]; exact hrex.rex_w s.DS)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      hcodeS hlow hpre.rcxZero

theorem repe_cmpsq_seg_zero_triple [Bindings] (p : BitVec 64) (r : SegReg) :
    Triple (RepZeroPre p) (codeRange p [r.prefixByte, 0xF3, 0x48, 0xA7]) (Effect.post (repZeroEffect p 4)) :=
  repe_cmpsq_seg_zero_triple_of_bytes p r 0x48 (by unfold RexWPrefix; decide)

structure RepeCmpsdLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0xA7]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  srcLow : (rsi.read s).toNat + 4 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 4 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 4 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = count

theorem RepeCmpsdLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpsdLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepeCmpsdLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {s : RamState} {count m : Nat} (h : RepeCmpsdLoop s count m) :
    X86.Machine.step s = some (.next (repeCmpsAfter 32 2 s)) := by
  have := h.srcLow
  have := h.dstLow
  exact repe_cmpsd_step hcm s h.ready [0xF3] (by simpa using scanPrefix_f3) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩ ⟨by omega, fun i hi => h.dstMem i (by omega)⟩

theorem RepeCmpsdLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpsdLoop s count (m + 1)) : repeCmpsCont 32 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeCmpsCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeCmpsdLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepeCmpsdLoop s count 0) : repeCmpsCont 32 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repeCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeCmpsdLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpsdLoop s (count + 1) (m + 1)) : RepeCmpsdLoop (repeCmpsAfter 32 2 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeCmpsAfter 32 2 s).RIP = s.RIP := by
    rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeCmpsAfter 32 2 s).RFLAGS = s.RFLAGS := by
    rw [repeCmpsAfter_rflags, hc]
    rfl
  have hs : rsi.read (repeCmpsAfter 32 2 s) = rsi.read s + BitVec.ofNat 64 4 := repeCmpsAfter_rsi 32 2 s
  have hd : rdi.read (repeCmpsAfter 32 2 s) = rdi.read s + BitVec.ofNat 64 4 := repeCmpsAfter_rdi 32 2 s
  have hsn : (rsi.read (repeCmpsAfter 32 2 s)).toNat = (rsi.read s).toNat + 4 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repeCmpsAfter 32 2 s)).toNat = (rdi.read s).toNat + 4 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 32).read (repeCmpsAfter 32 2 s) = (Operand.mem a : Operand 32).read s := by
    simp only [Operand.read, repeCmpsAfter_external]
  refine ⟨h.ready.repeCmps 32 2, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeCmpsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeCmpsAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repeCmpsAfter_external]
    exact h.srcMem (4 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repeCmpsAfter_external]
    exact h.dstMem (4 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 4 + 4 * i = 4 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 4 + 4 * m = 4 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeCmpsdDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (4 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (4 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_cmpsd_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeCmpsdLoop s count m →
      RepeCmpsdDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeCmpsAfter 32 2 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeCmpsAfter 32 2 s).Repeat_String_Operation = false := by
      rw [repeCmpsAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeCmps 32 2).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeCmpsAfter_rsi]
    · rw [repeCmpsAfter_rdi]
    · rw [repeCmpsAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeCmpsAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeCmps 32 2 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeCmpsAfter 32 2 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repeCmpsAfter 32 2 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repeCmpsAfter 32 2 s).RIP = s.RIP := by
      rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeCmpsAfter 32 2 s).RFLAGS = s.RFLAGS := by
      rw [repeCmpsAfter_rflags, hc]
      rfl
    have hs : rsi.read (repeCmpsAfter 32 2 s) = rsi.read s + BitVec.ofNat 64 4 := repeCmpsAfter_rsi 32 2 s
    have hd : rdi.read (repeCmpsAfter 32 2 s) = rdi.read s + BitVec.ofNat 64 4 := repeCmpsAfter_rdi 32 2 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 32).read (repeCmpsAfter 32 2 s) = (Operand.mem a : Operand 32).read s := by
      simp only [Operand.read, repeCmpsAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 4 + 4 * m = 4 * (m + 1) by omega]
    · refine ((AgreesExcept.repeCmps 32 2 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeCmpsdPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  srcLow : (rsi.read s).toNat + 4 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 4 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 4 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = (rcx.read s).toNat

def repeCmpsdEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (4 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (4 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)))

@[simp] theorem repeCmpsdEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeCmpsdEffect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repeCmpsdEffect, Effect.components]

theorem repe_cmpsd_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0xA7]) s) (hpre : RepeCmpsdPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0xA7]) t ∧ (repeCmpsdEffect p m s).Holds s t := by
  intro t
  have hloop : RepeCmpsdLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_cmpsd_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeCmpsdEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeCmpsdEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repe_cmpsd_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepeCmpsdPre p m) (codeRange p [0xF3, 0xA7]) (Effect.post (repeCmpsdEffect p m)) :=
  fun s h hcode hpre => ⟨_, repe_cmpsd_steps hcm p m s h hcode hpre⟩

structure RepeCmpsdSegLoop [Bindings] (r : SegReg) (base : BitVec 64) (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF3, 0xA7]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  srcLow : (base + rsi.read s).toNat + 4 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 4 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 4 * (m + 1), (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = count
  seg : r.Ready base s

theorem RepeCmpsdSegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat}
    (h : RepeCmpsdSegLoop r base s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepeCmpsdSegLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat} (h : RepeCmpsdSegLoop r base s count m) :
    X86.Machine.step s = some (.next (repeCmpsSegAfter base 32 3 s)) := by
  have := h.srcLow
  have := h.dstLow
  have hsrc : MemReadable s (base + rsi.read s) 4 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3] (noSegPrefix_cons noSegPrefix_f3 noSegPrefix_nil)]
  have hstep := repe_cmpsd_seg_step hcm s h.ready [r.prefixByte, 0xF3] (scanPrefix_seg_cons r (by simpa using scanPrefix_f3)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    h.df h.code h.codeLow h.rcx_ne (by rw [hsc]; exact hsrc)
    ⟨by omega, fun i hi => h.dstMem i (by omega)⟩
  rw [hsc] at hstep
  exact hstep

theorem RepeCmpsdSegLoop.cont_true [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat}
    (h : RepeCmpsdSegLoop r base s count (m + 1)) : repeCmpsSegCont base 32 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeCmpsSegCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeCmpsdSegLoop.cont_false [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepeCmpsdSegLoop r base s count 0) : repeCmpsSegCont base 32 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repeCmpsSegCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeCmpsdSegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat}
    (h : RepeCmpsdSegLoop r base s (count + 1) (m + 1)) : RepeCmpsdSegLoop r base (repeCmpsSegAfter base 32 3 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeCmpsSegAfter base 32 3 s).RIP = s.RIP := by
    rw [repeCmpsSegAfter_rip base _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeCmpsSegAfter base 32 3 s).RFLAGS = s.RFLAGS := by
    rw [repeCmpsSegAfter_rflags, hc]
    rfl
  have hs : base + rsi.read (repeCmpsSegAfter base 32 3 s) = base + rsi.read s + BitVec.ofNat 64 4 := by
    rw [repeCmpsSegAfter_rsi base 32 3 s, BitVec.add_assoc]
  have hd : rdi.read (repeCmpsSegAfter base 32 3 s) = rdi.read s + BitVec.ofNat 64 4 := repeCmpsSegAfter_rdi base 32 3 s
  have hsn : (base + rsi.read (repeCmpsSegAfter base 32 3 s)).toNat = (base + rsi.read s).toNat + 4 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repeCmpsSegAfter base 32 3 s)).toNat = (rdi.read s).toNat + 4 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 32).read (repeCmpsSegAfter base 32 3 s) = (Operand.mem a : Operand 32).read s := by
    simp only [Operand.read, repeCmpsSegAfter_external]
  refine ⟨h.ready.repeCmpsSeg base 32 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    repeCmpsSegAfter_segReady base 32 3 s h.seg⟩
  · intro i hi
    rw [hrip, repeCmpsSegAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeCmpsSegAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repeCmpsSegAfter_external]
    exact h.srcMem (4 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repeCmpsSegAfter_external]
    exact h.dstMem (4 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 4 + 4 * i = 4 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 4 + 4 * m = 4 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeCmpsdSegDone [Bindings] (base : BitVec 64) (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (4 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (4 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_cmpsd_seg_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {r : SegReg} {base : BitVec 64} (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeCmpsdSegLoop r base s count m →
      RepeCmpsdSegDone base s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeCmpsSegAfter base 32 3 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeCmpsSegAfter base 32 3 s).Repeat_String_Operation = false := by
      rw [repeCmpsSegAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeCmpsSeg base 32 3).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeCmpsSegAfter_rip base _ _ s h.ready.msr, hc]; rfl
    · rw [repeCmpsSegAfter_rsi]
    · rw [repeCmpsSegAfter_rdi]
    · rw [repeCmpsSegAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeCmpsSegAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeCmpsSeg base 32 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeCmpsSegAfter base 32 3 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repeCmpsSegAfter base 32 3 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repeCmpsSegAfter base 32 3 s).RIP = s.RIP := by
      rw [repeCmpsSegAfter_rip base _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeCmpsSegAfter base 32 3 s).RFLAGS = s.RFLAGS := by
      rw [repeCmpsSegAfter_rflags, hc]
      rfl
    have hsreg : rsi.read (repeCmpsSegAfter base 32 3 s) = rsi.read s + BitVec.ofNat 64 4 :=
      repeCmpsSegAfter_rsi base 32 3 s
    have hs : base + rsi.read (repeCmpsSegAfter base 32 3 s) = base + rsi.read s + BitVec.ofNat 64 4 := by
      rw [hsreg, BitVec.add_assoc]
    have hd : rdi.read (repeCmpsSegAfter base 32 3 s) = rdi.read s + BitVec.ofNat 64 4 := repeCmpsSegAfter_rdi base 32 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 32).read (repeCmpsSegAfter base 32 3 s) = (Operand.mem a : Operand 32).read s := by
      simp only [Operand.read, repeCmpsSegAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hsreg, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 4 + 4 * m = 4 * (m + 1) by omega]
    · refine ((AgreesExcept.repeCmpsSeg base 32 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeCmpsdSegPre (p : BitVec 64) (r : SegReg) (base : BitVec 64) (m : Nat)
    (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  srcLow : (base + rsi.read s).toNat + 4 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 4 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 4 * (m + 1), (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = (rcx.read s).toNat
  seg : r.Ready base s

def repeCmpsdSegEffect (p base : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (4 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (4 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)))

@[simp] theorem repeCmpsdSegEffect_components (p base : BitVec 64) (m : Nat) (s : RamState) :
    (repeCmpsdSegEffect p base m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repeCmpsdSegEffect, Effect.components]

theorem repe_cmpsd_seg_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF3, 0xA7]) s) (hpre : RepeCmpsdSegPre p r base m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF3, 0xA7]) t ∧ (repeCmpsdSegEffect p base m s).Holds s t := by
  intro t
  have hloop : RepeCmpsdSegLoop r base s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.equal, hpre.stop, hpre.seg⟩
  have hd := repe_cmpsd_seg_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeCmpsdSegEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeCmpsdSegEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repe_cmpsd_seg_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (m : Nat) :
    Triple (RepeCmpsdSegPre p r base m) (codeRange p [r.prefixByte, 0xF3, 0xA7]) (Effect.post (repeCmpsdSegEffect p base m)) :=
  fun s h hcode hpre => ⟨_, repe_cmpsd_seg_steps hcm p r base m s h hcode hpre⟩

theorem repe_cmpsd_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0xF3, 0xA7]) (Effect.post (repZeroEffect p 2)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0xF3, 0xA7] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repe_cmpsd_step_zero s h.midRep [0xF3] (by simpa using scanPrefix_f3) (by simp)
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      hcodeS hlow hpre.rcxZero

theorem repe_cmpsd_seg_zero_triple [Bindings] (p : BitVec 64) (r : SegReg)
    :
    Triple (RepZeroPre p) (codeRange p [r.prefixByte, 0xF3, 0xA7]) (Effect.post (repZeroEffect p 3)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF3, 0xA7] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3] =
        withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) (r.select (PrefixSegments.ofState s)) := by
      rw [scanContext_seg_cons _ _ r [0xF3] (noSegPrefix_cons noSegPrefix_f3 noSegPrefix_nil)]
    exact repe_cmpsd_step_zero s h.midRep [r.prefixByte, 0xF3] (scanPrefix_seg_cons r (by simpa using scanPrefix_f3)) (by simp)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      hcodeS hlow hpre.rcxZero

structure RepeCmpswLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0x66, 0xA7]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  srcLow : (rsi.read s).toNat + 2 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 2 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 2 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 2 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = count

theorem RepeCmpswLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpswLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepeCmpswLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {s : RamState} {count m : Nat} (h : RepeCmpswLoop s count m) :
    X86.Machine.step s = some (.next (repeCmpsAfter 16 3 s)) := by
  have := h.srcLow
  have := h.dstLow
  exact repe_cmpsw_step hcm s h.ready [0xF3, 0x66] (by simp [scanPrefix_f3, scanPrefix_66]) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩ ⟨by omega, fun i hi => h.dstMem i (by omega)⟩

theorem RepeCmpswLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpswLoop s count (m + 1)) : repeCmpsCont 16 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeCmpsCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeCmpswLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepeCmpswLoop s count 0) : repeCmpsCont 16 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repeCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeCmpswLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpswLoop s (count + 1) (m + 1)) : RepeCmpswLoop (repeCmpsAfter 16 3 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeCmpsAfter 16 3 s).RIP = s.RIP := by
    rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeCmpsAfter 16 3 s).RFLAGS = s.RFLAGS := by
    rw [repeCmpsAfter_rflags, hc]
    rfl
  have hs : rsi.read (repeCmpsAfter 16 3 s) = rsi.read s + BitVec.ofNat 64 2 := repeCmpsAfter_rsi 16 3 s
  have hd : rdi.read (repeCmpsAfter 16 3 s) = rdi.read s + BitVec.ofNat 64 2 := repeCmpsAfter_rdi 16 3 s
  have hsn : (rsi.read (repeCmpsAfter 16 3 s)).toNat = (rsi.read s).toNat + 2 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repeCmpsAfter 16 3 s)).toNat = (rdi.read s).toNat + 2 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 16).read (repeCmpsAfter 16 3 s) = (Operand.mem a : Operand 16).read s := by
    simp only [Operand.read, repeCmpsAfter_external]
  refine ⟨h.ready.repeCmps 16 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeCmpsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeCmpsAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repeCmpsAfter_external]
    exact h.srcMem (2 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repeCmpsAfter_external]
    exact h.dstMem (2 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 2 + 2 * i = 2 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 2 + 2 * m = 2 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeCmpswDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (2 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (2 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_cmpsw_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeCmpswLoop s count m →
      RepeCmpswDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeCmpsAfter 16 3 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeCmpsAfter 16 3 s).Repeat_String_Operation = false := by
      rw [repeCmpsAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeCmps 16 3).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeCmpsAfter_rsi]
    · rw [repeCmpsAfter_rdi]
    · rw [repeCmpsAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeCmpsAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeCmps 16 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeCmpsAfter 16 3 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repeCmpsAfter 16 3 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repeCmpsAfter 16 3 s).RIP = s.RIP := by
      rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeCmpsAfter 16 3 s).RFLAGS = s.RFLAGS := by
      rw [repeCmpsAfter_rflags, hc]
      rfl
    have hs : rsi.read (repeCmpsAfter 16 3 s) = rsi.read s + BitVec.ofNat 64 2 := repeCmpsAfter_rsi 16 3 s
    have hd : rdi.read (repeCmpsAfter 16 3 s) = rdi.read s + BitVec.ofNat 64 2 := repeCmpsAfter_rdi 16 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 16).read (repeCmpsAfter 16 3 s) = (Operand.mem a : Operand 16).read s := by
      simp only [Operand.read, repeCmpsAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 2 + 2 * m = 2 * (m + 1) by omega]
    · refine ((AgreesExcept.repeCmps 16 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeCmpswPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  srcLow : (rsi.read s).toNat + 2 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 2 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 2 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 2 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = (rcx.read s).toNat

def repeCmpswEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (2 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (2 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)))

@[simp] theorem repeCmpswEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeCmpswEffect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repeCmpswEffect, Effect.components]

theorem repe_cmpsw_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0x66, 0xA7]) s) (hpre : RepeCmpswPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0x66, 0xA7]) t ∧ (repeCmpswEffect p m s).Holds s t := by
  intro t
  have hloop : RepeCmpswLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_cmpsw_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeCmpswEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeCmpswEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repe_cmpsw_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepeCmpswPre p m) (codeRange p [0xF3, 0x66, 0xA7]) (Effect.post (repeCmpswEffect p m)) :=
  fun s h hcode hpre => ⟨_, repe_cmpsw_steps hcm p m s h hcode hpre⟩

structure RepeCmpswSegLoop [Bindings] (r : SegReg) (base : BitVec 64) (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF3, 0x66, 0xA7]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  srcLow : (base + rsi.read s).toNat + 2 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 2 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 2 * (m + 1), (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 2 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = count
  seg : r.Ready base s

theorem RepeCmpswSegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat}
    (h : RepeCmpswSegLoop r base s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepeCmpswSegLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat} (h : RepeCmpswSegLoop r base s count m) :
    X86.Machine.step s = some (.next (repeCmpsSegAfter base 16 4 s)) := by
  have := h.srcLow
  have := h.dstLow
  have hsrc : MemReadable s (base + rsi.read s) 2 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3, 0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3, 0x66] (noSegPrefix_cons noSegPrefix_f3 (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil))]
  have hstep := repe_cmpsw_seg_step hcm s h.ready [r.prefixByte, 0xF3, 0x66] (scanPrefix_seg_cons r (by simp [scanPrefix_f3, scanPrefix_66])) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    h.df h.code h.codeLow h.rcx_ne (by rw [hsc]; exact hsrc)
    ⟨by omega, fun i hi => h.dstMem i (by omega)⟩
  rw [hsc] at hstep
  exact hstep

theorem RepeCmpswSegLoop.cont_true [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat}
    (h : RepeCmpswSegLoop r base s count (m + 1)) : repeCmpsSegCont base 16 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeCmpsSegCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeCmpswSegLoop.cont_false [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepeCmpswSegLoop r base s count 0) : repeCmpsSegCont base 16 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repeCmpsSegCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeCmpswSegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat}
    (h : RepeCmpswSegLoop r base s (count + 1) (m + 1)) : RepeCmpswSegLoop r base (repeCmpsSegAfter base 16 4 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeCmpsSegAfter base 16 4 s).RIP = s.RIP := by
    rw [repeCmpsSegAfter_rip base _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeCmpsSegAfter base 16 4 s).RFLAGS = s.RFLAGS := by
    rw [repeCmpsSegAfter_rflags, hc]
    rfl
  have hs : base + rsi.read (repeCmpsSegAfter base 16 4 s) = base + rsi.read s + BitVec.ofNat 64 2 := by
    rw [repeCmpsSegAfter_rsi base 16 4 s, BitVec.add_assoc]
  have hd : rdi.read (repeCmpsSegAfter base 16 4 s) = rdi.read s + BitVec.ofNat 64 2 := repeCmpsSegAfter_rdi base 16 4 s
  have hsn : (base + rsi.read (repeCmpsSegAfter base 16 4 s)).toNat = (base + rsi.read s).toNat + 2 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repeCmpsSegAfter base 16 4 s)).toNat = (rdi.read s).toNat + 2 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 16).read (repeCmpsSegAfter base 16 4 s) = (Operand.mem a : Operand 16).read s := by
    simp only [Operand.read, repeCmpsSegAfter_external]
  refine ⟨h.ready.repeCmpsSeg base 16 4, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    repeCmpsSegAfter_segReady base 16 4 s h.seg⟩
  · intro i hi
    rw [hrip, repeCmpsSegAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeCmpsSegAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repeCmpsSegAfter_external]
    exact h.srcMem (2 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repeCmpsSegAfter_external]
    exact h.dstMem (2 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 2 + 2 * i = 2 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 2 + 2 * m = 2 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeCmpswSegDone [Bindings] (base : BitVec 64) (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 4)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (2 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (2 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_cmpsw_seg_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {r : SegReg} {base : BitVec 64} (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeCmpswSegLoop r base s count m →
      RepeCmpswSegDone base s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeCmpsSegAfter base 16 4 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeCmpsSegAfter base 16 4 s).Repeat_String_Operation = false := by
      rw [repeCmpsSegAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeCmpsSeg base 16 4).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeCmpsSegAfter_rip base _ _ s h.ready.msr, hc]; rfl
    · rw [repeCmpsSegAfter_rsi]
    · rw [repeCmpsSegAfter_rdi]
    · rw [repeCmpsSegAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeCmpsSegAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeCmpsSeg base 16 4 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeCmpsSegAfter base 16 4 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repeCmpsSegAfter base 16 4 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repeCmpsSegAfter base 16 4 s).RIP = s.RIP := by
      rw [repeCmpsSegAfter_rip base _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeCmpsSegAfter base 16 4 s).RFLAGS = s.RFLAGS := by
      rw [repeCmpsSegAfter_rflags, hc]
      rfl
    have hsreg : rsi.read (repeCmpsSegAfter base 16 4 s) = rsi.read s + BitVec.ofNat 64 2 :=
      repeCmpsSegAfter_rsi base 16 4 s
    have hs : base + rsi.read (repeCmpsSegAfter base 16 4 s) = base + rsi.read s + BitVec.ofNat 64 2 := by
      rw [hsreg, BitVec.add_assoc]
    have hd : rdi.read (repeCmpsSegAfter base 16 4 s) = rdi.read s + BitVec.ofNat 64 2 := repeCmpsSegAfter_rdi base 16 4 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 16).read (repeCmpsSegAfter base 16 4 s) = (Operand.mem a : Operand 16).read s := by
      simp only [Operand.read, repeCmpsSegAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hsreg, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 2 + 2 * m = 2 * (m + 1) by omega]
    · refine ((AgreesExcept.repeCmpsSeg base 16 4 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeCmpswSegPre (p : BitVec 64) (r : SegReg) (base : BitVec 64) (m : Nat)
    (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  srcLow : (base + rsi.read s).toNat + 2 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 2 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 2 * (m + 1), (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 2 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = (rcx.read s).toNat
  seg : r.Ready base s

def repeCmpswSegEffect (p base : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 4
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (2 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (2 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)))

@[simp] theorem repeCmpswSegEffect_components (p base : BitVec 64) (m : Nat) (s : RamState) :
    (repeCmpswSegEffect p base m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repeCmpswSegEffect, Effect.components]

theorem repe_cmpsw_seg_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF3, 0x66, 0xA7]) s) (hpre : RepeCmpswSegPre p r base m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF3, 0x66, 0xA7]) t ∧ (repeCmpswSegEffect p base m s).Holds s t := by
  intro t
  have hloop : RepeCmpswSegLoop r base s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.equal, hpre.stop, hpre.seg⟩
  have hd := repe_cmpsw_seg_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeCmpswSegEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeCmpswSegEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repe_cmpsw_seg_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (m : Nat) :
    Triple (RepeCmpswSegPre p r base m) (codeRange p [r.prefixByte, 0xF3, 0x66, 0xA7]) (Effect.post (repeCmpswSegEffect p base m)) :=
  fun s h hcode hpre => ⟨_, repe_cmpsw_seg_steps hcm p r base m s h hcode hpre⟩

theorem repe_cmpsw_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0xF3, 0x66, 0xA7]) (Effect.post (repZeroEffect p 3)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0xF3, 0x66, 0xA7] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repe_cmpsw_step_zero s h.midRep [0xF3, 0x66] (by simp [scanPrefix_f3, scanPrefix_66]) (by simp)
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      hcodeS hlow hpre.rcxZero

theorem repe_cmpsw_seg_zero_triple [Bindings] (p : BitVec 64) (r : SegReg)
    :
    Triple (RepZeroPre p) (codeRange p [r.prefixByte, 0xF3, 0x66, 0xA7]) (Effect.post (repZeroEffect p 4)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF3, 0x66, 0xA7] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3, 0x66] =
        withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3, 0x66]) (r.select (PrefixSegments.ofState s)) := by
      rw [scanContext_seg_cons _ _ r [0xF3, 0x66] (noSegPrefix_cons noSegPrefix_f3 (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil))]
    exact repe_cmpsw_step_zero s h.midRep [r.prefixByte, 0xF3, 0x66] (scanPrefix_seg_cons r (by simp [scanPrefix_f3, scanPrefix_66])) (by simp)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      hcodeS hlow hpre.rcxZero

structure RepeCmpsbLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0xA6]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  srcLow : (rsi.read s).toNat + 1 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 1 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 1 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 1 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = count

theorem RepeCmpsbLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpsbLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepeCmpsbLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {s : RamState} {count m : Nat} (h : RepeCmpsbLoop s count m) :
    X86.Machine.step s = some (.next (repeCmpsAfter 8 2 s)) := by
  have := h.srcLow
  have := h.dstLow
  exact repe_cmpsb_step hcm s h.ready [0xF3] (by simpa using scanPrefix_f3) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩ ⟨by omega, fun i hi => h.dstMem i (by omega)⟩

theorem RepeCmpsbLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpsbLoop s count (m + 1)) : repeCmpsCont 8 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeCmpsCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeCmpsbLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepeCmpsbLoop s count 0) : repeCmpsCont 8 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repeCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeCmpsbLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpsbLoop s (count + 1) (m + 1)) : RepeCmpsbLoop (repeCmpsAfter 8 2 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeCmpsAfter 8 2 s).RIP = s.RIP := by
    rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeCmpsAfter 8 2 s).RFLAGS = s.RFLAGS := by
    rw [repeCmpsAfter_rflags, hc]
    rfl
  have hs : rsi.read (repeCmpsAfter 8 2 s) = rsi.read s + BitVec.ofNat 64 1 := repeCmpsAfter_rsi 8 2 s
  have hd : rdi.read (repeCmpsAfter 8 2 s) = rdi.read s + BitVec.ofNat 64 1 := repeCmpsAfter_rdi 8 2 s
  have hsn : (rsi.read (repeCmpsAfter 8 2 s)).toNat = (rsi.read s).toNat + 1 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repeCmpsAfter 8 2 s)).toNat = (rdi.read s).toNat + 1 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 8).read (repeCmpsAfter 8 2 s) = (Operand.mem a : Operand 8).read s := by
    simp only [Operand.read, repeCmpsAfter_external]
  refine ⟨h.ready.repeCmps 8 2, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeCmpsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeCmpsAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repeCmpsAfter_external]
    exact h.srcMem (1 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repeCmpsAfter_external]
    exact h.dstMem (1 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 1 + 1 * i = 1 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 1 + 1 * m = 1 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeCmpsbDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (1 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (1 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_cmpsb_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeCmpsbLoop s count m →
      RepeCmpsbDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeCmpsAfter 8 2 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeCmpsAfter 8 2 s).Repeat_String_Operation = false := by
      rw [repeCmpsAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeCmps 8 2).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeCmpsAfter_rsi]
    · rw [repeCmpsAfter_rdi]
    · rw [repeCmpsAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeCmpsAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeCmps 8 2 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeCmpsAfter 8 2 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repeCmpsAfter 8 2 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repeCmpsAfter 8 2 s).RIP = s.RIP := by
      rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeCmpsAfter 8 2 s).RFLAGS = s.RFLAGS := by
      rw [repeCmpsAfter_rflags, hc]
      rfl
    have hs : rsi.read (repeCmpsAfter 8 2 s) = rsi.read s + BitVec.ofNat 64 1 := repeCmpsAfter_rsi 8 2 s
    have hd : rdi.read (repeCmpsAfter 8 2 s) = rdi.read s + BitVec.ofNat 64 1 := repeCmpsAfter_rdi 8 2 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 8).read (repeCmpsAfter 8 2 s) = (Operand.mem a : Operand 8).read s := by
      simp only [Operand.read, repeCmpsAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 1 + 1 * m = 1 * (m + 1) by omega]
    · refine ((AgreesExcept.repeCmps 8 2 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeCmpsbPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  srcLow : (rsi.read s).toNat + 1 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 1 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 1 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 1 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = (rcx.read s).toNat

def repeCmpsbEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (1 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (1 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)))

@[simp] theorem repeCmpsbEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeCmpsbEffect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repeCmpsbEffect, Effect.components]

theorem repe_cmpsb_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0xA6]) s) (hpre : RepeCmpsbPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0xA6]) t ∧ (repeCmpsbEffect p m s).Holds s t := by
  intro t
  have hloop : RepeCmpsbLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_cmpsb_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeCmpsbEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeCmpsbEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repe_cmpsb_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepeCmpsbPre p m) (codeRange p [0xF3, 0xA6]) (Effect.post (repeCmpsbEffect p m)) :=
  fun s h hcode hpre => ⟨_, repe_cmpsb_steps hcm p m s h hcode hpre⟩

structure RepeCmpsbSegLoop [Bindings] (r : SegReg) (base : BitVec 64) (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF3, 0xA6]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  srcLow : (base + rsi.read s).toNat + 1 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 1 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 1 * (m + 1), (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 1 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = count
  seg : r.Ready base s

theorem RepeCmpsbSegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat}
    (h : RepeCmpsbSegLoop r base s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepeCmpsbSegLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat} (h : RepeCmpsbSegLoop r base s count m) :
    X86.Machine.step s = some (.next (repeCmpsSegAfter base 8 3 s)) := by
  have := h.srcLow
  have := h.dstLow
  have hsrc : MemReadable s (base + rsi.read s) 1 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3] (noSegPrefix_cons noSegPrefix_f3 noSegPrefix_nil)]
  have hstep := repe_cmpsb_seg_step hcm s h.ready [r.prefixByte, 0xF3] (scanPrefix_seg_cons r (by simpa using scanPrefix_f3)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    h.df h.code h.codeLow h.rcx_ne (by rw [hsc]; exact hsrc)
    ⟨by omega, fun i hi => h.dstMem i (by omega)⟩
  rw [hsc] at hstep
  exact hstep

theorem RepeCmpsbSegLoop.cont_true [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat}
    (h : RepeCmpsbSegLoop r base s count (m + 1)) : repeCmpsSegCont base 8 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeCmpsSegCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeCmpsbSegLoop.cont_false [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepeCmpsbSegLoop r base s count 0) : repeCmpsSegCont base 8 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repeCmpsSegCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeCmpsbSegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat}
    (h : RepeCmpsbSegLoop r base s (count + 1) (m + 1)) : RepeCmpsbSegLoop r base (repeCmpsSegAfter base 8 3 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeCmpsSegAfter base 8 3 s).RIP = s.RIP := by
    rw [repeCmpsSegAfter_rip base _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeCmpsSegAfter base 8 3 s).RFLAGS = s.RFLAGS := by
    rw [repeCmpsSegAfter_rflags, hc]
    rfl
  have hs : base + rsi.read (repeCmpsSegAfter base 8 3 s) = base + rsi.read s + BitVec.ofNat 64 1 := by
    rw [repeCmpsSegAfter_rsi base 8 3 s, BitVec.add_assoc]
  have hd : rdi.read (repeCmpsSegAfter base 8 3 s) = rdi.read s + BitVec.ofNat 64 1 := repeCmpsSegAfter_rdi base 8 3 s
  have hsn : (base + rsi.read (repeCmpsSegAfter base 8 3 s)).toNat = (base + rsi.read s).toNat + 1 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repeCmpsSegAfter base 8 3 s)).toNat = (rdi.read s).toNat + 1 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 8).read (repeCmpsSegAfter base 8 3 s) = (Operand.mem a : Operand 8).read s := by
    simp only [Operand.read, repeCmpsSegAfter_external]
  refine ⟨h.ready.repeCmpsSeg base 8 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    repeCmpsSegAfter_segReady base 8 3 s h.seg⟩
  · intro i hi
    rw [hrip, repeCmpsSegAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeCmpsSegAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repeCmpsSegAfter_external]
    exact h.srcMem (1 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repeCmpsSegAfter_external]
    exact h.dstMem (1 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 1 + 1 * i = 1 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 1 + 1 * m = 1 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeCmpsbSegDone [Bindings] (base : BitVec 64) (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (1 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (1 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_cmpsb_seg_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {r : SegReg} {base : BitVec 64} (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeCmpsbSegLoop r base s count m →
      RepeCmpsbSegDone base s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeCmpsSegAfter base 8 3 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeCmpsSegAfter base 8 3 s).Repeat_String_Operation = false := by
      rw [repeCmpsSegAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeCmpsSeg base 8 3).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeCmpsSegAfter_rip base _ _ s h.ready.msr, hc]; rfl
    · rw [repeCmpsSegAfter_rsi]
    · rw [repeCmpsSegAfter_rdi]
    · rw [repeCmpsSegAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeCmpsSegAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeCmpsSeg base 8 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeCmpsSegAfter base 8 3 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repeCmpsSegAfter base 8 3 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repeCmpsSegAfter base 8 3 s).RIP = s.RIP := by
      rw [repeCmpsSegAfter_rip base _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeCmpsSegAfter base 8 3 s).RFLAGS = s.RFLAGS := by
      rw [repeCmpsSegAfter_rflags, hc]
      rfl
    have hsreg : rsi.read (repeCmpsSegAfter base 8 3 s) = rsi.read s + BitVec.ofNat 64 1 :=
      repeCmpsSegAfter_rsi base 8 3 s
    have hs : base + rsi.read (repeCmpsSegAfter base 8 3 s) = base + rsi.read s + BitVec.ofNat 64 1 := by
      rw [hsreg, BitVec.add_assoc]
    have hd : rdi.read (repeCmpsSegAfter base 8 3 s) = rdi.read s + BitVec.ofNat 64 1 := repeCmpsSegAfter_rdi base 8 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 8).read (repeCmpsSegAfter base 8 3 s) = (Operand.mem a : Operand 8).read s := by
      simp only [Operand.read, repeCmpsSegAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hsreg, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 1 + 1 * m = 1 * (m + 1) by omega]
    · refine ((AgreesExcept.repeCmpsSeg base 8 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeCmpsbSegPre (p : BitVec 64) (r : SegReg) (base : BitVec 64) (m : Nat)
    (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  srcLow : (base + rsi.read s).toNat + 1 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 1 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 1 * (m + 1), (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 1 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = (rcx.read s).toNat
  seg : r.Ready base s

def repeCmpsbSegEffect (p base : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (1 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (1 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)))

@[simp] theorem repeCmpsbSegEffect_components (p base : BitVec 64) (m : Nat) (s : RamState) :
    (repeCmpsbSegEffect p base m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repeCmpsbSegEffect, Effect.components]

theorem repe_cmpsb_seg_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF3, 0xA6]) s) (hpre : RepeCmpsbSegPre p r base m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF3, 0xA6]) t ∧ (repeCmpsbSegEffect p base m s).Holds s t := by
  intro t
  have hloop : RepeCmpsbSegLoop r base s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.equal, hpre.stop, hpre.seg⟩
  have hd := repe_cmpsb_seg_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeCmpsbSegEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeCmpsbSegEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repe_cmpsb_seg_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (m : Nat) :
    Triple (RepeCmpsbSegPre p r base m) (codeRange p [r.prefixByte, 0xF3, 0xA6]) (Effect.post (repeCmpsbSegEffect p base m)) :=
  fun s h hcode hpre => ⟨_, repe_cmpsb_seg_steps hcm p r base m s h hcode hpre⟩

theorem repe_cmpsb_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0xF3, 0xA6]) (Effect.post (repZeroEffect p 2)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0xF3, 0xA6] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repe_cmpsb_step_zero s h.midRep [0xF3] (by simpa using scanPrefix_f3) (by simp)
      rfl
      rfl
      rfl
      rfl
      rfl
      hcodeS hlow hpre.rcxZero

theorem repe_cmpsb_seg_zero_triple [Bindings] (p : BitVec 64) (r : SegReg)
    :
    Triple (RepZeroPre p) (codeRange p [r.prefixByte, 0xF3, 0xA6]) (Effect.post (repZeroEffect p 3)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF3, 0xA6] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3] =
        withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) (r.select (PrefixSegments.ofState s)) := by
      rw [scanContext_seg_cons _ _ r [0xF3] (noSegPrefix_cons noSegPrefix_f3 noSegPrefix_nil)]
    exact repe_cmpsb_step_zero s h.midRep [r.prefixByte, 0xF3] (scanPrefix_seg_cons r (by simpa using scanPrefix_f3)) (by simp)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      hcodeS hlow hpre.rcxZero

structure RepeCmpsqA32Loop [Bindings] (rex : UInt8) (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF3, rex, 0xA7]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^32
  bound : m < count
  srcLow : (rsi.read s).toNat + 8 * (m + 1) < 2^32
  dstLow : (rdi.read s).toNat + 8 * (m + 1) < 2^32
  srcMem : ∀ i < 8 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = count

theorem RepeCmpsqA32Loop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepeCmpsqA32Loop rex s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepeCmpsqA32Loop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState} {count m : Nat} (h : RepeCmpsqA32Loop rex s count m) :
    X86.Machine.step s = some (.next (repeCmpsAfter 64 4 s)) := by
  have hr := hrex.rexPrefix
  have := h.srcLow
  have := h.dstLow
  exact repe_cmpsq_a32_step hcm s h.ready [0x67, 0xF3, rex] (scanPrefix_asz_cons (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩ ⟨by omega, fun i hi => h.dstMem i (by omega)⟩
    (by omega) (by omega)
    (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.countLt; omega)]; exact h.countLt)

theorem RepeCmpsqA32Loop.cont_true [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepeCmpsqA32Loop rex s count (m + 1)) : repeCmpsCont 64 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeCmpsCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeCmpsqA32Loop.cont_false [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepeCmpsqA32Loop rex s count 0) : repeCmpsCont 64 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repeCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeCmpsqA32Loop.next [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepeCmpsqA32Loop rex s (count + 1) (m + 1)) : RepeCmpsqA32Loop rex (repeCmpsAfter 64 4 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeCmpsAfter 64 4 s).RIP = s.RIP := by
    rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeCmpsAfter 64 4 s).RFLAGS = s.RFLAGS := by
    rw [repeCmpsAfter_rflags, hc]
    rfl
  have hs : rsi.read (repeCmpsAfter 64 4 s) = rsi.read s + BitVec.ofNat 64 8 := repeCmpsAfter_rsi 64 4 s
  have hd : rdi.read (repeCmpsAfter 64 4 s) = rdi.read s + BitVec.ofNat 64 8 := repeCmpsAfter_rdi 64 4 s
  have hsn : (rsi.read (repeCmpsAfter 64 4 s)).toNat = (rsi.read s).toNat + 8 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repeCmpsAfter 64 4 s)).toNat = (rdi.read s).toNat + 8 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 64).read (repeCmpsAfter 64 4 s) = (Operand.mem a : Operand 64).read s := by
    simp only [Operand.read, repeCmpsAfter_external]
  refine ⟨h.ready.repeCmps 64 4, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeCmpsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeCmpsAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repeCmpsAfter_external]
    exact h.srcMem (8 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repeCmpsAfter_external]
    exact h.dstMem (8 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 8 + 8 * i = 8 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 8 + 8 * m = 8 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeCmpsqA32Done [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 4)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (8 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (8 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_cmpsq_a32_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeCmpsqA32Loop rex s count m →
      RepeCmpsqA32Done s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeCmpsAfter 64 4 s) := nextState_of_step (h.step hcm hrex )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeCmpsAfter 64 4 s).Repeat_String_Operation = false := by
      rw [repeCmpsAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeCmps 64 4).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeCmpsAfter_rsi]
    · rw [repeCmpsAfter_rdi]
    · rw [repeCmpsAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeCmpsAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeCmps 64 4 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeCmpsAfter 64 4 s) := nextState_of_step (h.step hcm hrex )
    have hc := h.cont_true
    have ih' := ih c (repeCmpsAfter 64 4 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repeCmpsAfter 64 4 s).RIP = s.RIP := by
      rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeCmpsAfter 64 4 s).RFLAGS = s.RFLAGS := by
      rw [repeCmpsAfter_rflags, hc]
      rfl
    have hs : rsi.read (repeCmpsAfter 64 4 s) = rsi.read s + BitVec.ofNat 64 8 := repeCmpsAfter_rsi 64 4 s
    have hd : rdi.read (repeCmpsAfter 64 4 s) = rdi.read s + BitVec.ofNat 64 8 := repeCmpsAfter_rdi 64 4 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 64).read (repeCmpsAfter 64 4 s) = (Operand.mem a : Operand 64).read s := by
      simp only [Operand.read, repeCmpsAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 8 + 8 * m = 8 * (m + 1) by omega]
    · refine ((AgreesExcept.repeCmps 64 4 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeCmpsqA32Pre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  rcxLow : (rcx.read s).toNat < 2^32
  srcLow : (rsi.read s).toNat + 8 * (m + 1) < 2^32
  dstLow : (rdi.read s).toNat + 8 * (m + 1) < 2^32
  srcMem : ∀ i < 8 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = (rcx.read s).toNat

def repeCmpsqA32Effect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 4
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (8 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (8 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)))

@[simp] theorem repeCmpsqA32Effect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeCmpsqA32Effect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repeCmpsqA32Effect, Effect.components]

theorem repe_cmpsq_a32_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF3, rex, 0xA7]) s) (hpre : RepeCmpsqA32Pre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF3, rex, 0xA7]) t ∧ (repeCmpsqA32Effect p m s).Holds s t := by
  intro t
  have hloop : RepeCmpsqA32Loop rex s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hpre.rcxLow, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_cmpsq_a32_loop hcm hrex m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeCmpsqA32Effect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeCmpsqA32Effect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repe_cmpsq_a32_triple_of_bytes [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    Triple (RepeCmpsqA32Pre p m) (codeRange p [0x67, 0xF3, rex, 0xA7]) (Effect.post (repeCmpsqA32Effect p m)) :=
  fun s h hcode hpre => ⟨_, repe_cmpsq_a32_steps hcm p rex hrex m s h hcode hpre⟩

theorem repe_cmpsq_a32_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepeCmpsqA32Pre p m) (codeRange p [0x67, 0xF3, 0x48, 0xA7]) (Effect.post (repeCmpsqA32Effect p m)) :=
  repe_cmpsq_a32_triple_of_bytes hcm p 0x48 (by unfold RexWPrefix; decide) m

theorem repe_cmpsq_a32_zero_triple_of_bytes [Bindings] (p : BitVec 64)
    (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepZeroPre p) (codeRange p [0x67, 0xF3, rex, 0xA7]) (Effect.post (repZeroEffect p 4)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hr := hrex.rexPrefix
    have hcodeS : BytesAt s s.RIP [0x67, 0xF3, rex, 0xA7] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repe_cmpsq_a32_step_zero s h.midRep [0x67, 0xF3, rex] (scanPrefix_asz_cons (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp)
      (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
      (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
      (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
      (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
      (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
      (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
      hcodeS hlow hpre.rcxZero

theorem repe_cmpsq_a32_zero_triple [Bindings] (p : BitVec 64) :
    Triple (RepZeroPre p) (codeRange p [0x67, 0xF3, 0x48, 0xA7]) (Effect.post (repZeroEffect p 4)) :=
  repe_cmpsq_a32_zero_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide)

structure RepeCmpsdA32Loop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF3, 0xA7]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^32
  bound : m < count
  srcLow : (rsi.read s).toNat + 4 * (m + 1) < 2^32
  dstLow : (rdi.read s).toNat + 4 * (m + 1) < 2^32
  srcMem : ∀ i < 4 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = count

theorem RepeCmpsdA32Loop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpsdA32Loop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepeCmpsdA32Loop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {s : RamState} {count m : Nat} (h : RepeCmpsdA32Loop s count m) :
    X86.Machine.step s = some (.next (repeCmpsAfter 32 3 s)) := by
  have := h.srcLow
  have := h.dstLow
  exact repe_cmpsd_a32_step hcm s h.ready [0x67, 0xF3] (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩ ⟨by omega, fun i hi => h.dstMem i (by omega)⟩
    (by omega) (by omega)
    (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.countLt; omega)]; exact h.countLt)

theorem RepeCmpsdA32Loop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpsdA32Loop s count (m + 1)) : repeCmpsCont 32 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeCmpsCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeCmpsdA32Loop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepeCmpsdA32Loop s count 0) : repeCmpsCont 32 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repeCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeCmpsdA32Loop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpsdA32Loop s (count + 1) (m + 1)) : RepeCmpsdA32Loop (repeCmpsAfter 32 3 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeCmpsAfter 32 3 s).RIP = s.RIP := by
    rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeCmpsAfter 32 3 s).RFLAGS = s.RFLAGS := by
    rw [repeCmpsAfter_rflags, hc]
    rfl
  have hs : rsi.read (repeCmpsAfter 32 3 s) = rsi.read s + BitVec.ofNat 64 4 := repeCmpsAfter_rsi 32 3 s
  have hd : rdi.read (repeCmpsAfter 32 3 s) = rdi.read s + BitVec.ofNat 64 4 := repeCmpsAfter_rdi 32 3 s
  have hsn : (rsi.read (repeCmpsAfter 32 3 s)).toNat = (rsi.read s).toNat + 4 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repeCmpsAfter 32 3 s)).toNat = (rdi.read s).toNat + 4 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 32).read (repeCmpsAfter 32 3 s) = (Operand.mem a : Operand 32).read s := by
    simp only [Operand.read, repeCmpsAfter_external]
  refine ⟨h.ready.repeCmps 32 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeCmpsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeCmpsAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repeCmpsAfter_external]
    exact h.srcMem (4 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repeCmpsAfter_external]
    exact h.dstMem (4 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 4 + 4 * i = 4 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 4 + 4 * m = 4 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeCmpsdA32Done [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (4 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (4 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_cmpsd_a32_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeCmpsdA32Loop s count m →
      RepeCmpsdA32Done s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeCmpsAfter 32 3 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeCmpsAfter 32 3 s).Repeat_String_Operation = false := by
      rw [repeCmpsAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeCmps 32 3).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeCmpsAfter_rsi]
    · rw [repeCmpsAfter_rdi]
    · rw [repeCmpsAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeCmpsAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeCmps 32 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeCmpsAfter 32 3 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repeCmpsAfter 32 3 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repeCmpsAfter 32 3 s).RIP = s.RIP := by
      rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeCmpsAfter 32 3 s).RFLAGS = s.RFLAGS := by
      rw [repeCmpsAfter_rflags, hc]
      rfl
    have hs : rsi.read (repeCmpsAfter 32 3 s) = rsi.read s + BitVec.ofNat 64 4 := repeCmpsAfter_rsi 32 3 s
    have hd : rdi.read (repeCmpsAfter 32 3 s) = rdi.read s + BitVec.ofNat 64 4 := repeCmpsAfter_rdi 32 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 32).read (repeCmpsAfter 32 3 s) = (Operand.mem a : Operand 32).read s := by
      simp only [Operand.read, repeCmpsAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 4 + 4 * m = 4 * (m + 1) by omega]
    · refine ((AgreesExcept.repeCmps 32 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeCmpsdA32Pre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  rcxLow : (rcx.read s).toNat < 2^32
  srcLow : (rsi.read s).toNat + 4 * (m + 1) < 2^32
  dstLow : (rdi.read s).toNat + 4 * (m + 1) < 2^32
  srcMem : ∀ i < 4 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = (rcx.read s).toNat

def repeCmpsdA32Effect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (4 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (4 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)))

@[simp] theorem repeCmpsdA32Effect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeCmpsdA32Effect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repeCmpsdA32Effect, Effect.components]

theorem repe_cmpsd_a32_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF3, 0xA7]) s) (hpre : RepeCmpsdA32Pre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF3, 0xA7]) t ∧ (repeCmpsdA32Effect p m s).Holds s t := by
  intro t
  have hloop : RepeCmpsdA32Loop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hpre.rcxLow, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_cmpsd_a32_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeCmpsdA32Effect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeCmpsdA32Effect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repe_cmpsd_a32_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepeCmpsdA32Pre p m) (codeRange p [0x67, 0xF3, 0xA7]) (Effect.post (repeCmpsdA32Effect p m)) :=
  fun s h hcode hpre => ⟨_, repe_cmpsd_a32_steps hcm p m s h hcode hpre⟩

theorem repe_cmpsd_a32_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0x67, 0xF3, 0xA7]) (Effect.post (repZeroEffect p 3)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0x67, 0xF3, 0xA7] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repe_cmpsd_a32_step_zero s h.midRep [0x67, 0xF3] (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      hcodeS hlow hpre.rcxZero

structure RepeCmpswA32Loop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF3, 0x66, 0xA7]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^32
  bound : m < count
  srcLow : (rsi.read s).toNat + 2 * (m + 1) < 2^32
  dstLow : (rdi.read s).toNat + 2 * (m + 1) < 2^32
  srcMem : ∀ i < 2 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 2 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = count

theorem RepeCmpswA32Loop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpswA32Loop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepeCmpswA32Loop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {s : RamState} {count m : Nat} (h : RepeCmpswA32Loop s count m) :
    X86.Machine.step s = some (.next (repeCmpsAfter 16 4 s)) := by
  have := h.srcLow
  have := h.dstLow
  exact repe_cmpsw_a32_step hcm s h.ready [0x67, 0xF3, 0x66] (scanPrefix_asz_cons (by simp [scanPrefix_f3, scanPrefix_66])) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩ ⟨by omega, fun i hi => h.dstMem i (by omega)⟩
    (by omega) (by omega)
    (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.countLt; omega)]; exact h.countLt)

theorem RepeCmpswA32Loop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpswA32Loop s count (m + 1)) : repeCmpsCont 16 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeCmpsCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeCmpswA32Loop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepeCmpswA32Loop s count 0) : repeCmpsCont 16 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repeCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeCmpswA32Loop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpswA32Loop s (count + 1) (m + 1)) : RepeCmpswA32Loop (repeCmpsAfter 16 4 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeCmpsAfter 16 4 s).RIP = s.RIP := by
    rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeCmpsAfter 16 4 s).RFLAGS = s.RFLAGS := by
    rw [repeCmpsAfter_rflags, hc]
    rfl
  have hs : rsi.read (repeCmpsAfter 16 4 s) = rsi.read s + BitVec.ofNat 64 2 := repeCmpsAfter_rsi 16 4 s
  have hd : rdi.read (repeCmpsAfter 16 4 s) = rdi.read s + BitVec.ofNat 64 2 := repeCmpsAfter_rdi 16 4 s
  have hsn : (rsi.read (repeCmpsAfter 16 4 s)).toNat = (rsi.read s).toNat + 2 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repeCmpsAfter 16 4 s)).toNat = (rdi.read s).toNat + 2 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 16).read (repeCmpsAfter 16 4 s) = (Operand.mem a : Operand 16).read s := by
    simp only [Operand.read, repeCmpsAfter_external]
  refine ⟨h.ready.repeCmps 16 4, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeCmpsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeCmpsAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repeCmpsAfter_external]
    exact h.srcMem (2 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repeCmpsAfter_external]
    exact h.dstMem (2 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 2 + 2 * i = 2 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 2 + 2 * m = 2 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeCmpswA32Done [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 4)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (2 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (2 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_cmpsw_a32_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeCmpswA32Loop s count m →
      RepeCmpswA32Done s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeCmpsAfter 16 4 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeCmpsAfter 16 4 s).Repeat_String_Operation = false := by
      rw [repeCmpsAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeCmps 16 4).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeCmpsAfter_rsi]
    · rw [repeCmpsAfter_rdi]
    · rw [repeCmpsAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeCmpsAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeCmps 16 4 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeCmpsAfter 16 4 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repeCmpsAfter 16 4 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repeCmpsAfter 16 4 s).RIP = s.RIP := by
      rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeCmpsAfter 16 4 s).RFLAGS = s.RFLAGS := by
      rw [repeCmpsAfter_rflags, hc]
      rfl
    have hs : rsi.read (repeCmpsAfter 16 4 s) = rsi.read s + BitVec.ofNat 64 2 := repeCmpsAfter_rsi 16 4 s
    have hd : rdi.read (repeCmpsAfter 16 4 s) = rdi.read s + BitVec.ofNat 64 2 := repeCmpsAfter_rdi 16 4 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 16).read (repeCmpsAfter 16 4 s) = (Operand.mem a : Operand 16).read s := by
      simp only [Operand.read, repeCmpsAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 2 + 2 * m = 2 * (m + 1) by omega]
    · refine ((AgreesExcept.repeCmps 16 4 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeCmpswA32Pre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  rcxLow : (rcx.read s).toNat < 2^32
  srcLow : (rsi.read s).toNat + 2 * (m + 1) < 2^32
  dstLow : (rdi.read s).toNat + 2 * (m + 1) < 2^32
  srcMem : ∀ i < 2 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 2 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = (rcx.read s).toNat

def repeCmpswA32Effect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 4
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (2 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (2 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)))

@[simp] theorem repeCmpswA32Effect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeCmpswA32Effect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repeCmpswA32Effect, Effect.components]

theorem repe_cmpsw_a32_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF3, 0x66, 0xA7]) s) (hpre : RepeCmpswA32Pre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF3, 0x66, 0xA7]) t ∧ (repeCmpswA32Effect p m s).Holds s t := by
  intro t
  have hloop : RepeCmpswA32Loop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hpre.rcxLow, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_cmpsw_a32_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeCmpswA32Effect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeCmpswA32Effect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repe_cmpsw_a32_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepeCmpswA32Pre p m) (codeRange p [0x67, 0xF3, 0x66, 0xA7]) (Effect.post (repeCmpswA32Effect p m)) :=
  fun s h hcode hpre => ⟨_, repe_cmpsw_a32_steps hcm p m s h hcode hpre⟩

theorem repe_cmpsw_a32_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0x67, 0xF3, 0x66, 0xA7]) (Effect.post (repZeroEffect p 4)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0x67, 0xF3, 0x66, 0xA7] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repe_cmpsw_a32_step_zero s h.midRep [0x67, 0xF3, 0x66] (scanPrefix_asz_cons (by simp [scanPrefix_f3, scanPrefix_66])) (by simp)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      hcodeS hlow hpre.rcxZero

structure RepeCmpsbA32Loop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF3, 0xA6]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^32
  bound : m < count
  srcLow : (rsi.read s).toNat + 1 * (m + 1) < 2^32
  dstLow : (rdi.read s).toNat + 1 * (m + 1) < 2^32
  srcMem : ∀ i < 1 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 1 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = count

theorem RepeCmpsbA32Loop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpsbA32Loop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepeCmpsbA32Loop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {s : RamState} {count m : Nat} (h : RepeCmpsbA32Loop s count m) :
    X86.Machine.step s = some (.next (repeCmpsAfter 8 3 s)) := by
  have := h.srcLow
  have := h.dstLow
  exact repe_cmpsb_a32_step hcm s h.ready [0x67, 0xF3] (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩ ⟨by omega, fun i hi => h.dstMem i (by omega)⟩
    (by omega) (by omega)
    (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.countLt; omega)]; exact h.countLt)

theorem RepeCmpsbA32Loop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpsbA32Loop s count (m + 1)) : repeCmpsCont 8 s = true := by
  have he := h.equal 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repeCmpsCont
  rw [cmpSpec_ZF, he, beq_self_eq_true, hc']
  rfl

theorem RepeCmpsbA32Loop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepeCmpsbA32Loop s count 0) : repeCmpsCont 8 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repeCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  · simp [h.counter]

theorem RepeCmpsbA32Loop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepeCmpsbA32Loop s (count + 1) (m + 1)) : RepeCmpsbA32Loop (repeCmpsAfter 8 3 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repeCmpsAfter 8 3 s).RIP = s.RIP := by
    rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repeCmpsAfter 8 3 s).RFLAGS = s.RFLAGS := by
    rw [repeCmpsAfter_rflags, hc]
    rfl
  have hs : rsi.read (repeCmpsAfter 8 3 s) = rsi.read s + BitVec.ofNat 64 1 := repeCmpsAfter_rsi 8 3 s
  have hd : rdi.read (repeCmpsAfter 8 3 s) = rdi.read s + BitVec.ofNat 64 1 := repeCmpsAfter_rdi 8 3 s
  have hsn : (rsi.read (repeCmpsAfter 8 3 s)).toNat = (rsi.read s).toNat + 1 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repeCmpsAfter 8 3 s)).toNat = (rdi.read s).toNat + 1 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 8).read (repeCmpsAfter 8 3 s) = (Operand.mem a : Operand 8).read s := by
    simp only [Operand.read, repeCmpsAfter_external]
  refine ⟨h.ready.repeCmps 8 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repeCmpsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repeCmpsAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repeCmpsAfter_external]
    exact h.srcMem (1 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repeCmpsAfter_external]
    exact h.dstMem (1 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 1 + 1 * i = 1 * (i + 1) by omega]
    exact h.equal (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 1 + 1 * m = 1 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepeCmpsbA32Done [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (1 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (1 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repe_cmpsb_a32_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepeCmpsbA32Loop s count m →
      RepeCmpsbA32Done s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repeCmpsAfter 8 3 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repeCmpsAfter 8 3 s).Repeat_String_Operation = false := by
      rw [repeCmpsAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repeCmps 8 3).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repeCmpsAfter_rsi]
    · rw [repeCmpsAfter_rdi]
    · rw [repeCmpsAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repeCmpsAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repeCmps 8 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repeCmpsAfter 8 3 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repeCmpsAfter 8 3 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repeCmpsAfter 8 3 s).RIP = s.RIP := by
      rw [repeCmpsAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repeCmpsAfter 8 3 s).RFLAGS = s.RFLAGS := by
      rw [repeCmpsAfter_rflags, hc]
      rfl
    have hs : rsi.read (repeCmpsAfter 8 3 s) = rsi.read s + BitVec.ofNat 64 1 := repeCmpsAfter_rsi 8 3 s
    have hd : rdi.read (repeCmpsAfter 8 3 s) = rdi.read s + BitVec.ofNat 64 1 := repeCmpsAfter_rdi 8 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 8).read (repeCmpsAfter 8 3 s) = (Operand.mem a : Operand 8).read s := by
      simp only [Operand.read, repeCmpsAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 1 + 1 * m = 1 * (m + 1) by omega]
    · refine ((AgreesExcept.repeCmps 8 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepeCmpsbA32Pre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  rcxLow : (rcx.read s).toNat < 2^32
  srcLow : (rsi.read s).toNat + 1 * (m + 1) < 2^32
  dstLow : (rdi.read s).toNat + 1 * (m + 1) < 2^32
  srcMem : ∀ i < 1 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 1 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  equal : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = (rcx.read s).toNat

def repeCmpsbA32Effect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (1 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (1 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)))

@[simp] theorem repeCmpsbA32Effect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repeCmpsbA32Effect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repeCmpsbA32Effect, Effect.components]

theorem repe_cmpsb_a32_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF3, 0xA6]) s) (hpre : RepeCmpsbA32Pre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF3, 0xA6]) t ∧ (repeCmpsbA32Effect p m s).Holds s t := by
  intro t
  have hloop : RepeCmpsbA32Loop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hpre.rcxLow, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.equal, hpre.stop⟩
  have hd := repe_cmpsb_a32_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repeCmpsbA32Effect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repeCmpsbA32Effect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repe_cmpsb_a32_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepeCmpsbA32Pre p m) (codeRange p [0x67, 0xF3, 0xA6]) (Effect.post (repeCmpsbA32Effect p m)) :=
  fun s h hcode hpre => ⟨_, repe_cmpsb_a32_steps hcm p m s h hcode hpre⟩

theorem repe_cmpsb_a32_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0x67, 0xF3, 0xA6]) (Effect.post (repZeroEffect p 3)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0x67, 0xF3, 0xA6] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repe_cmpsb_a32_step_zero s h.midRep [0x67, 0xF3] (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      hcodeS hlow hpre.rcxZero

attribute [x86_compose] repeCmpsqEffect repeCmpsqSegEffect repeCmpsdEffect repeCmpsdSegEffect repeCmpswEffect repeCmpswSegEffect repeCmpsbEffect repeCmpsbSegEffect repeCmpsqA32Effect repeCmpsdA32Effect repeCmpswA32Effect repeCmpsbA32Effect

@[x86_local] theorem repeCmpsqEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeCmpsqEffect p m) := by
  effect_local [repeCmpsqEffect]

@[x86_local] theorem repeCmpsqSegEffect_local {p base : BitVec 64} {m : Nat} :
    Effect.Local (repeCmpsqSegEffect p base m) := by
  effect_local [repeCmpsqSegEffect]

@[x86_local] theorem repeCmpsdEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeCmpsdEffect p m) := by
  effect_local [repeCmpsdEffect]

@[x86_local] theorem repeCmpsdSegEffect_local {p base : BitVec 64} {m : Nat} :
    Effect.Local (repeCmpsdSegEffect p base m) := by
  effect_local [repeCmpsdSegEffect]

@[x86_local] theorem repeCmpswEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeCmpswEffect p m) := by
  effect_local [repeCmpswEffect]

@[x86_local] theorem repeCmpswSegEffect_local {p base : BitVec 64} {m : Nat} :
    Effect.Local (repeCmpswSegEffect p base m) := by
  effect_local [repeCmpswSegEffect]

@[x86_local] theorem repeCmpsbEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeCmpsbEffect p m) := by
  effect_local [repeCmpsbEffect]

@[x86_local] theorem repeCmpsbSegEffect_local {p base : BitVec 64} {m : Nat} :
    Effect.Local (repeCmpsbSegEffect p base m) := by
  effect_local [repeCmpsbSegEffect]

@[x86_local] theorem repeCmpsqA32Effect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeCmpsqA32Effect p m) := by
  effect_local [repeCmpsqA32Effect]

@[x86_local] theorem repeCmpsdA32Effect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeCmpsdA32Effect p m) := by
  effect_local [repeCmpsdA32Effect]

@[x86_local] theorem repeCmpswA32Effect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeCmpswA32Effect p m) := by
  effect_local [repeCmpswA32Effect]

@[x86_local] theorem repeCmpsbA32Effect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repeCmpsbA32Effect p m) := by
  effect_local [repeCmpsbA32Effect]

end X86Proofs
