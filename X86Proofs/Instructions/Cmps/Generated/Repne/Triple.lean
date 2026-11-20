
import X86Proofs.Instructions.Cmps.Generated.Repne.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

structure RepneCmpsqLoop [Bindings] (rex : UInt8) (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF2, rex, 0xA7]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  srcLow : (rsi.read s).toNat + 8 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 8 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 8 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = count

theorem RepneCmpsqLoop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepneCmpsqLoop rex s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepneCmpsqLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState} {count m : Nat} (h : RepneCmpsqLoop rex s count m) :
    X86.Machine.step s = some (.next (repneCmpsAfter 64 3 s)) := by
  have hr := hrex.rexPrefix
  have := h.srcLow
  have := h.dstLow
  exact repne_cmpsq_step hcm s h.ready [0xF2, rex] (by simp [scanPrefix_f2, hr.scanPrefix]) (by simp)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩ ⟨by omega, fun i hi => h.dstMem i (by omega)⟩

theorem RepneCmpsqLoop.cont_true [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepneCmpsqLoop rex s count (m + 1)) : repneCmpsCont 64 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneCmpsCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneCmpsqLoop.cont_false [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepneCmpsqLoop rex s count 0) : repneCmpsCont 64 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repneCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneCmpsqLoop.next [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepneCmpsqLoop rex s (count + 1) (m + 1)) : RepneCmpsqLoop rex (repneCmpsAfter 64 3 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneCmpsAfter 64 3 s).RIP = s.RIP := by
    rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneCmpsAfter 64 3 s).RFLAGS = s.RFLAGS := by
    rw [repneCmpsAfter_rflags, hc]
    rfl
  have hs : rsi.read (repneCmpsAfter 64 3 s) = rsi.read s + BitVec.ofNat 64 8 := repneCmpsAfter_rsi 64 3 s
  have hd : rdi.read (repneCmpsAfter 64 3 s) = rdi.read s + BitVec.ofNat 64 8 := repneCmpsAfter_rdi 64 3 s
  have hsn : (rsi.read (repneCmpsAfter 64 3 s)).toNat = (rsi.read s).toNat + 8 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repneCmpsAfter 64 3 s)).toNat = (rdi.read s).toNat + 8 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 64).read (repneCmpsAfter 64 3 s) = (Operand.mem a : Operand 64).read s := by
    simp only [Operand.read, repneCmpsAfter_external]
  refine ⟨h.ready.repneCmps 64 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneCmpsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneCmpsAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repneCmpsAfter_external]
    exact h.srcMem (8 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repneCmpsAfter_external]
    exact h.dstMem (8 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 8 + 8 * i = 8 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 8 + 8 * m = 8 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneCmpsqDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (8 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (8 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_cmpsq_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneCmpsqLoop rex s count m →
      RepneCmpsqDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneCmpsAfter 64 3 s) := nextState_of_step (h.step hcm hrex )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneCmpsAfter 64 3 s).Repeat_String_Operation = false := by
      rw [repneCmpsAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneCmps 64 3).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneCmpsAfter_rsi]
    · rw [repneCmpsAfter_rdi]
    · rw [repneCmpsAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneCmpsAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneCmps 64 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneCmpsAfter 64 3 s) := nextState_of_step (h.step hcm hrex )
    have hc := h.cont_true
    have ih' := ih c (repneCmpsAfter 64 3 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repneCmpsAfter 64 3 s).RIP = s.RIP := by
      rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneCmpsAfter 64 3 s).RFLAGS = s.RFLAGS := by
      rw [repneCmpsAfter_rflags, hc]
      rfl
    have hs : rsi.read (repneCmpsAfter 64 3 s) = rsi.read s + BitVec.ofNat 64 8 := repneCmpsAfter_rsi 64 3 s
    have hd : rdi.read (repneCmpsAfter 64 3 s) = rdi.read s + BitVec.ofNat 64 8 := repneCmpsAfter_rdi 64 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 64).read (repneCmpsAfter 64 3 s) = (Operand.mem a : Operand 64).read s := by
      simp only [Operand.read, repneCmpsAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 8 + 8 * m = 8 * (m + 1) by omega]
    · refine ((AgreesExcept.repneCmps 64 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneCmpsqPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  srcLow : (rsi.read s).toNat + 8 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 8 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 8 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = (rcx.read s).toNat

def repneCmpsqEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (8 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (8 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)))

@[simp] theorem repneCmpsqEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneCmpsqEffect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repneCmpsqEffect, Effect.components]

theorem repne_cmpsq_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, rex, 0xA7]) s) (hpre : RepneCmpsqPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, rex, 0xA7]) t ∧ (repneCmpsqEffect p m s).Holds s t := by
  intro t
  have hloop : RepneCmpsqLoop rex s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_cmpsq_loop hcm hrex m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneCmpsqEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneCmpsqEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repne_cmpsq_triple_of_bytes [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    Triple (RepneCmpsqPre p m) (codeRange p [0xF2, rex, 0xA7]) (Effect.post (repneCmpsqEffect p m)) :=
  fun s h hcode hpre => ⟨_, repne_cmpsq_steps hcm p rex hrex m s h hcode hpre⟩

theorem repne_cmpsq_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepneCmpsqPre p m) (codeRange p [0xF2, 0x48, 0xA7]) (Effect.post (repneCmpsqEffect p m)) :=
  repne_cmpsq_triple_of_bytes hcm p 0x48 (by unfold RexWPrefix; decide) m

structure RepneCmpsqSegLoop [Bindings] (r : SegReg) (base : BitVec 64) (rex : UInt8) (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF2, rex, 0xA7]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  srcLow : (base + rsi.read s).toNat + 8 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 8 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 8 * (m + 1), (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = count
  seg : r.Ready base s

theorem RepneCmpsqSegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepneCmpsqSegLoop r base rex s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepneCmpsqSegLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {r : SegReg} {base : BitVec 64} {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState} {count m : Nat} (h : RepneCmpsqSegLoop r base rex s count m) :
    X86.Machine.step s = some (.next (repneCmpsSegAfter base 64 4 s)) := by
  have hr := hrex.rexPrefix
  have := h.srcLow
  have := h.dstLow
  have hsrc : MemReadable s (base + rsi.read s) 8 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2, rex] =
      withSeg (repneRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF2, rex] (noSegPrefix_cons noSegPrefix_f2 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_f2_rex _ _ hr]
  have hstep := repne_cmpsq_seg_step hcm s h.ready [r.prefixByte, 0xF2, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_f2, hr.scanPrefix])) (by simp)
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

theorem RepneCmpsqSegLoop.cont_true [Bindings] {r : SegReg} {base : BitVec 64} {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepneCmpsqSegLoop r base rex s count (m + 1)) : repneCmpsSegCont base 64 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneCmpsSegCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneCmpsqSegLoop.cont_false [Bindings] {r : SegReg} {base : BitVec 64} {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepneCmpsqSegLoop r base rex s count 0) : repneCmpsSegCont base 64 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repneCmpsSegCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneCmpsqSegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepneCmpsqSegLoop r base rex s (count + 1) (m + 1)) : RepneCmpsqSegLoop r base rex (repneCmpsSegAfter base 64 4 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneCmpsSegAfter base 64 4 s).RIP = s.RIP := by
    rw [repneCmpsSegAfter_rip base _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneCmpsSegAfter base 64 4 s).RFLAGS = s.RFLAGS := by
    rw [repneCmpsSegAfter_rflags, hc]
    rfl
  have hs : base + rsi.read (repneCmpsSegAfter base 64 4 s) = base + rsi.read s + BitVec.ofNat 64 8 := by
    rw [repneCmpsSegAfter_rsi base 64 4 s, BitVec.add_assoc]
  have hd : rdi.read (repneCmpsSegAfter base 64 4 s) = rdi.read s + BitVec.ofNat 64 8 := repneCmpsSegAfter_rdi base 64 4 s
  have hsn : (base + rsi.read (repneCmpsSegAfter base 64 4 s)).toNat = (base + rsi.read s).toNat + 8 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repneCmpsSegAfter base 64 4 s)).toNat = (rdi.read s).toNat + 8 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 64).read (repneCmpsSegAfter base 64 4 s) = (Operand.mem a : Operand 64).read s := by
    simp only [Operand.read, repneCmpsSegAfter_external]
  refine ⟨h.ready.repneCmpsSeg base 64 4, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    repneCmpsSegAfter_segReady base 64 4 s h.seg⟩
  · intro i hi
    rw [hrip, repneCmpsSegAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneCmpsSegAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repneCmpsSegAfter_external]
    exact h.srcMem (8 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repneCmpsSegAfter_external]
    exact h.dstMem (8 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 8 + 8 * i = 8 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 8 + 8 * m = 8 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneCmpsqSegDone [Bindings] (base : BitVec 64) (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 4)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (8 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (8 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_cmpsq_seg_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {r : SegReg} {base : BitVec 64} {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneCmpsqSegLoop r base rex s count m →
      RepneCmpsqSegDone base s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneCmpsSegAfter base 64 4 s) := nextState_of_step (h.step hcm hrex )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneCmpsSegAfter base 64 4 s).Repeat_String_Operation = false := by
      rw [repneCmpsSegAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneCmpsSeg base 64 4).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneCmpsSegAfter_rip base _ _ s h.ready.msr, hc]; rfl
    · rw [repneCmpsSegAfter_rsi]
    · rw [repneCmpsSegAfter_rdi]
    · rw [repneCmpsSegAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneCmpsSegAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneCmpsSeg base 64 4 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneCmpsSegAfter base 64 4 s) := nextState_of_step (h.step hcm hrex )
    have hc := h.cont_true
    have ih' := ih c (repneCmpsSegAfter base 64 4 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repneCmpsSegAfter base 64 4 s).RIP = s.RIP := by
      rw [repneCmpsSegAfter_rip base _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneCmpsSegAfter base 64 4 s).RFLAGS = s.RFLAGS := by
      rw [repneCmpsSegAfter_rflags, hc]
      rfl
    have hsreg : rsi.read (repneCmpsSegAfter base 64 4 s) = rsi.read s + BitVec.ofNat 64 8 :=
      repneCmpsSegAfter_rsi base 64 4 s
    have hs : base + rsi.read (repneCmpsSegAfter base 64 4 s) = base + rsi.read s + BitVec.ofNat 64 8 := by
      rw [hsreg, BitVec.add_assoc]
    have hd : rdi.read (repneCmpsSegAfter base 64 4 s) = rdi.read s + BitVec.ofNat 64 8 := repneCmpsSegAfter_rdi base 64 4 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 64).read (repneCmpsSegAfter base 64 4 s) = (Operand.mem a : Operand 64).read s := by
      simp only [Operand.read, repneCmpsSegAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hsreg, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 8 + 8 * m = 8 * (m + 1) by omega]
    · refine ((AgreesExcept.repneCmpsSeg base 64 4 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneCmpsqSegPre (p : BitVec 64) (r : SegReg) (base : BitVec 64) (m : Nat)
    (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  srcLow : (base + rsi.read s).toNat + 8 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 8 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 8 * (m + 1), (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = (rcx.read s).toNat
  seg : r.Ready base s

def repneCmpsqSegEffect (p base : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 4
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (8 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (8 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)))

@[simp] theorem repneCmpsqSegEffect_components (p base : BitVec 64) (m : Nat) (s : RamState) :
    (repneCmpsqSegEffect p base m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repneCmpsqSegEffect, Effect.components]

theorem repne_cmpsq_seg_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF2, rex, 0xA7]) s) (hpre : RepneCmpsqSegPre p r base m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF2, rex, 0xA7]) t ∧ (repneCmpsqSegEffect p base m s).Holds s t := by
  intro t
  have hloop : RepneCmpsqSegLoop r base rex s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.differ, hpre.stop, hpre.seg⟩
  have hd := repne_cmpsq_seg_loop hcm hrex m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneCmpsqSegEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneCmpsqSegEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repne_cmpsq_seg_triple_of_bytes [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    Triple (RepneCmpsqSegPre p r base m) (codeRange p [r.prefixByte, 0xF2, rex, 0xA7]) (Effect.post (repneCmpsqSegEffect p base m)) :=
  fun s h hcode hpre => ⟨_, repne_cmpsq_seg_steps hcm p r base rex hrex m s h hcode hpre⟩

theorem repne_cmpsq_seg_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (m : Nat) :
    Triple (RepneCmpsqSegPre p r base m) (codeRange p [r.prefixByte, 0xF2, 0x48, 0xA7]) (Effect.post (repneCmpsqSegEffect p base m)) :=
  repne_cmpsq_seg_triple_of_bytes hcm p r base 0x48 (by unfold RexWPrefix; decide) m

theorem repne_cmpsq_zero_triple_of_bytes [Bindings] (p : BitVec 64)
    (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepZeroPre p) (codeRange p [0xF2, rex, 0xA7]) (Effect.post (repZeroEffect p 3)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hr := hrex.rexPrefix
    have hcodeS : BytesAt s s.RIP [0xF2, rex, 0xA7] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repne_cmpsq_step_zero s h.midRep [0xF2, rex] (by simp [scanPrefix_f2, hr.scanPrefix]) (by simp)
      (by rw [scanContext_f2_rex _ _ hr]; rfl)
      (by rw [scanContext_f2_rex _ _ hr]; exact hrex.rex_w s.DS)
      (by rw [scanContext_f2_rex _ _ hr]; rfl)
      (by rw [scanContext_f2_rex _ _ hr]; rfl)
      (by rw [scanContext_f2_rex _ _ hr]; rfl)
      (by rw [scanContext_f2_rex _ _ hr]; rfl)
      hcodeS hlow hpre.rcxZero

theorem repne_cmpsq_zero_triple [Bindings] (p : BitVec 64) :
    Triple (RepZeroPre p) (codeRange p [0xF2, 0x48, 0xA7]) (Effect.post (repZeroEffect p 3)) :=
  repne_cmpsq_zero_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide)

theorem repne_cmpsq_seg_zero_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepZeroPre p) (codeRange p [r.prefixByte, 0xF2, rex, 0xA7]) (Effect.post (repZeroEffect p 4)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hr := hrex.rexPrefix
    have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF2, rex, 0xA7] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2, rex] =
        withSeg (repneRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
      rw [scanContext_seg_cons _ _ r [0xF2, rex] (noSegPrefix_cons noSegPrefix_f2 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_f2_rex _ _ hr]
    exact repne_cmpsq_step_zero s h.midRep [r.prefixByte, 0xF2, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_f2, hr.scanPrefix])) (by simp)
      (by rw [hsc]; rfl)
      (by rw [hsc]; exact hrex.rex_w s.DS)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      hcodeS hlow hpre.rcxZero

theorem repne_cmpsq_seg_zero_triple [Bindings] (p : BitVec 64) (r : SegReg) :
    Triple (RepZeroPre p) (codeRange p [r.prefixByte, 0xF2, 0x48, 0xA7]) (Effect.post (repZeroEffect p 4)) :=
  repne_cmpsq_seg_zero_triple_of_bytes p r 0x48 (by unfold RexWPrefix; decide)

structure RepneCmpsdLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF2, 0xA7]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  srcLow : (rsi.read s).toNat + 4 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 4 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 4 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = count

theorem RepneCmpsdLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpsdLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepneCmpsdLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {s : RamState} {count m : Nat} (h : RepneCmpsdLoop s count m) :
    X86.Machine.step s = some (.next (repneCmpsAfter 32 2 s)) := by
  have := h.srcLow
  have := h.dstLow
  exact repne_cmpsd_step hcm s h.ready [0xF2] (by simpa using scanPrefix_f2) (by simp)
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

theorem RepneCmpsdLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpsdLoop s count (m + 1)) : repneCmpsCont 32 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneCmpsCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneCmpsdLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepneCmpsdLoop s count 0) : repneCmpsCont 32 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repneCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneCmpsdLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpsdLoop s (count + 1) (m + 1)) : RepneCmpsdLoop (repneCmpsAfter 32 2 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneCmpsAfter 32 2 s).RIP = s.RIP := by
    rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneCmpsAfter 32 2 s).RFLAGS = s.RFLAGS := by
    rw [repneCmpsAfter_rflags, hc]
    rfl
  have hs : rsi.read (repneCmpsAfter 32 2 s) = rsi.read s + BitVec.ofNat 64 4 := repneCmpsAfter_rsi 32 2 s
  have hd : rdi.read (repneCmpsAfter 32 2 s) = rdi.read s + BitVec.ofNat 64 4 := repneCmpsAfter_rdi 32 2 s
  have hsn : (rsi.read (repneCmpsAfter 32 2 s)).toNat = (rsi.read s).toNat + 4 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repneCmpsAfter 32 2 s)).toNat = (rdi.read s).toNat + 4 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 32).read (repneCmpsAfter 32 2 s) = (Operand.mem a : Operand 32).read s := by
    simp only [Operand.read, repneCmpsAfter_external]
  refine ⟨h.ready.repneCmps 32 2, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneCmpsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneCmpsAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repneCmpsAfter_external]
    exact h.srcMem (4 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repneCmpsAfter_external]
    exact h.dstMem (4 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 4 + 4 * i = 4 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 4 + 4 * m = 4 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneCmpsdDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (4 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (4 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_cmpsd_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneCmpsdLoop s count m →
      RepneCmpsdDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneCmpsAfter 32 2 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneCmpsAfter 32 2 s).Repeat_String_Operation = false := by
      rw [repneCmpsAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneCmps 32 2).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneCmpsAfter_rsi]
    · rw [repneCmpsAfter_rdi]
    · rw [repneCmpsAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneCmpsAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneCmps 32 2 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneCmpsAfter 32 2 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repneCmpsAfter 32 2 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repneCmpsAfter 32 2 s).RIP = s.RIP := by
      rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneCmpsAfter 32 2 s).RFLAGS = s.RFLAGS := by
      rw [repneCmpsAfter_rflags, hc]
      rfl
    have hs : rsi.read (repneCmpsAfter 32 2 s) = rsi.read s + BitVec.ofNat 64 4 := repneCmpsAfter_rsi 32 2 s
    have hd : rdi.read (repneCmpsAfter 32 2 s) = rdi.read s + BitVec.ofNat 64 4 := repneCmpsAfter_rdi 32 2 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 32).read (repneCmpsAfter 32 2 s) = (Operand.mem a : Operand 32).read s := by
      simp only [Operand.read, repneCmpsAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 4 + 4 * m = 4 * (m + 1) by omega]
    · refine ((AgreesExcept.repneCmps 32 2 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneCmpsdPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  srcLow : (rsi.read s).toNat + 4 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 4 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 4 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = (rcx.read s).toNat

def repneCmpsdEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (4 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (4 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)))

@[simp] theorem repneCmpsdEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneCmpsdEffect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repneCmpsdEffect, Effect.components]

theorem repne_cmpsd_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, 0xA7]) s) (hpre : RepneCmpsdPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, 0xA7]) t ∧ (repneCmpsdEffect p m s).Holds s t := by
  intro t
  have hloop : RepneCmpsdLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_cmpsd_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneCmpsdEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneCmpsdEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repne_cmpsd_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepneCmpsdPre p m) (codeRange p [0xF2, 0xA7]) (Effect.post (repneCmpsdEffect p m)) :=
  fun s h hcode hpre => ⟨_, repne_cmpsd_steps hcm p m s h hcode hpre⟩

structure RepneCmpsdSegLoop [Bindings] (r : SegReg) (base : BitVec 64) (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF2, 0xA7]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  srcLow : (base + rsi.read s).toNat + 4 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 4 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 4 * (m + 1), (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = count
  seg : r.Ready base s

theorem RepneCmpsdSegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat}
    (h : RepneCmpsdSegLoop r base s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepneCmpsdSegLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat} (h : RepneCmpsdSegLoop r base s count m) :
    X86.Machine.step s = some (.next (repneCmpsSegAfter base 32 3 s)) := by
  have := h.srcLow
  have := h.dstLow
  have hsrc : MemReadable s (base + rsi.read s) 4 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF2]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF2] (noSegPrefix_cons noSegPrefix_f2 noSegPrefix_nil)]
  have hstep := repne_cmpsd_seg_step hcm s h.ready [r.prefixByte, 0xF2] (scanPrefix_seg_cons r (by simpa using scanPrefix_f2)) (by simp)
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

theorem RepneCmpsdSegLoop.cont_true [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat}
    (h : RepneCmpsdSegLoop r base s count (m + 1)) : repneCmpsSegCont base 32 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneCmpsSegCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneCmpsdSegLoop.cont_false [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepneCmpsdSegLoop r base s count 0) : repneCmpsSegCont base 32 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repneCmpsSegCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneCmpsdSegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat}
    (h : RepneCmpsdSegLoop r base s (count + 1) (m + 1)) : RepneCmpsdSegLoop r base (repneCmpsSegAfter base 32 3 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneCmpsSegAfter base 32 3 s).RIP = s.RIP := by
    rw [repneCmpsSegAfter_rip base _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneCmpsSegAfter base 32 3 s).RFLAGS = s.RFLAGS := by
    rw [repneCmpsSegAfter_rflags, hc]
    rfl
  have hs : base + rsi.read (repneCmpsSegAfter base 32 3 s) = base + rsi.read s + BitVec.ofNat 64 4 := by
    rw [repneCmpsSegAfter_rsi base 32 3 s, BitVec.add_assoc]
  have hd : rdi.read (repneCmpsSegAfter base 32 3 s) = rdi.read s + BitVec.ofNat 64 4 := repneCmpsSegAfter_rdi base 32 3 s
  have hsn : (base + rsi.read (repneCmpsSegAfter base 32 3 s)).toNat = (base + rsi.read s).toNat + 4 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repneCmpsSegAfter base 32 3 s)).toNat = (rdi.read s).toNat + 4 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 32).read (repneCmpsSegAfter base 32 3 s) = (Operand.mem a : Operand 32).read s := by
    simp only [Operand.read, repneCmpsSegAfter_external]
  refine ⟨h.ready.repneCmpsSeg base 32 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    repneCmpsSegAfter_segReady base 32 3 s h.seg⟩
  · intro i hi
    rw [hrip, repneCmpsSegAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneCmpsSegAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repneCmpsSegAfter_external]
    exact h.srcMem (4 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repneCmpsSegAfter_external]
    exact h.dstMem (4 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 4 + 4 * i = 4 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 4 + 4 * m = 4 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneCmpsdSegDone [Bindings] (base : BitVec 64) (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (4 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (4 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_cmpsd_seg_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {r : SegReg} {base : BitVec 64} (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneCmpsdSegLoop r base s count m →
      RepneCmpsdSegDone base s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneCmpsSegAfter base 32 3 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneCmpsSegAfter base 32 3 s).Repeat_String_Operation = false := by
      rw [repneCmpsSegAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneCmpsSeg base 32 3).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneCmpsSegAfter_rip base _ _ s h.ready.msr, hc]; rfl
    · rw [repneCmpsSegAfter_rsi]
    · rw [repneCmpsSegAfter_rdi]
    · rw [repneCmpsSegAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneCmpsSegAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneCmpsSeg base 32 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneCmpsSegAfter base 32 3 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repneCmpsSegAfter base 32 3 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repneCmpsSegAfter base 32 3 s).RIP = s.RIP := by
      rw [repneCmpsSegAfter_rip base _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneCmpsSegAfter base 32 3 s).RFLAGS = s.RFLAGS := by
      rw [repneCmpsSegAfter_rflags, hc]
      rfl
    have hsreg : rsi.read (repneCmpsSegAfter base 32 3 s) = rsi.read s + BitVec.ofNat 64 4 :=
      repneCmpsSegAfter_rsi base 32 3 s
    have hs : base + rsi.read (repneCmpsSegAfter base 32 3 s) = base + rsi.read s + BitVec.ofNat 64 4 := by
      rw [hsreg, BitVec.add_assoc]
    have hd : rdi.read (repneCmpsSegAfter base 32 3 s) = rdi.read s + BitVec.ofNat 64 4 := repneCmpsSegAfter_rdi base 32 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 32).read (repneCmpsSegAfter base 32 3 s) = (Operand.mem a : Operand 32).read s := by
      simp only [Operand.read, repneCmpsSegAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hsreg, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 4 + 4 * m = 4 * (m + 1) by omega]
    · refine ((AgreesExcept.repneCmpsSeg base 32 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneCmpsdSegPre (p : BitVec 64) (r : SegReg) (base : BitVec 64) (m : Nat)
    (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  srcLow : (base + rsi.read s).toNat + 4 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 4 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 4 * (m + 1), (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = (rcx.read s).toNat
  seg : r.Ready base s

def repneCmpsdSegEffect (p base : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (4 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (4 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)))

@[simp] theorem repneCmpsdSegEffect_components (p base : BitVec 64) (m : Nat) (s : RamState) :
    (repneCmpsdSegEffect p base m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repneCmpsdSegEffect, Effect.components]

theorem repne_cmpsd_seg_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF2, 0xA7]) s) (hpre : RepneCmpsdSegPre p r base m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF2, 0xA7]) t ∧ (repneCmpsdSegEffect p base m s).Holds s t := by
  intro t
  have hloop : RepneCmpsdSegLoop r base s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.differ, hpre.stop, hpre.seg⟩
  have hd := repne_cmpsd_seg_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneCmpsdSegEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneCmpsdSegEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repne_cmpsd_seg_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (m : Nat) :
    Triple (RepneCmpsdSegPre p r base m) (codeRange p [r.prefixByte, 0xF2, 0xA7]) (Effect.post (repneCmpsdSegEffect p base m)) :=
  fun s h hcode hpre => ⟨_, repne_cmpsd_seg_steps hcm p r base m s h hcode hpre⟩

theorem repne_cmpsd_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0xF2, 0xA7]) (Effect.post (repZeroEffect p 2)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0xF2, 0xA7] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repne_cmpsd_step_zero s h.midRep [0xF2] (by simpa using scanPrefix_f2) (by simp)
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      hcodeS hlow hpre.rcxZero

theorem repne_cmpsd_seg_zero_triple [Bindings] (p : BitVec 64) (r : SegReg)
    :
    Triple (RepZeroPre p) (codeRange p [r.prefixByte, 0xF2, 0xA7]) (Effect.post (repZeroEffect p 3)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF2, 0xA7] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2] =
        withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF2]) (r.select (PrefixSegments.ofState s)) := by
      rw [scanContext_seg_cons _ _ r [0xF2] (noSegPrefix_cons noSegPrefix_f2 noSegPrefix_nil)]
    exact repne_cmpsd_step_zero s h.midRep [r.prefixByte, 0xF2] (scanPrefix_seg_cons r (by simpa using scanPrefix_f2)) (by simp)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      hcodeS hlow hpre.rcxZero

structure RepneCmpswLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF2, 0x66, 0xA7]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  srcLow : (rsi.read s).toNat + 2 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 2 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 2 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 2 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = count

theorem RepneCmpswLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpswLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepneCmpswLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {s : RamState} {count m : Nat} (h : RepneCmpswLoop s count m) :
    X86.Machine.step s = some (.next (repneCmpsAfter 16 3 s)) := by
  have := h.srcLow
  have := h.dstLow
  exact repne_cmpsw_step hcm s h.ready [0xF2, 0x66] (by simp [scanPrefix_f2, scanPrefix_66]) (by simp)
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

theorem RepneCmpswLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpswLoop s count (m + 1)) : repneCmpsCont 16 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneCmpsCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneCmpswLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepneCmpswLoop s count 0) : repneCmpsCont 16 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repneCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneCmpswLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpswLoop s (count + 1) (m + 1)) : RepneCmpswLoop (repneCmpsAfter 16 3 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneCmpsAfter 16 3 s).RIP = s.RIP := by
    rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneCmpsAfter 16 3 s).RFLAGS = s.RFLAGS := by
    rw [repneCmpsAfter_rflags, hc]
    rfl
  have hs : rsi.read (repneCmpsAfter 16 3 s) = rsi.read s + BitVec.ofNat 64 2 := repneCmpsAfter_rsi 16 3 s
  have hd : rdi.read (repneCmpsAfter 16 3 s) = rdi.read s + BitVec.ofNat 64 2 := repneCmpsAfter_rdi 16 3 s
  have hsn : (rsi.read (repneCmpsAfter 16 3 s)).toNat = (rsi.read s).toNat + 2 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repneCmpsAfter 16 3 s)).toNat = (rdi.read s).toNat + 2 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 16).read (repneCmpsAfter 16 3 s) = (Operand.mem a : Operand 16).read s := by
    simp only [Operand.read, repneCmpsAfter_external]
  refine ⟨h.ready.repneCmps 16 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneCmpsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneCmpsAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repneCmpsAfter_external]
    exact h.srcMem (2 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repneCmpsAfter_external]
    exact h.dstMem (2 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 2 + 2 * i = 2 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 2 + 2 * m = 2 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneCmpswDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (2 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (2 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_cmpsw_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneCmpswLoop s count m →
      RepneCmpswDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneCmpsAfter 16 3 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneCmpsAfter 16 3 s).Repeat_String_Operation = false := by
      rw [repneCmpsAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneCmps 16 3).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneCmpsAfter_rsi]
    · rw [repneCmpsAfter_rdi]
    · rw [repneCmpsAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneCmpsAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneCmps 16 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneCmpsAfter 16 3 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repneCmpsAfter 16 3 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repneCmpsAfter 16 3 s).RIP = s.RIP := by
      rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneCmpsAfter 16 3 s).RFLAGS = s.RFLAGS := by
      rw [repneCmpsAfter_rflags, hc]
      rfl
    have hs : rsi.read (repneCmpsAfter 16 3 s) = rsi.read s + BitVec.ofNat 64 2 := repneCmpsAfter_rsi 16 3 s
    have hd : rdi.read (repneCmpsAfter 16 3 s) = rdi.read s + BitVec.ofNat 64 2 := repneCmpsAfter_rdi 16 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 16).read (repneCmpsAfter 16 3 s) = (Operand.mem a : Operand 16).read s := by
      simp only [Operand.read, repneCmpsAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 2 + 2 * m = 2 * (m + 1) by omega]
    · refine ((AgreesExcept.repneCmps 16 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneCmpswPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  srcLow : (rsi.read s).toNat + 2 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 2 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 2 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 2 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = (rcx.read s).toNat

def repneCmpswEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (2 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (2 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)))

@[simp] theorem repneCmpswEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneCmpswEffect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repneCmpswEffect, Effect.components]

theorem repne_cmpsw_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, 0x66, 0xA7]) s) (hpre : RepneCmpswPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, 0x66, 0xA7]) t ∧ (repneCmpswEffect p m s).Holds s t := by
  intro t
  have hloop : RepneCmpswLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_cmpsw_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneCmpswEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneCmpswEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repne_cmpsw_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepneCmpswPre p m) (codeRange p [0xF2, 0x66, 0xA7]) (Effect.post (repneCmpswEffect p m)) :=
  fun s h hcode hpre => ⟨_, repne_cmpsw_steps hcm p m s h hcode hpre⟩

structure RepneCmpswSegLoop [Bindings] (r : SegReg) (base : BitVec 64) (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF2, 0x66, 0xA7]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  srcLow : (base + rsi.read s).toNat + 2 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 2 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 2 * (m + 1), (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 2 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = count
  seg : r.Ready base s

theorem RepneCmpswSegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat}
    (h : RepneCmpswSegLoop r base s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepneCmpswSegLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat} (h : RepneCmpswSegLoop r base s count m) :
    X86.Machine.step s = some (.next (repneCmpsSegAfter base 16 4 s)) := by
  have := h.srcLow
  have := h.dstLow
  have hsrc : MemReadable s (base + rsi.read s) 2 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF2, 0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF2, 0x66] (noSegPrefix_cons noSegPrefix_f2 (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil))]
  have hstep := repne_cmpsw_seg_step hcm s h.ready [r.prefixByte, 0xF2, 0x66] (scanPrefix_seg_cons r (by simp [scanPrefix_f2, scanPrefix_66])) (by simp)
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

theorem RepneCmpswSegLoop.cont_true [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat}
    (h : RepneCmpswSegLoop r base s count (m + 1)) : repneCmpsSegCont base 16 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneCmpsSegCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneCmpswSegLoop.cont_false [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepneCmpswSegLoop r base s count 0) : repneCmpsSegCont base 16 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repneCmpsSegCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneCmpswSegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat}
    (h : RepneCmpswSegLoop r base s (count + 1) (m + 1)) : RepneCmpswSegLoop r base (repneCmpsSegAfter base 16 4 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneCmpsSegAfter base 16 4 s).RIP = s.RIP := by
    rw [repneCmpsSegAfter_rip base _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneCmpsSegAfter base 16 4 s).RFLAGS = s.RFLAGS := by
    rw [repneCmpsSegAfter_rflags, hc]
    rfl
  have hs : base + rsi.read (repneCmpsSegAfter base 16 4 s) = base + rsi.read s + BitVec.ofNat 64 2 := by
    rw [repneCmpsSegAfter_rsi base 16 4 s, BitVec.add_assoc]
  have hd : rdi.read (repneCmpsSegAfter base 16 4 s) = rdi.read s + BitVec.ofNat 64 2 := repneCmpsSegAfter_rdi base 16 4 s
  have hsn : (base + rsi.read (repneCmpsSegAfter base 16 4 s)).toNat = (base + rsi.read s).toNat + 2 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repneCmpsSegAfter base 16 4 s)).toNat = (rdi.read s).toNat + 2 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 16).read (repneCmpsSegAfter base 16 4 s) = (Operand.mem a : Operand 16).read s := by
    simp only [Operand.read, repneCmpsSegAfter_external]
  refine ⟨h.ready.repneCmpsSeg base 16 4, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    repneCmpsSegAfter_segReady base 16 4 s h.seg⟩
  · intro i hi
    rw [hrip, repneCmpsSegAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneCmpsSegAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repneCmpsSegAfter_external]
    exact h.srcMem (2 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repneCmpsSegAfter_external]
    exact h.dstMem (2 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 2 + 2 * i = 2 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 2 + 2 * m = 2 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneCmpswSegDone [Bindings] (base : BitVec 64) (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 4)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (2 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (2 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_cmpsw_seg_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {r : SegReg} {base : BitVec 64} (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneCmpswSegLoop r base s count m →
      RepneCmpswSegDone base s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneCmpsSegAfter base 16 4 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneCmpsSegAfter base 16 4 s).Repeat_String_Operation = false := by
      rw [repneCmpsSegAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneCmpsSeg base 16 4).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneCmpsSegAfter_rip base _ _ s h.ready.msr, hc]; rfl
    · rw [repneCmpsSegAfter_rsi]
    · rw [repneCmpsSegAfter_rdi]
    · rw [repneCmpsSegAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneCmpsSegAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneCmpsSeg base 16 4 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneCmpsSegAfter base 16 4 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repneCmpsSegAfter base 16 4 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repneCmpsSegAfter base 16 4 s).RIP = s.RIP := by
      rw [repneCmpsSegAfter_rip base _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneCmpsSegAfter base 16 4 s).RFLAGS = s.RFLAGS := by
      rw [repneCmpsSegAfter_rflags, hc]
      rfl
    have hsreg : rsi.read (repneCmpsSegAfter base 16 4 s) = rsi.read s + BitVec.ofNat 64 2 :=
      repneCmpsSegAfter_rsi base 16 4 s
    have hs : base + rsi.read (repneCmpsSegAfter base 16 4 s) = base + rsi.read s + BitVec.ofNat 64 2 := by
      rw [hsreg, BitVec.add_assoc]
    have hd : rdi.read (repneCmpsSegAfter base 16 4 s) = rdi.read s + BitVec.ofNat 64 2 := repneCmpsSegAfter_rdi base 16 4 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 16).read (repneCmpsSegAfter base 16 4 s) = (Operand.mem a : Operand 16).read s := by
      simp only [Operand.read, repneCmpsSegAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hsreg, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 2 + 2 * m = 2 * (m + 1) by omega]
    · refine ((AgreesExcept.repneCmpsSeg base 16 4 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneCmpswSegPre (p : BitVec 64) (r : SegReg) (base : BitVec 64) (m : Nat)
    (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  srcLow : (base + rsi.read s).toNat + 2 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 2 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 2 * (m + 1), (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 2 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = (rcx.read s).toNat
  seg : r.Ready base s

def repneCmpswSegEffect (p base : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 4
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (2 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (2 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)))

@[simp] theorem repneCmpswSegEffect_components (p base : BitVec 64) (m : Nat) (s : RamState) :
    (repneCmpswSegEffect p base m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repneCmpswSegEffect, Effect.components]

theorem repne_cmpsw_seg_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF2, 0x66, 0xA7]) s) (hpre : RepneCmpswSegPre p r base m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF2, 0x66, 0xA7]) t ∧ (repneCmpswSegEffect p base m s).Holds s t := by
  intro t
  have hloop : RepneCmpswSegLoop r base s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.differ, hpre.stop, hpre.seg⟩
  have hd := repne_cmpsw_seg_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneCmpswSegEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneCmpswSegEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repne_cmpsw_seg_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (m : Nat) :
    Triple (RepneCmpswSegPre p r base m) (codeRange p [r.prefixByte, 0xF2, 0x66, 0xA7]) (Effect.post (repneCmpswSegEffect p base m)) :=
  fun s h hcode hpre => ⟨_, repne_cmpsw_seg_steps hcm p r base m s h hcode hpre⟩

theorem repne_cmpsw_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0xF2, 0x66, 0xA7]) (Effect.post (repZeroEffect p 3)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0xF2, 0x66, 0xA7] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repne_cmpsw_step_zero s h.midRep [0xF2, 0x66] (by simp [scanPrefix_f2, scanPrefix_66]) (by simp)
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      hcodeS hlow hpre.rcxZero

theorem repne_cmpsw_seg_zero_triple [Bindings] (p : BitVec 64) (r : SegReg)
    :
    Triple (RepZeroPre p) (codeRange p [r.prefixByte, 0xF2, 0x66, 0xA7]) (Effect.post (repZeroEffect p 4)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF2, 0x66, 0xA7] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2, 0x66] =
        withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF2, 0x66]) (r.select (PrefixSegments.ofState s)) := by
      rw [scanContext_seg_cons _ _ r [0xF2, 0x66] (noSegPrefix_cons noSegPrefix_f2 (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil))]
    exact repne_cmpsw_step_zero s h.midRep [r.prefixByte, 0xF2, 0x66] (scanPrefix_seg_cons r (by simp [scanPrefix_f2, scanPrefix_66])) (by simp)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      hcodeS hlow hpre.rcxZero

structure RepneCmpsbLoop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF2, 0xA6]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  srcLow : (rsi.read s).toNat + 1 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 1 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 1 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 1 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = count

theorem RepneCmpsbLoop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpsbLoop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepneCmpsbLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {s : RamState} {count m : Nat} (h : RepneCmpsbLoop s count m) :
    X86.Machine.step s = some (.next (repneCmpsAfter 8 2 s)) := by
  have := h.srcLow
  have := h.dstLow
  exact repne_cmpsb_step hcm s h.ready [0xF2] (by simpa using scanPrefix_f2) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩ ⟨by omega, fun i hi => h.dstMem i (by omega)⟩

theorem RepneCmpsbLoop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpsbLoop s count (m + 1)) : repneCmpsCont 8 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneCmpsCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneCmpsbLoop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepneCmpsbLoop s count 0) : repneCmpsCont 8 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repneCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneCmpsbLoop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpsbLoop s (count + 1) (m + 1)) : RepneCmpsbLoop (repneCmpsAfter 8 2 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneCmpsAfter 8 2 s).RIP = s.RIP := by
    rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneCmpsAfter 8 2 s).RFLAGS = s.RFLAGS := by
    rw [repneCmpsAfter_rflags, hc]
    rfl
  have hs : rsi.read (repneCmpsAfter 8 2 s) = rsi.read s + BitVec.ofNat 64 1 := repneCmpsAfter_rsi 8 2 s
  have hd : rdi.read (repneCmpsAfter 8 2 s) = rdi.read s + BitVec.ofNat 64 1 := repneCmpsAfter_rdi 8 2 s
  have hsn : (rsi.read (repneCmpsAfter 8 2 s)).toNat = (rsi.read s).toNat + 1 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repneCmpsAfter 8 2 s)).toNat = (rdi.read s).toNat + 1 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 8).read (repneCmpsAfter 8 2 s) = (Operand.mem a : Operand 8).read s := by
    simp only [Operand.read, repneCmpsAfter_external]
  refine ⟨h.ready.repneCmps 8 2, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneCmpsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneCmpsAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repneCmpsAfter_external]
    exact h.srcMem (1 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repneCmpsAfter_external]
    exact h.dstMem (1 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 1 + 1 * i = 1 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 1 + 1 * m = 1 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneCmpsbDone [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (1 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (1 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_cmpsb_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneCmpsbLoop s count m →
      RepneCmpsbDone s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneCmpsAfter 8 2 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneCmpsAfter 8 2 s).Repeat_String_Operation = false := by
      rw [repneCmpsAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneCmps 8 2).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneCmpsAfter_rsi]
    · rw [repneCmpsAfter_rdi]
    · rw [repneCmpsAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneCmpsAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneCmps 8 2 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneCmpsAfter 8 2 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repneCmpsAfter 8 2 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repneCmpsAfter 8 2 s).RIP = s.RIP := by
      rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneCmpsAfter 8 2 s).RFLAGS = s.RFLAGS := by
      rw [repneCmpsAfter_rflags, hc]
      rfl
    have hs : rsi.read (repneCmpsAfter 8 2 s) = rsi.read s + BitVec.ofNat 64 1 := repneCmpsAfter_rsi 8 2 s
    have hd : rdi.read (repneCmpsAfter 8 2 s) = rdi.read s + BitVec.ofNat 64 1 := repneCmpsAfter_rdi 8 2 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 8).read (repneCmpsAfter 8 2 s) = (Operand.mem a : Operand 8).read s := by
      simp only [Operand.read, repneCmpsAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 1 + 1 * m = 1 * (m + 1) by omega]
    · refine ((AgreesExcept.repneCmps 8 2 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneCmpsbPre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  srcLow : (rsi.read s).toNat + 1 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 1 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 1 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 1 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = (rcx.read s).toNat

def repneCmpsbEffect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (1 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (1 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)))

@[simp] theorem repneCmpsbEffect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneCmpsbEffect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repneCmpsbEffect, Effect.components]

theorem repne_cmpsb_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, 0xA6]) s) (hpre : RepneCmpsbPre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, 0xA6]) t ∧ (repneCmpsbEffect p m s).Holds s t := by
  intro t
  have hloop : RepneCmpsbLoop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_cmpsb_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneCmpsbEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneCmpsbEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repne_cmpsb_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepneCmpsbPre p m) (codeRange p [0xF2, 0xA6]) (Effect.post (repneCmpsbEffect p m)) :=
  fun s h hcode hpre => ⟨_, repne_cmpsb_steps hcm p m s h hcode hpre⟩

structure RepneCmpsbSegLoop [Bindings] (r : SegReg) (base : BitVec 64) (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF2, 0xA6]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^64
  bound : m < count
  srcLow : (base + rsi.read s).toNat + 1 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 1 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 1 * (m + 1), (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 1 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = count
  seg : r.Ready base s

theorem RepneCmpsbSegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat}
    (h : RepneCmpsbSegLoop r base s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepneCmpsbSegLoop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat} (h : RepneCmpsbSegLoop r base s count m) :
    X86.Machine.step s = some (.next (repneCmpsSegAfter base 8 3 s)) := by
  have := h.srcLow
  have := h.dstLow
  have hsrc : MemReadable s (base + rsi.read s) 1 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF2]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF2] (noSegPrefix_cons noSegPrefix_f2 noSegPrefix_nil)]
  have hstep := repne_cmpsb_seg_step hcm s h.ready [r.prefixByte, 0xF2] (scanPrefix_seg_cons r (by simpa using scanPrefix_f2)) (by simp)
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

theorem RepneCmpsbSegLoop.cont_true [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat}
    (h : RepneCmpsbSegLoop r base s count (m + 1)) : repneCmpsSegCont base 8 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneCmpsSegCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneCmpsbSegLoop.cont_false [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepneCmpsbSegLoop r base s count 0) : repneCmpsSegCont base 8 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repneCmpsSegCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneCmpsbSegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count m : Nat}
    (h : RepneCmpsbSegLoop r base s (count + 1) (m + 1)) : RepneCmpsbSegLoop r base (repneCmpsSegAfter base 8 3 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneCmpsSegAfter base 8 3 s).RIP = s.RIP := by
    rw [repneCmpsSegAfter_rip base _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneCmpsSegAfter base 8 3 s).RFLAGS = s.RFLAGS := by
    rw [repneCmpsSegAfter_rflags, hc]
    rfl
  have hs : base + rsi.read (repneCmpsSegAfter base 8 3 s) = base + rsi.read s + BitVec.ofNat 64 1 := by
    rw [repneCmpsSegAfter_rsi base 8 3 s, BitVec.add_assoc]
  have hd : rdi.read (repneCmpsSegAfter base 8 3 s) = rdi.read s + BitVec.ofNat 64 1 := repneCmpsSegAfter_rdi base 8 3 s
  have hsn : (base + rsi.read (repneCmpsSegAfter base 8 3 s)).toNat = (base + rsi.read s).toNat + 1 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repneCmpsSegAfter base 8 3 s)).toNat = (rdi.read s).toNat + 1 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 8).read (repneCmpsSegAfter base 8 3 s) = (Operand.mem a : Operand 8).read s := by
    simp only [Operand.read, repneCmpsSegAfter_external]
  refine ⟨h.ready.repneCmpsSeg base 8 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    repneCmpsSegAfter_segReady base 8 3 s h.seg⟩
  · intro i hi
    rw [hrip, repneCmpsSegAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneCmpsSegAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repneCmpsSegAfter_external]
    exact h.srcMem (1 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repneCmpsSegAfter_external]
    exact h.dstMem (1 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 1 + 1 * i = 1 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 1 + 1 * m = 1 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneCmpsbSegDone [Bindings] (base : BitVec 64) (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (1 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (1 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_cmpsb_seg_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {r : SegReg} {base : BitVec 64} (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneCmpsbSegLoop r base s count m →
      RepneCmpsbSegDone base s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneCmpsSegAfter base 8 3 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneCmpsSegAfter base 8 3 s).Repeat_String_Operation = false := by
      rw [repneCmpsSegAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneCmpsSeg base 8 3).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneCmpsSegAfter_rip base _ _ s h.ready.msr, hc]; rfl
    · rw [repneCmpsSegAfter_rsi]
    · rw [repneCmpsSegAfter_rdi]
    · rw [repneCmpsSegAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneCmpsSegAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneCmpsSeg base 8 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneCmpsSegAfter base 8 3 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repneCmpsSegAfter base 8 3 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repneCmpsSegAfter base 8 3 s).RIP = s.RIP := by
      rw [repneCmpsSegAfter_rip base _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneCmpsSegAfter base 8 3 s).RFLAGS = s.RFLAGS := by
      rw [repneCmpsSegAfter_rflags, hc]
      rfl
    have hsreg : rsi.read (repneCmpsSegAfter base 8 3 s) = rsi.read s + BitVec.ofNat 64 1 :=
      repneCmpsSegAfter_rsi base 8 3 s
    have hs : base + rsi.read (repneCmpsSegAfter base 8 3 s) = base + rsi.read s + BitVec.ofNat 64 1 := by
      rw [hsreg, BitVec.add_assoc]
    have hd : rdi.read (repneCmpsSegAfter base 8 3 s) = rdi.read s + BitVec.ofNat 64 1 := repneCmpsSegAfter_rdi base 8 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 8).read (repneCmpsSegAfter base 8 3 s) = (Operand.mem a : Operand 8).read s := by
      simp only [Operand.read, repneCmpsSegAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hsreg, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 1 + 1 * m = 1 * (m + 1) by omega]
    · refine ((AgreesExcept.repneCmpsSeg base 8 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneCmpsbSegPre (p : BitVec 64) (r : SegReg) (base : BitVec 64) (m : Nat)
    (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  srcLow : (base + rsi.read s).toNat + 1 * (m + 1) ≤ 2^32
  dstLow : (rdi.read s).toNat + 1 * (m + 1) ≤ 2^32
  srcMem : ∀ i < 1 * (m + 1), (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 1 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = (rcx.read s).toNat
  seg : r.Ready base s

def repneCmpsbSegEffect (p base : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (1 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (1 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)))

@[simp] theorem repneCmpsbSegEffect_components (p base : BitVec 64) (m : Nat) (s : RamState) :
    (repneCmpsbSegEffect p base m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repneCmpsbSegEffect, Effect.components]

theorem repne_cmpsb_seg_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF2, 0xA6]) s) (hpre : RepneCmpsbSegPre p r base m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF2, 0xA6]) t ∧ (repneCmpsbSegEffect p base m s).Holds s t := by
  intro t
  have hloop : RepneCmpsbSegLoop r base s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], (rcx.read s).isLt, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.differ, hpre.stop, hpre.seg⟩
  have hd := repne_cmpsb_seg_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneCmpsbSegEffect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneCmpsbSegEffect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repne_cmpsb_seg_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (m : Nat) :
    Triple (RepneCmpsbSegPre p r base m) (codeRange p [r.prefixByte, 0xF2, 0xA6]) (Effect.post (repneCmpsbSegEffect p base m)) :=
  fun s h hcode hpre => ⟨_, repne_cmpsb_seg_steps hcm p r base m s h hcode hpre⟩

theorem repne_cmpsb_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0xF2, 0xA6]) (Effect.post (repZeroEffect p 2)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0xF2, 0xA6] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repne_cmpsb_step_zero s h.midRep [0xF2] (by simpa using scanPrefix_f2) (by simp)
      rfl
      rfl
      rfl
      rfl
      rfl
      hcodeS hlow hpre.rcxZero

theorem repne_cmpsb_seg_zero_triple [Bindings] (p : BitVec 64) (r : SegReg)
    :
    Triple (RepZeroPre p) (codeRange p [r.prefixByte, 0xF2, 0xA6]) (Effect.post (repZeroEffect p 3)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF2, 0xA6] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2] =
        withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF2]) (r.select (PrefixSegments.ofState s)) := by
      rw [scanContext_seg_cons _ _ r [0xF2] (noSegPrefix_cons noSegPrefix_f2 noSegPrefix_nil)]
    exact repne_cmpsb_step_zero s h.midRep [r.prefixByte, 0xF2] (scanPrefix_seg_cons r (by simpa using scanPrefix_f2)) (by simp)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      (by rw [hsc]; rfl)
      hcodeS hlow hpre.rcxZero

structure RepneCmpsqA32Loop [Bindings] (rex : UInt8) (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF2, rex, 0xA7]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^32
  bound : m < count
  srcLow : (rsi.read s).toNat + 8 * (m + 1) < 2^32
  dstLow : (rdi.read s).toNat + 8 * (m + 1) < 2^32
  srcMem : ∀ i < 8 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = count

theorem RepneCmpsqA32Loop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepneCmpsqA32Loop rex s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepneCmpsqA32Loop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState} {count m : Nat} (h : RepneCmpsqA32Loop rex s count m) :
    X86.Machine.step s = some (.next (repneCmpsAfter 64 4 s)) := by
  have hr := hrex.rexPrefix
  have := h.srcLow
  have := h.dstLow
  exact repne_cmpsq_a32_step hcm s h.ready [0x67, 0xF2, rex] (scanPrefix_asz_cons (by simp [scanPrefix_f2, hr.scanPrefix])) (by simp)
    (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; rfl)
    h.df h.code h.codeLow h.rcx_ne
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩ ⟨by omega, fun i hi => h.dstMem i (by omega)⟩
    (by omega) (by omega)
    (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.countLt; omega)]; exact h.countLt)

theorem RepneCmpsqA32Loop.cont_true [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepneCmpsqA32Loop rex s count (m + 1)) : repneCmpsCont 64 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneCmpsCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneCmpsqA32Loop.cont_false [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepneCmpsqA32Loop rex s count 0) : repneCmpsCont 64 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repneCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneCmpsqA32Loop.next [Bindings] {rex : UInt8} {s : RamState} {count m : Nat}
    (h : RepneCmpsqA32Loop rex s (count + 1) (m + 1)) : RepneCmpsqA32Loop rex (repneCmpsAfter 64 4 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneCmpsAfter 64 4 s).RIP = s.RIP := by
    rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneCmpsAfter 64 4 s).RFLAGS = s.RFLAGS := by
    rw [repneCmpsAfter_rflags, hc]
    rfl
  have hs : rsi.read (repneCmpsAfter 64 4 s) = rsi.read s + BitVec.ofNat 64 8 := repneCmpsAfter_rsi 64 4 s
  have hd : rdi.read (repneCmpsAfter 64 4 s) = rdi.read s + BitVec.ofNat 64 8 := repneCmpsAfter_rdi 64 4 s
  have hsn : (rsi.read (repneCmpsAfter 64 4 s)).toNat = (rsi.read s).toNat + 8 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repneCmpsAfter 64 4 s)).toNat = (rdi.read s).toNat + 8 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 64).read (repneCmpsAfter 64 4 s) = (Operand.mem a : Operand 64).read s := by
    simp only [Operand.read, repneCmpsAfter_external]
  refine ⟨h.ready.repneCmps 64 4, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneCmpsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneCmpsAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repneCmpsAfter_external]
    exact h.srcMem (8 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repneCmpsAfter_external]
    exact h.dstMem (8 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 8 + 8 * i = 8 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 8 + 8 * m = 8 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneCmpsqA32Done [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 4)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (8 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (8 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_cmpsq_a32_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneCmpsqA32Loop rex s count m →
      RepneCmpsqA32Done s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneCmpsAfter 64 4 s) := nextState_of_step (h.step hcm hrex )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneCmpsAfter 64 4 s).Repeat_String_Operation = false := by
      rw [repneCmpsAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneCmps 64 4).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneCmpsAfter_rsi]
    · rw [repneCmpsAfter_rdi]
    · rw [repneCmpsAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneCmpsAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneCmps 64 4 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneCmpsAfter 64 4 s) := nextState_of_step (h.step hcm hrex )
    have hc := h.cont_true
    have ih' := ih c (repneCmpsAfter 64 4 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repneCmpsAfter 64 4 s).RIP = s.RIP := by
      rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneCmpsAfter 64 4 s).RFLAGS = s.RFLAGS := by
      rw [repneCmpsAfter_rflags, hc]
      rfl
    have hs : rsi.read (repneCmpsAfter 64 4 s) = rsi.read s + BitVec.ofNat 64 8 := repneCmpsAfter_rsi 64 4 s
    have hd : rdi.read (repneCmpsAfter 64 4 s) = rdi.read s + BitVec.ofNat 64 8 := repneCmpsAfter_rdi 64 4 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 64).read (repneCmpsAfter 64 4 s) = (Operand.mem a : Operand 64).read s := by
      simp only [Operand.read, repneCmpsAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 8 + 8 * m = 8 * (m + 1) by omega]
    · refine ((AgreesExcept.repneCmps 64 4 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneCmpsqA32Pre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  rcxLow : (rcx.read s).toNat < 2^32
  srcLow : (rsi.read s).toNat + 8 * (m + 1) < 2^32
  dstLow : (rdi.read s).toNat + 8 * (m + 1) < 2^32
  srcMem : ∀ i < 8 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * i)) : Operand 64).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s) ∨ m + 1 = (rcx.read s).toNat

def repneCmpsqA32Effect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 4
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (8 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (8 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (8 * m)) : Operand 64).read s)))

@[simp] theorem repneCmpsqA32Effect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneCmpsqA32Effect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repneCmpsqA32Effect, Effect.components]

theorem repne_cmpsq_a32_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF2, rex, 0xA7]) s) (hpre : RepneCmpsqA32Pre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF2, rex, 0xA7]) t ∧ (repneCmpsqA32Effect p m s).Holds s t := by
  intro t
  have hloop : RepneCmpsqA32Loop rex s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hpre.rcxLow, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_cmpsq_a32_loop hcm hrex m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneCmpsqA32Effect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneCmpsqA32Effect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repne_cmpsq_a32_triple_of_bytes [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (m : Nat) :
    Triple (RepneCmpsqA32Pre p m) (codeRange p [0x67, 0xF2, rex, 0xA7]) (Effect.post (repneCmpsqA32Effect p m)) :=
  fun s h hcode hpre => ⟨_, repne_cmpsq_a32_steps hcm p rex hrex m s h hcode hpre⟩

theorem repne_cmpsq_a32_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepneCmpsqA32Pre p m) (codeRange p [0x67, 0xF2, 0x48, 0xA7]) (Effect.post (repneCmpsqA32Effect p m)) :=
  repne_cmpsq_a32_triple_of_bytes hcm p 0x48 (by unfold RexWPrefix; decide) m

theorem repne_cmpsq_a32_zero_triple_of_bytes [Bindings] (p : BitVec 64)
    (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepZeroPre p) (codeRange p [0x67, 0xF2, rex, 0xA7]) (Effect.post (repZeroEffect p 4)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hr := hrex.rexPrefix
    have hcodeS : BytesAt s s.RIP [0x67, 0xF2, rex, 0xA7] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repne_cmpsq_a32_step_zero s h.midRep [0x67, 0xF2, rex] (scanPrefix_asz_cons (by simp [scanPrefix_f2, hr.scanPrefix])) (by simp)
      (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; rfl)
      (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; exact hrex.rex_w s.DS)
      (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; rfl)
      (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; rfl)
      (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; rfl)
      (by rw [scanContext_asz_cons, scanContext_f2_rex _ _ hr]; rfl)
      hcodeS hlow hpre.rcxZero

theorem repne_cmpsq_a32_zero_triple [Bindings] (p : BitVec 64) :
    Triple (RepZeroPre p) (codeRange p [0x67, 0xF2, 0x48, 0xA7]) (Effect.post (repZeroEffect p 4)) :=
  repne_cmpsq_a32_zero_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide)

structure RepneCmpsdA32Loop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF2, 0xA7]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^32
  bound : m < count
  srcLow : (rsi.read s).toNat + 4 * (m + 1) < 2^32
  dstLow : (rdi.read s).toNat + 4 * (m + 1) < 2^32
  srcMem : ∀ i < 4 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = count

theorem RepneCmpsdA32Loop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpsdA32Loop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepneCmpsdA32Loop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {s : RamState} {count m : Nat} (h : RepneCmpsdA32Loop s count m) :
    X86.Machine.step s = some (.next (repneCmpsAfter 32 3 s)) := by
  have := h.srcLow
  have := h.dstLow
  exact repne_cmpsd_a32_step hcm s h.ready [0x67, 0xF2] (scanPrefix_asz_cons (by simpa using scanPrefix_f2)) (by simp)
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

theorem RepneCmpsdA32Loop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpsdA32Loop s count (m + 1)) : repneCmpsCont 32 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneCmpsCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneCmpsdA32Loop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepneCmpsdA32Loop s count 0) : repneCmpsCont 32 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repneCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneCmpsdA32Loop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpsdA32Loop s (count + 1) (m + 1)) : RepneCmpsdA32Loop (repneCmpsAfter 32 3 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneCmpsAfter 32 3 s).RIP = s.RIP := by
    rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneCmpsAfter 32 3 s).RFLAGS = s.RFLAGS := by
    rw [repneCmpsAfter_rflags, hc]
    rfl
  have hs : rsi.read (repneCmpsAfter 32 3 s) = rsi.read s + BitVec.ofNat 64 4 := repneCmpsAfter_rsi 32 3 s
  have hd : rdi.read (repneCmpsAfter 32 3 s) = rdi.read s + BitVec.ofNat 64 4 := repneCmpsAfter_rdi 32 3 s
  have hsn : (rsi.read (repneCmpsAfter 32 3 s)).toNat = (rsi.read s).toNat + 4 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repneCmpsAfter 32 3 s)).toNat = (rdi.read s).toNat + 4 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 32).read (repneCmpsAfter 32 3 s) = (Operand.mem a : Operand 32).read s := by
    simp only [Operand.read, repneCmpsAfter_external]
  refine ⟨h.ready.repneCmps 32 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneCmpsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneCmpsAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repneCmpsAfter_external]
    exact h.srcMem (4 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repneCmpsAfter_external]
    exact h.dstMem (4 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 4 + 4 * i = 4 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 4 + 4 * m = 4 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneCmpsdA32Done [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (4 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (4 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_cmpsd_a32_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneCmpsdA32Loop s count m →
      RepneCmpsdA32Done s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneCmpsAfter 32 3 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneCmpsAfter 32 3 s).Repeat_String_Operation = false := by
      rw [repneCmpsAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneCmps 32 3).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneCmpsAfter_rsi]
    · rw [repneCmpsAfter_rdi]
    · rw [repneCmpsAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneCmpsAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneCmps 32 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneCmpsAfter 32 3 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repneCmpsAfter 32 3 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repneCmpsAfter 32 3 s).RIP = s.RIP := by
      rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneCmpsAfter 32 3 s).RFLAGS = s.RFLAGS := by
      rw [repneCmpsAfter_rflags, hc]
      rfl
    have hs : rsi.read (repneCmpsAfter 32 3 s) = rsi.read s + BitVec.ofNat 64 4 := repneCmpsAfter_rsi 32 3 s
    have hd : rdi.read (repneCmpsAfter 32 3 s) = rdi.read s + BitVec.ofNat 64 4 := repneCmpsAfter_rdi 32 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 32).read (repneCmpsAfter 32 3 s) = (Operand.mem a : Operand 32).read s := by
      simp only [Operand.read, repneCmpsAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 4 + 4 * m = 4 * (m + 1) by omega]
    · refine ((AgreesExcept.repneCmps 32 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneCmpsdA32Pre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  rcxLow : (rcx.read s).toNat < 2^32
  srcLow : (rsi.read s).toNat + 4 * (m + 1) < 2^32
  dstLow : (rdi.read s).toNat + 4 * (m + 1) < 2^32
  srcMem : ∀ i < 4 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * i)) : Operand 32).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s) ∨ m + 1 = (rcx.read s).toNat

def repneCmpsdA32Effect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (4 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (4 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (4 * m)) : Operand 32).read s)))

@[simp] theorem repneCmpsdA32Effect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneCmpsdA32Effect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repneCmpsdA32Effect, Effect.components]

theorem repne_cmpsd_a32_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF2, 0xA7]) s) (hpre : RepneCmpsdA32Pre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF2, 0xA7]) t ∧ (repneCmpsdA32Effect p m s).Holds s t := by
  intro t
  have hloop : RepneCmpsdA32Loop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hpre.rcxLow, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_cmpsd_a32_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneCmpsdA32Effect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneCmpsdA32Effect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repne_cmpsd_a32_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepneCmpsdA32Pre p m) (codeRange p [0x67, 0xF2, 0xA7]) (Effect.post (repneCmpsdA32Effect p m)) :=
  fun s h hcode hpre => ⟨_, repne_cmpsd_a32_steps hcm p m s h hcode hpre⟩

theorem repne_cmpsd_a32_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0x67, 0xF2, 0xA7]) (Effect.post (repZeroEffect p 3)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0x67, 0xF2, 0xA7] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repne_cmpsd_a32_step_zero s h.midRep [0x67, 0xF2] (scanPrefix_asz_cons (by simpa using scanPrefix_f2)) (by simp)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      hcodeS hlow hpre.rcxZero

structure RepneCmpswA32Loop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF2, 0x66, 0xA7]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^32
  bound : m < count
  srcLow : (rsi.read s).toNat + 2 * (m + 1) < 2^32
  dstLow : (rdi.read s).toNat + 2 * (m + 1) < 2^32
  srcMem : ∀ i < 2 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 2 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = count

theorem RepneCmpswA32Loop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpswA32Loop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepneCmpswA32Loop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {s : RamState} {count m : Nat} (h : RepneCmpswA32Loop s count m) :
    X86.Machine.step s = some (.next (repneCmpsAfter 16 4 s)) := by
  have := h.srcLow
  have := h.dstLow
  exact repne_cmpsw_a32_step hcm s h.ready [0x67, 0xF2, 0x66] (scanPrefix_asz_cons (by simp [scanPrefix_f2, scanPrefix_66])) (by simp)
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

theorem RepneCmpswA32Loop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpswA32Loop s count (m + 1)) : repneCmpsCont 16 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneCmpsCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneCmpswA32Loop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepneCmpswA32Loop s count 0) : repneCmpsCont 16 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repneCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneCmpswA32Loop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpswA32Loop s (count + 1) (m + 1)) : RepneCmpswA32Loop (repneCmpsAfter 16 4 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneCmpsAfter 16 4 s).RIP = s.RIP := by
    rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneCmpsAfter 16 4 s).RFLAGS = s.RFLAGS := by
    rw [repneCmpsAfter_rflags, hc]
    rfl
  have hs : rsi.read (repneCmpsAfter 16 4 s) = rsi.read s + BitVec.ofNat 64 2 := repneCmpsAfter_rsi 16 4 s
  have hd : rdi.read (repneCmpsAfter 16 4 s) = rdi.read s + BitVec.ofNat 64 2 := repneCmpsAfter_rdi 16 4 s
  have hsn : (rsi.read (repneCmpsAfter 16 4 s)).toNat = (rsi.read s).toNat + 2 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repneCmpsAfter 16 4 s)).toNat = (rdi.read s).toNat + 2 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 16).read (repneCmpsAfter 16 4 s) = (Operand.mem a : Operand 16).read s := by
    simp only [Operand.read, repneCmpsAfter_external]
  refine ⟨h.ready.repneCmps 16 4, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneCmpsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneCmpsAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repneCmpsAfter_external]
    exact h.srcMem (2 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repneCmpsAfter_external]
    exact h.dstMem (2 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 2 + 2 * i = 2 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 2 + 2 * m = 2 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneCmpswA32Done [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 4)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (2 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (2 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_cmpsw_a32_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneCmpswA32Loop s count m →
      RepneCmpswA32Done s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneCmpsAfter 16 4 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneCmpsAfter 16 4 s).Repeat_String_Operation = false := by
      rw [repneCmpsAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneCmps 16 4).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneCmpsAfter_rsi]
    · rw [repneCmpsAfter_rdi]
    · rw [repneCmpsAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneCmpsAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneCmps 16 4 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneCmpsAfter 16 4 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repneCmpsAfter 16 4 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repneCmpsAfter 16 4 s).RIP = s.RIP := by
      rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneCmpsAfter 16 4 s).RFLAGS = s.RFLAGS := by
      rw [repneCmpsAfter_rflags, hc]
      rfl
    have hs : rsi.read (repneCmpsAfter 16 4 s) = rsi.read s + BitVec.ofNat 64 2 := repneCmpsAfter_rsi 16 4 s
    have hd : rdi.read (repneCmpsAfter 16 4 s) = rdi.read s + BitVec.ofNat 64 2 := repneCmpsAfter_rdi 16 4 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 16).read (repneCmpsAfter 16 4 s) = (Operand.mem a : Operand 16).read s := by
      simp only [Operand.read, repneCmpsAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 2 + 2 * m = 2 * (m + 1) by omega]
    · refine ((AgreesExcept.repneCmps 16 4 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneCmpswA32Pre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  rcxLow : (rcx.read s).toNat < 2^32
  srcLow : (rsi.read s).toNat + 2 * (m + 1) < 2^32
  dstLow : (rdi.read s).toNat + 2 * (m + 1) < 2^32
  srcMem : ∀ i < 2 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 2 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * i)) : Operand 16).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s) ∨ m + 1 = (rcx.read s).toNat

def repneCmpswA32Effect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 4
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (2 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (2 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (2 * m)) : Operand 16).read s)))

@[simp] theorem repneCmpswA32Effect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneCmpswA32Effect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repneCmpswA32Effect, Effect.components]

theorem repne_cmpsw_a32_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF2, 0x66, 0xA7]) s) (hpre : RepneCmpswA32Pre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF2, 0x66, 0xA7]) t ∧ (repneCmpswA32Effect p m s).Holds s t := by
  intro t
  have hloop : RepneCmpswA32Loop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hpre.rcxLow, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_cmpsw_a32_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneCmpswA32Effect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneCmpswA32Effect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repne_cmpsw_a32_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepneCmpswA32Pre p m) (codeRange p [0x67, 0xF2, 0x66, 0xA7]) (Effect.post (repneCmpswA32Effect p m)) :=
  fun s h hcode hpre => ⟨_, repne_cmpsw_a32_steps hcm p m s h hcode hpre⟩

theorem repne_cmpsw_a32_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0x67, 0xF2, 0x66, 0xA7]) (Effect.post (repZeroEffect p 4)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0x67, 0xF2, 0x66, 0xA7] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repne_cmpsw_a32_step_zero s h.midRep [0x67, 0xF2, 0x66] (scanPrefix_asz_cons (by simp [scanPrefix_f2, scanPrefix_66])) (by simp)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      hcodeS hlow hpre.rcxZero

structure RepneCmpsbA32Loop [Bindings] (s : RamState) (count m : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF2, 0xA6]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  countLt : count < 2^32
  bound : m < count
  srcLow : (rsi.read s).toNat + 1 * (m + 1) < 2^32
  dstLow : (rdi.read s).toNat + 1 * (m + 1) < 2^32
  srcMem : ∀ i < 1 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 1 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = count

theorem RepneCmpsbA32Loop.rcx_ne [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpsbA32Loop s count m) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero (by have := h.bound; omega) (by have := h.countLt; omega)

theorem RepneCmpsbA32Loop.step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    {s : RamState} {count m : Nat} (h : RepneCmpsbA32Loop s count m) :
    X86.Machine.step s = some (.next (repneCmpsAfter 8 3 s)) := by
  have := h.srcLow
  have := h.dstLow
  exact repne_cmpsb_a32_step hcm s h.ready [0x67, 0xF2] (scanPrefix_asz_cons (by simpa using scanPrefix_f2)) (by simp)
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

theorem RepneCmpsbA32Loop.cont_true [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpsbA32Loop s count (m + 1)) : repneCmpsCont 8 s = true := by
  have he := h.differ 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at he
  have hb := h.bound
  have hc : rcx.read s - 1 ≠ 0 := by
    rw [h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
    exact ofNat_ne_zero (by omega) (by have := h.countLt; omega)
  have hc' : (rcx.read s - 1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc
  unfold repneCmpsCont
  rw [cmpSpec_ZF, beq_eq_false_iff_ne.mpr he, hc']
  rfl

theorem RepneCmpsbA32Loop.cont_false [Bindings] {s : RamState} {count : Nat}
    (h : RepneCmpsbA32Loop s count 0) : repneCmpsCont 8 s = false := by
  have hs := h.stop
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at hs
  unfold repneCmpsCont
  rcases hs with hne | rfl
  · rw [cmpSpec_ZF, hne, beq_self_eq_true, Bool.not_true, Bool.and_false]
  · simp [h.counter]

theorem RepneCmpsbA32Loop.next [Bindings] {s : RamState} {count m : Nat}
    (h : RepneCmpsbA32Loop s (count + 1) (m + 1)) : RepneCmpsbA32Loop (repneCmpsAfter 8 3 s) count m := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hb := h.bound
  have hc := h.cont_true
  have hrip : (repneCmpsAfter 8 3 s).RIP = s.RIP := by
    rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]
    rfl
  have hfl : (repneCmpsAfter 8 3 s).RFLAGS = s.RFLAGS := by
    rw [repneCmpsAfter_rflags, hc]
    rfl
  have hs : rsi.read (repneCmpsAfter 8 3 s) = rsi.read s + BitVec.ofNat 64 1 := repneCmpsAfter_rsi 8 3 s
  have hd : rdi.read (repneCmpsAfter 8 3 s) = rdi.read s + BitVec.ofNat 64 1 := repneCmpsAfter_rdi 8 3 s
  have hsn : (rsi.read (repneCmpsAfter 8 3 s)).toNat = (rsi.read s).toNat + 1 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repneCmpsAfter 8 3 s)).toNat = (rdi.read s).toNat + 1 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 8).read (repneCmpsAfter 8 3 s) = (Operand.mem a : Operand 8).read s := by
    simp only [Operand.read, repneCmpsAfter_external]
  refine ⟨h.ready.repneCmps 8 3, hfl ▸ h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repneCmpsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [repneCmpsAfter_rcx, h.counter, ofNat_succ_sub_one]
  · have := h.countLt; omega
  · omega
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repneCmpsAfter_external]
    exact h.srcMem (1 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repneCmpsAfter_external]
    exact h.dstMem (1 + i) (by omega)
  · intro i hi
    rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 1 + 1 * i = 1 * (i + 1) by omega]
    exact h.differ (i + 1) (by omega)
  · rw [hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
      show 1 + 1 * m = 1 * (m + 1) by omega]
    rcases h.stop with hne | heq
    · exact .inl hne
    · exact .inr (by omega)

structure RepneCmpsbA32Done [Bindings] (s t : RamState) (count m : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (1 * (m + 1))
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (1 * (m + 1))
  rcxAfter : rcx.read t = BitVec.ofNat 64 (count - (m + 1))
  rflags : t.RFLAGS = (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)).store s.RFLAGS
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s) t

theorem repne_cmpsb_a32_loop [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (m : Nat) :
    ∀ (count : Nat) (s : RamState), RepneCmpsbA32Loop s count m →
      RepneCmpsbA32Done s (nextStates (m + 1) s) count m := by
  induction m with
  | zero =>
    intro count s h
    have hnext : nextState s = (repneCmpsAfter 8 3 s) := nextState_of_step (h.step hcm )
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc := h.cont_false
    have hflag : (repneCmpsAfter 8 3 s).Repeat_String_Operation = false := by
      rw [repneCmpsAfter_repeat, hc]
    have hb := h.bound
    refine ⟨(h.ready.repneCmps 8 3).ready hflag, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]; rfl
    · rw [repneCmpsAfter_rsi]
    · rw [repneCmpsAfter_rdi]
    · rw [repneCmpsAfter_rcx, h.counter, show count = (count - 1) + 1 by omega, ofNat_succ_sub_one]
      congr 1 <;> omega
    · rw [repneCmpsAfter_rflags, hc]
      simp only [Nat.mul_zero, BitVec.add_zero, Bool.false_eq_true, ↓reduceIte]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repneCmps 8 3 s
  | succ m ih =>
    intro count s h
    obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by have := h.bound; omega⟩
    have hnext : nextState s = (repneCmpsAfter 8 3 s) := nextState_of_step (h.step hcm )
    have hc := h.cont_true
    have ih' := ih c (repneCmpsAfter 8 3 s) h.next
    rw [nextStates_succ, hnext]
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hrip : (repneCmpsAfter 8 3 s).RIP = s.RIP := by
      rw [repneCmpsAfter_rip _ _ s h.ready.msr, hc]
      rfl
    have hfl : (repneCmpsAfter 8 3 s).RFLAGS = s.RFLAGS := by
      rw [repneCmpsAfter_rflags, hc]
      rfl
    have hs : rsi.read (repneCmpsAfter 8 3 s) = rsi.read s + BitVec.ofNat 64 1 := repneCmpsAfter_rsi 8 3 s
    have hd : rdi.read (repneCmpsAfter 8 3 s) = rdi.read s + BitVec.ofNat 64 1 := repneCmpsAfter_rdi 8 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 8).read (repneCmpsAfter 8 3 s) = (Operand.mem a : Operand 8).read s := by
      simp only [Operand.read, repneCmpsAfter_external]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rcxAfter]; congr 1 <;> omega
    · rw [ih'.rflags, hfl, hs, hd, add_ofNat_add_ofNat, add_ofNat_add_ofNat, hm, hm,
        show 1 + 1 * m = 1 * (m + 1) by omega]
    · refine ((AgreesExcept.repneCmps 8 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepneCmpsbA32Pre (p : BitVec 64) (m : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  bound : m < (rcx.read s).toNat
  rcxLow : (rcx.read s).toNat < 2^32
  srcLow : (rsi.read s).toNat + 1 * (m + 1) < 2^32
  dstLow : (rdi.read s).toNat + 1 * (m + 1) < 2^32
  srcMem : ∀ i < 1 * (m + 1), (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 1 * (m + 1), (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  differ : ∀ i < m, ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s) ≠
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * i)) : Operand 8).read s)
  stop : ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) =
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s) ∨ m + 1 = (rcx.read s).toNat

def repneCmpsbA32Effect (p : BitVec 64) (m : Nat) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (1 * (m + 1))⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (1 * (m + 1))⟩,
    ⟨rcx, BitVec.ofNat 64 ((rcx.read s).toNat - (m + 1))⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)
    ((Operand.mem (rdi.read s + BitVec.ofNat 64 (1 * m)) : Operand 8).read s)))

@[simp] theorem repneCmpsbA32Effect_components (p : BitVec 64) (m : Nat) (s : RamState) :
    (repneCmpsbA32Effect p m s).components = [.reg 6, .reg 7, .reg 1, .flags, .rip] := by
  simp [repneCmpsbA32Effect, Effect.components]

theorem repne_cmpsb_a32_steps [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF2, 0xA6]) s) (hpre : RepneCmpsbA32Pre p m s) :
    let t := nextStates (m + 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF2, 0xA6]) t ∧ (repneCmpsbA32Effect p m s).Holds s t := by
  intro t
  have hloop : RepneCmpsbA32Loop s (rcx.read s).toNat m :=
    ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, hpre.rip ▸ hcode.low (by simp) (by simp),
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hpre.rcxLow, hpre.bound, hpre.srcLow,
      hpre.dstLow, hpre.srcMem, hpre.dstMem, hpre.differ, hpre.stop⟩
  have hd := repne_cmpsb_a32_loop hcm m _ s hloop
  have hag := hd.agrees
  rw [clearRep_eq h.ready.repeatClear] at hag
  refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ?_, ?_, ?_⟩
  · rw [hd.rip, hpre.rip]; rfl
  · exact ⟨hd.rsiAfter, hd.rdiAfter, hd.rcxAfter⟩
  · simp only [Effect.FlagsHold, repneCmpsbA32Effect]
    rw [hd.rflags]
    exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _
  · rw [repneCmpsbA32Effect_components]
    refine hag.mono ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

theorem repne_cmpsb_a32_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (p : BitVec 64) (m : Nat) :
    Triple (RepneCmpsbA32Pre p m) (codeRange p [0x67, 0xF2, 0xA6]) (Effect.post (repneCmpsbA32Effect p m)) :=
  fun s h hcode hpre => ⟨_, repne_cmpsb_a32_steps hcm p m s h hcode hpre⟩

theorem repne_cmpsb_a32_zero_triple [Bindings] (p : BitVec 64)
    :
    Triple (RepZeroPre p) (codeRange p [0x67, 0xF2, 0xA6]) (Effect.post (repZeroEffect p 3)) :=
  Triple.of_repZero fun s h hcode hpre => by
    have hcodeS : BytesAt s s.RIP [0x67, 0xF2, 0xA6] := hpre.rip ▸ hcode.bytesAt
    have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
    exact repne_cmpsb_a32_step_zero s h.midRep [0x67, 0xF2] (scanPrefix_asz_cons (by simpa using scanPrefix_f2)) (by simp)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      (by rw [scanContext_asz_cons]; rfl)
      hcodeS hlow hpre.rcxZero

attribute [x86_compose] repneCmpsqEffect repneCmpsqSegEffect repneCmpsdEffect repneCmpsdSegEffect repneCmpswEffect repneCmpswSegEffect repneCmpsbEffect repneCmpsbSegEffect repneCmpsqA32Effect repneCmpsdA32Effect repneCmpswA32Effect repneCmpsbA32Effect

@[x86_local] theorem repneCmpsqEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneCmpsqEffect p m) := by
  effect_local [repneCmpsqEffect]

@[x86_local] theorem repneCmpsqSegEffect_local {p base : BitVec 64} {m : Nat} :
    Effect.Local (repneCmpsqSegEffect p base m) := by
  effect_local [repneCmpsqSegEffect]

@[x86_local] theorem repneCmpsdEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneCmpsdEffect p m) := by
  effect_local [repneCmpsdEffect]

@[x86_local] theorem repneCmpsdSegEffect_local {p base : BitVec 64} {m : Nat} :
    Effect.Local (repneCmpsdSegEffect p base m) := by
  effect_local [repneCmpsdSegEffect]

@[x86_local] theorem repneCmpswEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneCmpswEffect p m) := by
  effect_local [repneCmpswEffect]

@[x86_local] theorem repneCmpswSegEffect_local {p base : BitVec 64} {m : Nat} :
    Effect.Local (repneCmpswSegEffect p base m) := by
  effect_local [repneCmpswSegEffect]

@[x86_local] theorem repneCmpsbEffect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneCmpsbEffect p m) := by
  effect_local [repneCmpsbEffect]

@[x86_local] theorem repneCmpsbSegEffect_local {p base : BitVec 64} {m : Nat} :
    Effect.Local (repneCmpsbSegEffect p base m) := by
  effect_local [repneCmpsbSegEffect]

@[x86_local] theorem repneCmpsqA32Effect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneCmpsqA32Effect p m) := by
  effect_local [repneCmpsqA32Effect]

@[x86_local] theorem repneCmpsdA32Effect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneCmpsdA32Effect p m) := by
  effect_local [repneCmpsdA32Effect]

@[x86_local] theorem repneCmpswA32Effect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneCmpswA32Effect p m) := by
  effect_local [repneCmpswA32Effect]

@[x86_local] theorem repneCmpsbA32Effect_local {p : BitVec 64} {m : Nat} :
    Effect.Local (repneCmpsbA32Effect p m) := by
  effect_local [repneCmpsbA32Effect]

end X86Proofs
