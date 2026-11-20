
import X86Proofs.Instructions.Lods.Generated.Rep.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

structure RepLodsqLoop [Bindings] (rex : UInt8) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, rex, 0xAD]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 8 * count ≤ 2^32
  srcMem : ∀ i < 8 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome

theorem RepLodsqLoop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepLodsqLoop rex s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodsqLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState} {count : Nat} (h : RepLodsqLoop rex s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repLodsAfter 64 3 s)) := by
  have hr := hrex.rexPrefix
  have := h.srcLow
  exact rep_lodsq_step hstride s h.ready [0xF3, rex] (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    h.df h.code h.codeLow (h.rcx_ne hpos) ⟨by omega, fun i hi => h.srcMem i (by omega)⟩

theorem RepLodsqLoop.rcx_after [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepLodsqLoop rex s (count + 1)) : rcx.read (repLodsAfter 64 3 s) = BitVec.ofNat 64 count := by
  rw [repLodsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepLodsqLoop.next [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepLodsqLoop rex s (count + 2)) : RepLodsqLoop rex (repLodsAfter 64 3 s) (count + 1) := by
  have hsl := h.srcLow
  have hrip : (repLodsAfter 64 3 s).RIP = s.RIP := by
    rw [repLodsAfter_rip 64 3 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : rsi.read (repLodsAfter 64 3 s) = rsi.read s + BitVec.ofNat 64 8 :=
    repLodsAfter_rsi 64 3 s
  have hsn : (rsi.read (repLodsAfter 64 3 s)).toNat = (rsi.read s).toNat + 8 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repLods 64 3, h.df, ?_, ?_, h.rcx_after, ?_, ?_⟩
  · intro i hi
    rw [hrip, repLodsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repLodsAfter_external]
    exact h.srcMem (8 + i) (by omega)

structure RepLodsqDone [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (8 * count)
  raxAfter : (Operand.reg 0 : Operand 64).read t =
    mergeGPR 64
      ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * (count - 1))) : Operand 64).read s)
      ((Operand.reg 0 : Operand 64).read s)
  agrees : AgreesExcept [.reg 0, .reg 1, .reg 6, .rip] (clearRep s) t

theorem rep_lodsq_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (count : Nat) (s : RamState) (h : RepLodsqLoop rex s (count + 1)) :
    RepLodsqDone s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repLodsAfter 64 3 s) :=
      nextState_of_step (h.step hstride hrex (by omega))
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repLodsAfter 64 3 s).Repeat_String_Operation = false := by
      rw [repLodsAfter_repeat, hc]; rfl
    refine ⟨(h.ready.repLods 64 3).ready hflag, ?_, ?_, repLodsAfter_rsi 64 3 s, ?_, ?_⟩
    · rw [repLodsAfter_rip 64 3 s h.ready.msr, hc]; rfl
    · rw [repLodsAfter_rcx, hc]
    · rw [repLodsAfter_rax]
      simp only [Nat.zero_add, Nat.sub_self, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repLods 64 3 s
  | succ m ih =>
    have hnext : nextState s = (repLodsAfter 64 3 s) :=
      nextState_of_step (h.step hstride hrex (by omega))
    have hs : rsi.read (repLodsAfter 64 3 s) = rsi.read s + BitVec.ofNat 64 8 :=
      repLodsAfter_rsi 64 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 64).read (repLodsAfter 64 3 s) =
          (Operand.mem a : Operand 64).read s := by
      simp only [Operand.read, repLodsAfter_external]
    have ih' := ih (repLodsAfter 64 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repLodsAfter 64 3 s).RIP = s.RIP := by
      rw [repLodsAfter_rip 64 3 s h.ready.msr, h.counter]
      have := h.srcLow
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.raxAfter, repLodsAfter_rax, mergeGPR_mergeGPR 64 (by decide), hs, add_ofNat_add_ofNat,
        hm, show 8 + 8 * (m + 1 - 1) = 8 * (m + 1 + 1 - 1) by omega]
    · refine ((AgreesExcept.repLods 64 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepLodsqPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (rsi.read s).toNat + 8 * (rcx.read s).toNat ≤ 2^32
  srcMem : ∀ i < 8 * (rcx.read s).toNat, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome

def repLodsqEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (8 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.reg 0 : Operand 64), if rcx.read s = 0 then (Operand.reg 0 : Operand 64).read s else
      ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * ((rcx.read s).toNat - 1))) :
        Operand 64).read s)⟩]

@[simp] theorem repLodsqEffect_components (p : BitVec 64) (s : RamState) :
    (repLodsqEffect p s).components = [.reg 6, .reg 1, .reg 0, .rip] := by
  simp [repLodsqEffect, Effect.components]

theorem rep_lodsq_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, rex, 0xAD]) s) (hpre : RepLodsqPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, rex, 0xAD]) t ∧ (repLodsqEffect p s).Holds s t := by
  intro t
  have hr := hrex.rexPrefix
  have hcodeS : BytesAt s s.RIP [0xF3, rex, 0xAD] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_lodsq_step_zero s h.midRep [0xF3, rex]
        (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp)
        (by rw [scanContext_f3_rex _ _ hr]; rfl)
        (by rw [scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
        (by rw [scanContext_f3_rex _ _ hr]; rfl)
        (by rw [scanContext_f3_rex _ _ hr]; rfl)
        (by rw [scanContext_f3_rex _ _ hr]; rfl)
        hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repZeroAfter 3 s) :=
      (AgreesExcept.repZero 3 s).of_clearRep hrep (repZeroAfter_repeat 3 s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables,
      hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, ?_, ?_⟩, trivial,
      hag.mono (by simp)⟩
    · rw [repZeroAfter_rip _ s h.ready.msr, hpre.rip]; rfl
    · rw [hag.read (by simp), hn]; simp
    · rw [hag.read (by simp), hz]
    · show (Operand.reg 0 : Operand 64).read _ = _
      rw [hag.read (by simp)]; simp [hz]
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.srcLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hnz : rcx.read s ≠ 0 := fun h0 => by simp [h0] at hn
    have hready : RepLodsqLoop rex s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.srcMem⟩
    have hd := rep_lodsq_loop hstride hrex c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, hd.rcxZero, ?_⟩,
      trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · rw [hd.rsiAfter, hn]
    · show _ = if rcx.read s = 0 then _ else _
      simp only [hnz, ↓reduceIte]
      rw [hd.raxAfter, hn]
      exact mergeGPR_64 _ _
    · rw [repLodsqEffect_components]
      refine hag.mono ?_
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem rep_lodsq_triple_of_bytes [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepLodsqPre p) (codeRange p [0xF3, rex, 0xAD]) (Effect.post (repLodsqEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_lodsq_steps hstride p rex hrex s h hcode hpre⟩

theorem rep_lodsq_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) :
    Triple (RepLodsqPre p) (codeRange p [0xF3, 0x48, 0xAD]) (Effect.post (repLodsqEffect p)) :=
  rep_lodsq_triple_of_bytes hstride p 0x48 (by unfold RexWPrefix; decide)

structure RepLodsqSegLoop [Bindings] (r : SegReg) (base : BitVec 64) (rex : UInt8) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF3, rex, 0xAD]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (base + rsi.read s).toNat + 8 * count ≤ 2^32
  srcMem : ∀ i < 8 * count, (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  seg : r.Ready base s

theorem RepLodsqSegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepLodsqSegLoop r base rex s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodsqSegLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {r : SegReg} {base : BitVec 64} {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState} {count : Nat} (h : RepLodsqSegLoop r base rex s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repLodsSegAfter base 64 4 s)) := by
  have hr := hrex.rexPrefix
  have := h.srcLow
  have hsrc : MemReadable s (base + rsi.read s) 8 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3, rex] =
      withSeg (repRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3, rex] (noSegPrefix_cons noSegPrefix_f3 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_f3_rex _ _ hr]
  have hstep := rep_lodsq_seg_step hstride s h.ready [r.prefixByte, 0xF3, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hrex.rex_w s.DS)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    h.df h.code h.codeLow (h.rcx_ne hpos) (by rw [hsc]; exact hsrc)
  rw [hsc] at hstep
  exact hstep

theorem RepLodsqSegLoop.rcx_after [Bindings] {r : SegReg} {base : BitVec 64} {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepLodsqSegLoop r base rex s (count + 1)) : rcx.read (repLodsSegAfter base 64 4 s) = BitVec.ofNat 64 count := by
  rw [repLodsSegAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepLodsqSegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepLodsqSegLoop r base rex s (count + 2)) : RepLodsqSegLoop r base rex (repLodsSegAfter base 64 4 s) (count + 1) := by
  have hsl := h.srcLow
  have hrip : (repLodsSegAfter base 64 4 s).RIP = s.RIP := by
    rw [repLodsSegAfter_rip base 64 4 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : base + rsi.read (repLodsSegAfter base 64 4 s) = base + rsi.read s + BitVec.ofNat 64 8 := by
    rw [repLodsSegAfter_rsi base 64 4 s, BitVec.add_assoc]
  have hsn : (base + rsi.read (repLodsSegAfter base 64 4 s)).toNat = (base + rsi.read s).toNat + 8 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repLodsSeg base 64 4, h.df, ?_, ?_, h.rcx_after, ?_, ?_,
    repLodsSegAfter_segReady base 64 4 s h.seg⟩
  · intro i hi
    rw [hrip, repLodsSegAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repLodsSegAfter_external]
    exact h.srcMem (8 + i) (by omega)

structure RepLodsqSegDone [Bindings] (base : BitVec 64) (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 4)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (8 * count)
  raxAfter : (Operand.reg 0 : Operand 64).read t =
    mergeGPR 64
      ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (8 * (count - 1))) : Operand 64).read s)
      ((Operand.reg 0 : Operand 64).read s)
  agrees : AgreesExcept [.reg 0, .reg 1, .reg 6, .rip] (clearRep s) t

theorem rep_lodsq_seg_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {r : SegReg} {base : BitVec 64} {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (count : Nat) (s : RamState) (h : RepLodsqSegLoop r base rex s (count + 1)) :
    RepLodsqSegDone base s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repLodsSegAfter base 64 4 s) :=
      nextState_of_step (h.step hstride hrex (by omega))
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repLodsSegAfter base 64 4 s).Repeat_String_Operation = false := by
      rw [repLodsSegAfter_repeat, hc]; rfl
    refine ⟨(h.ready.repLodsSeg base 64 4).ready hflag, ?_, ?_, repLodsSegAfter_rsi base 64 4 s, ?_, ?_⟩
    · rw [repLodsSegAfter_rip base 64 4 s h.ready.msr, hc]; rfl
    · rw [repLodsSegAfter_rcx, hc]
    · rw [repLodsSegAfter_rax]
      simp only [Nat.zero_add, Nat.sub_self, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repLodsSeg base 64 4 s
  | succ m ih =>
    have hnext : nextState s = (repLodsSegAfter base 64 4 s) :=
      nextState_of_step (h.step hstride hrex (by omega))
    have hsreg : rsi.read (repLodsSegAfter base 64 4 s) = rsi.read s + BitVec.ofNat 64 8 :=
      repLodsSegAfter_rsi base 64 4 s
    have hs : base + rsi.read (repLodsSegAfter base 64 4 s) = base + rsi.read s + BitVec.ofNat 64 8 := by
      rw [hsreg, BitVec.add_assoc]
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 64).read (repLodsSegAfter base 64 4 s) =
          (Operand.mem a : Operand 64).read s := by
      simp only [Operand.read, repLodsSegAfter_external]
    have ih' := ih (repLodsSegAfter base 64 4 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repLodsSegAfter base 64 4 s).RIP = s.RIP := by
      rw [repLodsSegAfter_rip base 64 4 s h.ready.msr, h.counter]
      have := h.srcLow
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hsreg, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.raxAfter, repLodsSegAfter_rax, mergeGPR_mergeGPR 64 (by decide), hs, add_ofNat_add_ofNat,
        hm, show 8 + 8 * (m + 1 - 1) = 8 * (m + 1 + 1 - 1) by omega]
    · refine ((AgreesExcept.repLodsSeg base 64 4 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepLodsqSegPre (p : BitVec 64) (r : SegReg) (base : BitVec 64) (s : RamState) :
    Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (base + rsi.read s).toNat + 8 * (rcx.read s).toNat ≤ 2^32
  srcMem : ∀ i < 8 * (rcx.read s).toNat,
    (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  seg : r.Ready base s

def repLodsqSegEffect (p base : BitVec 64) (s : RamState) : Effect where
  rip := p + 4
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (8 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.reg 0 : Operand 64), if rcx.read s = 0 then (Operand.reg 0 : Operand 64).read s else
      ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (8 * ((rcx.read s).toNat - 1))) :
        Operand 64).read s)⟩]

@[simp] theorem repLodsqSegEffect_components (p base : BitVec 64) (s : RamState) :
    (repLodsqSegEffect p base s).components = [.reg 6, .reg 1, .reg 0, .rip] := by
  simp [repLodsqSegEffect, Effect.components]

theorem rep_lodsq_seg_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF3, rex, 0xAD]) s) (hpre : RepLodsqSegPre p r base s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF3, rex, 0xAD]) t ∧ (repLodsqSegEffect p base s).Holds s t := by
  intro t
  have hr := hrex.rexPrefix
  have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF3, rex, 0xAD] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  have hrep := h.ready.repeatClear
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3, rex] =
      withSeg (repRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3, rex] (noSegPrefix_cons noSegPrefix_f3 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_f3_rex _ _ hr]
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 4 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_lodsq_step_zero s h.midRep [r.prefixByte, 0xF3, rex]
        (scanPrefix_seg_cons r (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp)
        (by rw [hsc]; rfl)
        (by rw [hsc]; exact hrex.rex_w s.DS)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repZeroAfter 4 s) :=
      (AgreesExcept.repZero 4 s).of_clearRep hrep (repZeroAfter_repeat 4 s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables,
      hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, ?_, ?_⟩, trivial,
      hag.mono (by simp)⟩
    · rw [repZeroAfter_rip _ s h.ready.msr, hpre.rip]; rfl
    · rw [hag.read (by simp), hn]; simp
    · rw [hag.read (by simp), hz]
    · show (Operand.reg 0 : Operand 64).read _ = _
      rw [hag.read (by simp)]; simp [hz]
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.srcLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hnz : rcx.read s ≠ 0 := fun h0 => by simp [h0] at hn
    have hready : RepLodsqSegLoop r base rex s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.srcMem, hpre.seg⟩
    have hd := rep_lodsq_seg_loop hstride hrex c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, hd.rcxZero, ?_⟩,
      trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · rw [hd.rsiAfter, hn]
    · show _ = if rcx.read s = 0 then _ else _
      simp only [hnz, ↓reduceIte]
      rw [hd.raxAfter, hn]
      exact mergeGPR_64 _ _
    · rw [repLodsqSegEffect_components]
      refine hag.mono ?_
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem rep_lodsq_seg_triple_of_bytes [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepLodsqSegPre p r base) (codeRange p [r.prefixByte, 0xF3, rex, 0xAD]) (Effect.post (repLodsqSegEffect p base)) :=
  fun s h hcode hpre => ⟨_, rep_lodsq_seg_steps hstride p r base rex hrex s h hcode hpre⟩

theorem rep_lodsq_seg_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (RepLodsqSegPre p r base) (codeRange p [r.prefixByte, 0xF3, 0x48, 0xAD]) (Effect.post (repLodsqSegEffect p base)) :=
  rep_lodsq_seg_triple_of_bytes hstride p r base 0x48 (by unfold RexWPrefix; decide)

structure RepLodsdLoop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0xAD]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 4 * count ≤ 2^32
  srcMem : ∀ i < 4 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome

theorem RepLodsdLoop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepLodsdLoop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodsdLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count : Nat} (h : RepLodsdLoop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repLodsAfter 32 2 s)) := by
  have := h.srcLow
  exact rep_lodsd_step hstride s h.ready [0xF3] (by simpa using scanPrefix_f3) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne hpos) ⟨by omega, fun i hi => h.srcMem i (by omega)⟩

theorem RepLodsdLoop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepLodsdLoop s (count + 1)) : rcx.read (repLodsAfter 32 2 s) = BitVec.ofNat 64 count := by
  rw [repLodsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepLodsdLoop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepLodsdLoop s (count + 2)) : RepLodsdLoop (repLodsAfter 32 2 s) (count + 1) := by
  have hsl := h.srcLow
  have hrip : (repLodsAfter 32 2 s).RIP = s.RIP := by
    rw [repLodsAfter_rip 32 2 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : rsi.read (repLodsAfter 32 2 s) = rsi.read s + BitVec.ofNat 64 4 :=
    repLodsAfter_rsi 32 2 s
  have hsn : (rsi.read (repLodsAfter 32 2 s)).toNat = (rsi.read s).toNat + 4 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repLods 32 2, h.df, ?_, ?_, h.rcx_after, ?_, ?_⟩
  · intro i hi
    rw [hrip, repLodsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repLodsAfter_external]
    exact h.srcMem (4 + i) (by omega)

structure RepLodsdDone [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (4 * count)
  raxAfter : (Operand.reg 0 : Operand 64).read t =
    mergeGPR 32
      ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * (count - 1))) : Operand 32).read s)
      ((Operand.reg 0 : Operand 64).read s)
  agrees : AgreesExcept [.reg 0, .reg 1, .reg 6, .rip] (clearRep s) t

theorem rep_lodsd_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (count : Nat) (s : RamState) (h : RepLodsdLoop s (count + 1)) :
    RepLodsdDone s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repLodsAfter 32 2 s) :=
      nextState_of_step (h.step hstride (by omega))
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repLodsAfter 32 2 s).Repeat_String_Operation = false := by
      rw [repLodsAfter_repeat, hc]; rfl
    refine ⟨(h.ready.repLods 32 2).ready hflag, ?_, ?_, repLodsAfter_rsi 32 2 s, ?_, ?_⟩
    · rw [repLodsAfter_rip 32 2 s h.ready.msr, hc]; rfl
    · rw [repLodsAfter_rcx, hc]
    · rw [repLodsAfter_rax]
      simp only [Nat.zero_add, Nat.sub_self, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repLods 32 2 s
  | succ m ih =>
    have hnext : nextState s = (repLodsAfter 32 2 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hs : rsi.read (repLodsAfter 32 2 s) = rsi.read s + BitVec.ofNat 64 4 :=
      repLodsAfter_rsi 32 2 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 32).read (repLodsAfter 32 2 s) =
          (Operand.mem a : Operand 32).read s := by
      simp only [Operand.read, repLodsAfter_external]
    have ih' := ih (repLodsAfter 32 2 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repLodsAfter 32 2 s).RIP = s.RIP := by
      rw [repLodsAfter_rip 32 2 s h.ready.msr, h.counter]
      have := h.srcLow
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.raxAfter, repLodsAfter_rax, mergeGPR_mergeGPR 32 (by decide), hs, add_ofNat_add_ofNat,
        hm, show 4 + 4 * (m + 1 - 1) = 4 * (m + 1 + 1 - 1) by omega]
    · refine ((AgreesExcept.repLods 32 2 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepLodsdPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (rsi.read s).toNat + 4 * (rcx.read s).toNat ≤ 2^32
  srcMem : ∀ i < 4 * (rcx.read s).toNat, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome

def repLodsdEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (4 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.reg 0 : Operand 64), if rcx.read s = 0 then (Operand.reg 0 : Operand 64).read s else
      ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * ((rcx.read s).toNat - 1))) :
        Operand 32).read s).setWidth 64⟩]

@[simp] theorem repLodsdEffect_components (p : BitVec 64) (s : RamState) :
    (repLodsdEffect p s).components = [.reg 6, .reg 1, .reg 0, .rip] := by
  simp [repLodsdEffect, Effect.components]

theorem rep_lodsd_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0xAD]) s) (hpre : RepLodsdPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0xAD]) t ∧ (repLodsdEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF3, 0xAD] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 2 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_lodsd_step_zero s h.midRep [0xF3]
        (by simpa using scanPrefix_f3) (by simp)
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
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables,
      hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, ?_, ?_⟩, trivial,
      hag.mono (by simp)⟩
    · rw [repZeroAfter_rip _ s h.ready.msr, hpre.rip]; rfl
    · rw [hag.read (by simp), hn]; simp
    · rw [hag.read (by simp), hz]
    · show (Operand.reg 0 : Operand 64).read _ = _
      rw [hag.read (by simp)]; simp [hz]
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.srcLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hnz : rcx.read s ≠ 0 := fun h0 => by simp [h0] at hn
    have hready : RepLodsdLoop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.srcMem⟩
    have hd := rep_lodsd_loop hstride c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, hd.rcxZero, ?_⟩,
      trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · rw [hd.rsiAfter, hn]
    · show _ = if rcx.read s = 0 then _ else _
      simp only [hnz, ↓reduceIte]
      rw [hd.raxAfter, hn]
      exact mergeGPR_32 _ _
    · rw [repLodsdEffect_components]
      refine hag.mono ?_
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem rep_lodsd_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepLodsdPre p) (codeRange p [0xF3, 0xAD]) (Effect.post (repLodsdEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_lodsd_steps hstride p s h hcode hpre⟩

structure RepLodsdSegLoop [Bindings] (r : SegReg) (base : BitVec 64) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF3, 0xAD]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (base + rsi.read s).toNat + 4 * count ≤ 2^32
  srcMem : ∀ i < 4 * count, (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  seg : r.Ready base s

theorem RepLodsdSegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepLodsdSegLoop r base s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodsdSegLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat} (h : RepLodsdSegLoop r base s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repLodsSegAfter base 32 3 s)) := by
  have := h.srcLow
  have hsrc : MemReadable s (base + rsi.read s) 4 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3] (noSegPrefix_cons noSegPrefix_f3 noSegPrefix_nil)]
  have hstep := rep_lodsd_seg_step hstride s h.ready [r.prefixByte, 0xF3] (scanPrefix_seg_cons r (by simpa using scanPrefix_f3)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    h.df h.code h.codeLow (h.rcx_ne hpos) (by rw [hsc]; exact hsrc)
  rw [hsc] at hstep
  exact hstep

theorem RepLodsdSegLoop.rcx_after [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepLodsdSegLoop r base s (count + 1)) : rcx.read (repLodsSegAfter base 32 3 s) = BitVec.ofNat 64 count := by
  rw [repLodsSegAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepLodsdSegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepLodsdSegLoop r base s (count + 2)) : RepLodsdSegLoop r base (repLodsSegAfter base 32 3 s) (count + 1) := by
  have hsl := h.srcLow
  have hrip : (repLodsSegAfter base 32 3 s).RIP = s.RIP := by
    rw [repLodsSegAfter_rip base 32 3 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : base + rsi.read (repLodsSegAfter base 32 3 s) = base + rsi.read s + BitVec.ofNat 64 4 := by
    rw [repLodsSegAfter_rsi base 32 3 s, BitVec.add_assoc]
  have hsn : (base + rsi.read (repLodsSegAfter base 32 3 s)).toNat = (base + rsi.read s).toNat + 4 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repLodsSeg base 32 3, h.df, ?_, ?_, h.rcx_after, ?_, ?_,
    repLodsSegAfter_segReady base 32 3 s h.seg⟩
  · intro i hi
    rw [hrip, repLodsSegAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repLodsSegAfter_external]
    exact h.srcMem (4 + i) (by omega)

structure RepLodsdSegDone [Bindings] (base : BitVec 64) (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (4 * count)
  raxAfter : (Operand.reg 0 : Operand 64).read t =
    mergeGPR 32
      ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (4 * (count - 1))) : Operand 32).read s)
      ((Operand.reg 0 : Operand 64).read s)
  agrees : AgreesExcept [.reg 0, .reg 1, .reg 6, .rip] (clearRep s) t

theorem rep_lodsd_seg_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {r : SegReg} {base : BitVec 64} (count : Nat) (s : RamState) (h : RepLodsdSegLoop r base s (count + 1)) :
    RepLodsdSegDone base s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repLodsSegAfter base 32 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repLodsSegAfter base 32 3 s).Repeat_String_Operation = false := by
      rw [repLodsSegAfter_repeat, hc]; rfl
    refine ⟨(h.ready.repLodsSeg base 32 3).ready hflag, ?_, ?_, repLodsSegAfter_rsi base 32 3 s, ?_, ?_⟩
    · rw [repLodsSegAfter_rip base 32 3 s h.ready.msr, hc]; rfl
    · rw [repLodsSegAfter_rcx, hc]
    · rw [repLodsSegAfter_rax]
      simp only [Nat.zero_add, Nat.sub_self, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repLodsSeg base 32 3 s
  | succ m ih =>
    have hnext : nextState s = (repLodsSegAfter base 32 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsreg : rsi.read (repLodsSegAfter base 32 3 s) = rsi.read s + BitVec.ofNat 64 4 :=
      repLodsSegAfter_rsi base 32 3 s
    have hs : base + rsi.read (repLodsSegAfter base 32 3 s) = base + rsi.read s + BitVec.ofNat 64 4 := by
      rw [hsreg, BitVec.add_assoc]
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 32).read (repLodsSegAfter base 32 3 s) =
          (Operand.mem a : Operand 32).read s := by
      simp only [Operand.read, repLodsSegAfter_external]
    have ih' := ih (repLodsSegAfter base 32 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repLodsSegAfter base 32 3 s).RIP = s.RIP := by
      rw [repLodsSegAfter_rip base 32 3 s h.ready.msr, h.counter]
      have := h.srcLow
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hsreg, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.raxAfter, repLodsSegAfter_rax, mergeGPR_mergeGPR 32 (by decide), hs, add_ofNat_add_ofNat,
        hm, show 4 + 4 * (m + 1 - 1) = 4 * (m + 1 + 1 - 1) by omega]
    · refine ((AgreesExcept.repLodsSeg base 32 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepLodsdSegPre (p : BitVec 64) (r : SegReg) (base : BitVec 64) (s : RamState) :
    Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (base + rsi.read s).toNat + 4 * (rcx.read s).toNat ≤ 2^32
  srcMem : ∀ i < 4 * (rcx.read s).toNat,
    (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  seg : r.Ready base s

def repLodsdSegEffect (p base : BitVec 64) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (4 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.reg 0 : Operand 64), if rcx.read s = 0 then (Operand.reg 0 : Operand 64).read s else
      ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (4 * ((rcx.read s).toNat - 1))) :
        Operand 32).read s).setWidth 64⟩]

@[simp] theorem repLodsdSegEffect_components (p base : BitVec 64) (s : RamState) :
    (repLodsdSegEffect p base s).components = [.reg 6, .reg 1, .reg 0, .rip] := by
  simp [repLodsdSegEffect, Effect.components]

theorem rep_lodsd_seg_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF3, 0xAD]) s) (hpre : RepLodsdSegPre p r base s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF3, 0xAD]) t ∧ (repLodsdSegEffect p base s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF3, 0xAD] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  have hrep := h.ready.repeatClear
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3] (noSegPrefix_cons noSegPrefix_f3 noSegPrefix_nil)]
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_lodsd_step_zero s h.midRep [r.prefixByte, 0xF3]
        (scanPrefix_seg_cons r (by simpa using scanPrefix_f3)) (by simp)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repZeroAfter 3 s) :=
      (AgreesExcept.repZero 3 s).of_clearRep hrep (repZeroAfter_repeat 3 s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables,
      hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, ?_, ?_⟩, trivial,
      hag.mono (by simp)⟩
    · rw [repZeroAfter_rip _ s h.ready.msr, hpre.rip]; rfl
    · rw [hag.read (by simp), hn]; simp
    · rw [hag.read (by simp), hz]
    · show (Operand.reg 0 : Operand 64).read _ = _
      rw [hag.read (by simp)]; simp [hz]
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.srcLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hnz : rcx.read s ≠ 0 := fun h0 => by simp [h0] at hn
    have hready : RepLodsdSegLoop r base s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.srcMem, hpre.seg⟩
    have hd := rep_lodsd_seg_loop hstride c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, hd.rcxZero, ?_⟩,
      trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · rw [hd.rsiAfter, hn]
    · show _ = if rcx.read s = 0 then _ else _
      simp only [hnz, ↓reduceIte]
      rw [hd.raxAfter, hn]
      exact mergeGPR_32 _ _
    · rw [repLodsdSegEffect_components]
      refine hag.mono ?_
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem rep_lodsd_seg_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (RepLodsdSegPre p r base) (codeRange p [r.prefixByte, 0xF3, 0xAD]) (Effect.post (repLodsdSegEffect p base)) :=
  fun s h hcode hpre => ⟨_, rep_lodsd_seg_steps hstride p r base s h hcode hpre⟩

structure RepLodswLoop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0x66, 0xAD]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 2 * count ≤ 2^32
  srcMem : ∀ i < 2 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome

theorem RepLodswLoop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepLodswLoop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodswLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count : Nat} (h : RepLodswLoop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repLodsAfter 16 3 s)) := by
  have := h.srcLow
  exact rep_lodsw_step hstride s h.ready [0xF3, 0x66] (by simp [scanPrefix_f3, scanPrefix_66]) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne hpos) ⟨by omega, fun i hi => h.srcMem i (by omega)⟩

theorem RepLodswLoop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepLodswLoop s (count + 1)) : rcx.read (repLodsAfter 16 3 s) = BitVec.ofNat 64 count := by
  rw [repLodsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepLodswLoop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepLodswLoop s (count + 2)) : RepLodswLoop (repLodsAfter 16 3 s) (count + 1) := by
  have hsl := h.srcLow
  have hrip : (repLodsAfter 16 3 s).RIP = s.RIP := by
    rw [repLodsAfter_rip 16 3 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : rsi.read (repLodsAfter 16 3 s) = rsi.read s + BitVec.ofNat 64 2 :=
    repLodsAfter_rsi 16 3 s
  have hsn : (rsi.read (repLodsAfter 16 3 s)).toNat = (rsi.read s).toNat + 2 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repLods 16 3, h.df, ?_, ?_, h.rcx_after, ?_, ?_⟩
  · intro i hi
    rw [hrip, repLodsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repLodsAfter_external]
    exact h.srcMem (2 + i) (by omega)

structure RepLodswDone [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (2 * count)
  raxAfter : (Operand.reg 0 : Operand 64).read t =
    mergeGPR 16
      ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * (count - 1))) : Operand 16).read s)
      ((Operand.reg 0 : Operand 64).read s)
  agrees : AgreesExcept [.reg 0, .reg 1, .reg 6, .rip] (clearRep s) t

theorem rep_lodsw_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (count : Nat) (s : RamState) (h : RepLodswLoop s (count + 1)) :
    RepLodswDone s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repLodsAfter 16 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repLodsAfter 16 3 s).Repeat_String_Operation = false := by
      rw [repLodsAfter_repeat, hc]; rfl
    refine ⟨(h.ready.repLods 16 3).ready hflag, ?_, ?_, repLodsAfter_rsi 16 3 s, ?_, ?_⟩
    · rw [repLodsAfter_rip 16 3 s h.ready.msr, hc]; rfl
    · rw [repLodsAfter_rcx, hc]
    · rw [repLodsAfter_rax]
      simp only [Nat.zero_add, Nat.sub_self, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repLods 16 3 s
  | succ m ih =>
    have hnext : nextState s = (repLodsAfter 16 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hs : rsi.read (repLodsAfter 16 3 s) = rsi.read s + BitVec.ofNat 64 2 :=
      repLodsAfter_rsi 16 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 16).read (repLodsAfter 16 3 s) =
          (Operand.mem a : Operand 16).read s := by
      simp only [Operand.read, repLodsAfter_external]
    have ih' := ih (repLodsAfter 16 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repLodsAfter 16 3 s).RIP = s.RIP := by
      rw [repLodsAfter_rip 16 3 s h.ready.msr, h.counter]
      have := h.srcLow
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.raxAfter, repLodsAfter_rax, mergeGPR_mergeGPR 16 (by decide), hs, add_ofNat_add_ofNat,
        hm, show 2 + 2 * (m + 1 - 1) = 2 * (m + 1 + 1 - 1) by omega]
    · refine ((AgreesExcept.repLods 16 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepLodswPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (rsi.read s).toNat + 2 * (rcx.read s).toNat ≤ 2^32
  srcMem : ∀ i < 2 * (rcx.read s).toNat, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome

def repLodswEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (2 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.reg 0 : Operand 64), if rcx.read s = 0 then (Operand.reg 0 : Operand 64).read s else
      mergeGPR 16 ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * ((rcx.read s).toNat - 1))) :
        Operand 16).read s)
        ((Operand.reg 0 : Operand 64).read s)⟩]

@[simp] theorem repLodswEffect_components (p : BitVec 64) (s : RamState) :
    (repLodswEffect p s).components = [.reg 6, .reg 1, .reg 0, .rip] := by
  simp [repLodswEffect, Effect.components]

theorem rep_lodsw_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0x66, 0xAD]) s) (hpre : RepLodswPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0x66, 0xAD]) t ∧ (repLodswEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF3, 0x66, 0xAD] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_lodsw_step_zero s h.midRep [0xF3, 0x66]
        (by simp [scanPrefix_f3, scanPrefix_66]) (by simp)
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
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables,
      hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, ?_, ?_⟩, trivial,
      hag.mono (by simp)⟩
    · rw [repZeroAfter_rip _ s h.ready.msr, hpre.rip]; rfl
    · rw [hag.read (by simp), hn]; simp
    · rw [hag.read (by simp), hz]
    · show (Operand.reg 0 : Operand 64).read _ = _
      rw [hag.read (by simp)]; simp [hz]
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.srcLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hnz : rcx.read s ≠ 0 := fun h0 => by simp [h0] at hn
    have hready : RepLodswLoop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.srcMem⟩
    have hd := rep_lodsw_loop hstride c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, hd.rcxZero, ?_⟩,
      trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · rw [hd.rsiAfter, hn]
    · show _ = if rcx.read s = 0 then _ else _
      simp only [hnz, ↓reduceIte]
      rw [hd.raxAfter, hn]
    · rw [repLodswEffect_components]
      refine hag.mono ?_
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem rep_lodsw_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepLodswPre p) (codeRange p [0xF3, 0x66, 0xAD]) (Effect.post (repLodswEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_lodsw_steps hstride p s h hcode hpre⟩

structure RepLodswSegLoop [Bindings] (r : SegReg) (base : BitVec 64) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF3, 0x66, 0xAD]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (base + rsi.read s).toNat + 2 * count ≤ 2^32
  srcMem : ∀ i < 2 * count, (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  seg : r.Ready base s

theorem RepLodswSegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepLodswSegLoop r base s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodswSegLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat} (h : RepLodswSegLoop r base s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repLodsSegAfter base 16 4 s)) := by
  have := h.srcLow
  have hsrc : MemReadable s (base + rsi.read s) 2 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3, 0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3, 0x66] (noSegPrefix_cons noSegPrefix_f3 (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil))]
  have hstep := rep_lodsw_seg_step hstride s h.ready [r.prefixByte, 0xF3, 0x66] (scanPrefix_seg_cons r (by simp [scanPrefix_f3, scanPrefix_66])) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    h.df h.code h.codeLow (h.rcx_ne hpos) (by rw [hsc]; exact hsrc)
  rw [hsc] at hstep
  exact hstep

theorem RepLodswSegLoop.rcx_after [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepLodswSegLoop r base s (count + 1)) : rcx.read (repLodsSegAfter base 16 4 s) = BitVec.ofNat 64 count := by
  rw [repLodsSegAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepLodswSegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepLodswSegLoop r base s (count + 2)) : RepLodswSegLoop r base (repLodsSegAfter base 16 4 s) (count + 1) := by
  have hsl := h.srcLow
  have hrip : (repLodsSegAfter base 16 4 s).RIP = s.RIP := by
    rw [repLodsSegAfter_rip base 16 4 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : base + rsi.read (repLodsSegAfter base 16 4 s) = base + rsi.read s + BitVec.ofNat 64 2 := by
    rw [repLodsSegAfter_rsi base 16 4 s, BitVec.add_assoc]
  have hsn : (base + rsi.read (repLodsSegAfter base 16 4 s)).toNat = (base + rsi.read s).toNat + 2 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repLodsSeg base 16 4, h.df, ?_, ?_, h.rcx_after, ?_, ?_,
    repLodsSegAfter_segReady base 16 4 s h.seg⟩
  · intro i hi
    rw [hrip, repLodsSegAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repLodsSegAfter_external]
    exact h.srcMem (2 + i) (by omega)

structure RepLodswSegDone [Bindings] (base : BitVec 64) (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 4)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (2 * count)
  raxAfter : (Operand.reg 0 : Operand 64).read t =
    mergeGPR 16
      ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (2 * (count - 1))) : Operand 16).read s)
      ((Operand.reg 0 : Operand 64).read s)
  agrees : AgreesExcept [.reg 0, .reg 1, .reg 6, .rip] (clearRep s) t

theorem rep_lodsw_seg_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {r : SegReg} {base : BitVec 64} (count : Nat) (s : RamState) (h : RepLodswSegLoop r base s (count + 1)) :
    RepLodswSegDone base s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repLodsSegAfter base 16 4 s) :=
      nextState_of_step (h.step hstride (by omega))
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repLodsSegAfter base 16 4 s).Repeat_String_Operation = false := by
      rw [repLodsSegAfter_repeat, hc]; rfl
    refine ⟨(h.ready.repLodsSeg base 16 4).ready hflag, ?_, ?_, repLodsSegAfter_rsi base 16 4 s, ?_, ?_⟩
    · rw [repLodsSegAfter_rip base 16 4 s h.ready.msr, hc]; rfl
    · rw [repLodsSegAfter_rcx, hc]
    · rw [repLodsSegAfter_rax]
      simp only [Nat.zero_add, Nat.sub_self, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repLodsSeg base 16 4 s
  | succ m ih =>
    have hnext : nextState s = (repLodsSegAfter base 16 4 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsreg : rsi.read (repLodsSegAfter base 16 4 s) = rsi.read s + BitVec.ofNat 64 2 :=
      repLodsSegAfter_rsi base 16 4 s
    have hs : base + rsi.read (repLodsSegAfter base 16 4 s) = base + rsi.read s + BitVec.ofNat 64 2 := by
      rw [hsreg, BitVec.add_assoc]
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 16).read (repLodsSegAfter base 16 4 s) =
          (Operand.mem a : Operand 16).read s := by
      simp only [Operand.read, repLodsSegAfter_external]
    have ih' := ih (repLodsSegAfter base 16 4 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repLodsSegAfter base 16 4 s).RIP = s.RIP := by
      rw [repLodsSegAfter_rip base 16 4 s h.ready.msr, h.counter]
      have := h.srcLow
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hsreg, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.raxAfter, repLodsSegAfter_rax, mergeGPR_mergeGPR 16 (by decide), hs, add_ofNat_add_ofNat,
        hm, show 2 + 2 * (m + 1 - 1) = 2 * (m + 1 + 1 - 1) by omega]
    · refine ((AgreesExcept.repLodsSeg base 16 4 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepLodswSegPre (p : BitVec 64) (r : SegReg) (base : BitVec 64) (s : RamState) :
    Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (base + rsi.read s).toNat + 2 * (rcx.read s).toNat ≤ 2^32
  srcMem : ∀ i < 2 * (rcx.read s).toNat,
    (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  seg : r.Ready base s

def repLodswSegEffect (p base : BitVec 64) (s : RamState) : Effect where
  rip := p + 4
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (2 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.reg 0 : Operand 64), if rcx.read s = 0 then (Operand.reg 0 : Operand 64).read s else
      mergeGPR 16 ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (2 * ((rcx.read s).toNat - 1))) :
        Operand 16).read s)
        ((Operand.reg 0 : Operand 64).read s)⟩]

@[simp] theorem repLodswSegEffect_components (p base : BitVec 64) (s : RamState) :
    (repLodswSegEffect p base s).components = [.reg 6, .reg 1, .reg 0, .rip] := by
  simp [repLodswSegEffect, Effect.components]

theorem rep_lodsw_seg_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF3, 0x66, 0xAD]) s) (hpre : RepLodswSegPre p r base s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF3, 0x66, 0xAD]) t ∧ (repLodswSegEffect p base s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF3, 0x66, 0xAD] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  have hrep := h.ready.repeatClear
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3, 0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3, 0x66] (noSegPrefix_cons noSegPrefix_f3 (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil))]
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 4 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_lodsw_step_zero s h.midRep [r.prefixByte, 0xF3, 0x66]
        (scanPrefix_seg_cons r (by simp [scanPrefix_f3, scanPrefix_66])) (by simp)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repZeroAfter 4 s) :=
      (AgreesExcept.repZero 4 s).of_clearRep hrep (repZeroAfter_repeat 4 s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables,
      hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, ?_, ?_⟩, trivial,
      hag.mono (by simp)⟩
    · rw [repZeroAfter_rip _ s h.ready.msr, hpre.rip]; rfl
    · rw [hag.read (by simp), hn]; simp
    · rw [hag.read (by simp), hz]
    · show (Operand.reg 0 : Operand 64).read _ = _
      rw [hag.read (by simp)]; simp [hz]
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.srcLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hnz : rcx.read s ≠ 0 := fun h0 => by simp [h0] at hn
    have hready : RepLodswSegLoop r base s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.srcMem, hpre.seg⟩
    have hd := rep_lodsw_seg_loop hstride c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, hd.rcxZero, ?_⟩,
      trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · rw [hd.rsiAfter, hn]
    · show _ = if rcx.read s = 0 then _ else _
      simp only [hnz, ↓reduceIte]
      rw [hd.raxAfter, hn]
    · rw [repLodswSegEffect_components]
      refine hag.mono ?_
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem rep_lodsw_seg_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (RepLodswSegPre p r base) (codeRange p [r.prefixByte, 0xF3, 0x66, 0xAD]) (Effect.post (repLodswSegEffect p base)) :=
  fun s h hcode hpre => ⟨_, rep_lodsw_seg_steps hstride p r base s h hcode hpre⟩

structure RepLodsbLoop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0xAC]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 1 * count ≤ 2^32
  srcMem : ∀ i < 1 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome

theorem RepLodsbLoop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepLodsbLoop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodsbLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count : Nat} (h : RepLodsbLoop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repLodsAfter 8 2 s)) := by
  have := h.srcLow
  exact rep_lodsb_step hstride s h.ready [0xF3] (by simpa using scanPrefix_f3) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne hpos) ⟨by omega, fun i hi => h.srcMem i (by omega)⟩

theorem RepLodsbLoop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepLodsbLoop s (count + 1)) : rcx.read (repLodsAfter 8 2 s) = BitVec.ofNat 64 count := by
  rw [repLodsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepLodsbLoop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepLodsbLoop s (count + 2)) : RepLodsbLoop (repLodsAfter 8 2 s) (count + 1) := by
  have hsl := h.srcLow
  have hrip : (repLodsAfter 8 2 s).RIP = s.RIP := by
    rw [repLodsAfter_rip 8 2 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : rsi.read (repLodsAfter 8 2 s) = rsi.read s + BitVec.ofNat 64 1 :=
    repLodsAfter_rsi 8 2 s
  have hsn : (rsi.read (repLodsAfter 8 2 s)).toNat = (rsi.read s).toNat + 1 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repLods 8 2, h.df, ?_, ?_, h.rcx_after, ?_, ?_⟩
  · intro i hi
    rw [hrip, repLodsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repLodsAfter_external]
    exact h.srcMem (1 + i) (by omega)

structure RepLodsbDone [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (1 * count)
  raxAfter : (Operand.reg 0 : Operand 64).read t =
    mergeGPR 8
      ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * (count - 1))) : Operand 8).read s)
      ((Operand.reg 0 : Operand 64).read s)
  agrees : AgreesExcept [.reg 0, .reg 1, .reg 6, .rip] (clearRep s) t

theorem rep_lodsb_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (count : Nat) (s : RamState) (h : RepLodsbLoop s (count + 1)) :
    RepLodsbDone s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repLodsAfter 8 2 s) :=
      nextState_of_step (h.step hstride (by omega))
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repLodsAfter 8 2 s).Repeat_String_Operation = false := by
      rw [repLodsAfter_repeat, hc]; rfl
    refine ⟨(h.ready.repLods 8 2).ready hflag, ?_, ?_, repLodsAfter_rsi 8 2 s, ?_, ?_⟩
    · rw [repLodsAfter_rip 8 2 s h.ready.msr, hc]; rfl
    · rw [repLodsAfter_rcx, hc]
    · rw [repLodsAfter_rax]
      simp only [Nat.zero_add, Nat.sub_self, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repLods 8 2 s
  | succ m ih =>
    have hnext : nextState s = (repLodsAfter 8 2 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hs : rsi.read (repLodsAfter 8 2 s) = rsi.read s + BitVec.ofNat 64 1 :=
      repLodsAfter_rsi 8 2 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 8).read (repLodsAfter 8 2 s) =
          (Operand.mem a : Operand 8).read s := by
      simp only [Operand.read, repLodsAfter_external]
    have ih' := ih (repLodsAfter 8 2 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repLodsAfter 8 2 s).RIP = s.RIP := by
      rw [repLodsAfter_rip 8 2 s h.ready.msr, h.counter]
      have := h.srcLow
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.raxAfter, repLodsAfter_rax, mergeGPR_mergeGPR 8 (by decide), hs, add_ofNat_add_ofNat,
        hm, show 1 + 1 * (m + 1 - 1) = 1 * (m + 1 + 1 - 1) by omega]
    · refine ((AgreesExcept.repLods 8 2 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepLodsbPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (rsi.read s).toNat + 1 * (rcx.read s).toNat ≤ 2^32
  srcMem : ∀ i < 1 * (rcx.read s).toNat, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome

def repLodsbEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (1 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.reg 0 : Operand 64), if rcx.read s = 0 then (Operand.reg 0 : Operand 64).read s else
      mergeGPR 8 ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * ((rcx.read s).toNat - 1))) :
        Operand 8).read s)
        ((Operand.reg 0 : Operand 64).read s)⟩]

@[simp] theorem repLodsbEffect_components (p : BitVec 64) (s : RamState) :
    (repLodsbEffect p s).components = [.reg 6, .reg 1, .reg 0, .rip] := by
  simp [repLodsbEffect, Effect.components]

theorem rep_lodsb_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0xAC]) s) (hpre : RepLodsbPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0xAC]) t ∧ (repLodsbEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF3, 0xAC] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 2 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_lodsb_step_zero s h.midRep [0xF3]
        (by simpa using scanPrefix_f3) (by simp)
        rfl
        rfl
        rfl
        rfl
        hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repZeroAfter 2 s) :=
      (AgreesExcept.repZero 2 s).of_clearRep hrep (repZeroAfter_repeat 2 s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables,
      hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, ?_, ?_⟩, trivial,
      hag.mono (by simp)⟩
    · rw [repZeroAfter_rip _ s h.ready.msr, hpre.rip]; rfl
    · rw [hag.read (by simp), hn]; simp
    · rw [hag.read (by simp), hz]
    · show (Operand.reg 0 : Operand 64).read _ = _
      rw [hag.read (by simp)]; simp [hz]
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.srcLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hnz : rcx.read s ≠ 0 := fun h0 => by simp [h0] at hn
    have hready : RepLodsbLoop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.srcMem⟩
    have hd := rep_lodsb_loop hstride c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, hd.rcxZero, ?_⟩,
      trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · rw [hd.rsiAfter, hn]
    · show _ = if rcx.read s = 0 then _ else _
      simp only [hnz, ↓reduceIte]
      rw [hd.raxAfter, hn]
    · rw [repLodsbEffect_components]
      refine hag.mono ?_
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem rep_lodsb_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepLodsbPre p) (codeRange p [0xF3, 0xAC]) (Effect.post (repLodsbEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_lodsb_steps hstride p s h hcode hpre⟩

structure RepLodsbSegLoop [Bindings] (r : SegReg) (base : BitVec 64) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF3, 0xAC]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (base + rsi.read s).toNat + 1 * count ≤ 2^32
  srcMem : ∀ i < 1 * count, (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  seg : r.Ready base s

theorem RepLodsbSegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepLodsbSegLoop r base s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodsbSegLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat} (h : RepLodsbSegLoop r base s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repLodsSegAfter base 8 3 s)) := by
  have := h.srcLow
  have hsrc : MemReadable s (base + rsi.read s) 1 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3] (noSegPrefix_cons noSegPrefix_f3 noSegPrefix_nil)]
  have hstep := rep_lodsb_seg_step hstride s h.ready [r.prefixByte, 0xF3] (scanPrefix_seg_cons r (by simpa using scanPrefix_f3)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    h.df h.code h.codeLow (h.rcx_ne hpos) (by rw [hsc]; exact hsrc)
  rw [hsc] at hstep
  exact hstep

theorem RepLodsbSegLoop.rcx_after [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepLodsbSegLoop r base s (count + 1)) : rcx.read (repLodsSegAfter base 8 3 s) = BitVec.ofNat 64 count := by
  rw [repLodsSegAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepLodsbSegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepLodsbSegLoop r base s (count + 2)) : RepLodsbSegLoop r base (repLodsSegAfter base 8 3 s) (count + 1) := by
  have hsl := h.srcLow
  have hrip : (repLodsSegAfter base 8 3 s).RIP = s.RIP := by
    rw [repLodsSegAfter_rip base 8 3 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : base + rsi.read (repLodsSegAfter base 8 3 s) = base + rsi.read s + BitVec.ofNat 64 1 := by
    rw [repLodsSegAfter_rsi base 8 3 s, BitVec.add_assoc]
  have hsn : (base + rsi.read (repLodsSegAfter base 8 3 s)).toNat = (base + rsi.read s).toNat + 1 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repLodsSeg base 8 3, h.df, ?_, ?_, h.rcx_after, ?_, ?_,
    repLodsSegAfter_segReady base 8 3 s h.seg⟩
  · intro i hi
    rw [hrip, repLodsSegAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repLodsSegAfter_external]
    exact h.srcMem (1 + i) (by omega)

structure RepLodsbSegDone [Bindings] (base : BitVec 64) (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (1 * count)
  raxAfter : (Operand.reg 0 : Operand 64).read t =
    mergeGPR 8
      ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (1 * (count - 1))) : Operand 8).read s)
      ((Operand.reg 0 : Operand 64).read s)
  agrees : AgreesExcept [.reg 0, .reg 1, .reg 6, .rip] (clearRep s) t

theorem rep_lodsb_seg_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {r : SegReg} {base : BitVec 64} (count : Nat) (s : RamState) (h : RepLodsbSegLoop r base s (count + 1)) :
    RepLodsbSegDone base s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repLodsSegAfter base 8 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repLodsSegAfter base 8 3 s).Repeat_String_Operation = false := by
      rw [repLodsSegAfter_repeat, hc]; rfl
    refine ⟨(h.ready.repLodsSeg base 8 3).ready hflag, ?_, ?_, repLodsSegAfter_rsi base 8 3 s, ?_, ?_⟩
    · rw [repLodsSegAfter_rip base 8 3 s h.ready.msr, hc]; rfl
    · rw [repLodsSegAfter_rcx, hc]
    · rw [repLodsSegAfter_rax]
      simp only [Nat.zero_add, Nat.sub_self, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repLodsSeg base 8 3 s
  | succ m ih =>
    have hnext : nextState s = (repLodsSegAfter base 8 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsreg : rsi.read (repLodsSegAfter base 8 3 s) = rsi.read s + BitVec.ofNat 64 1 :=
      repLodsSegAfter_rsi base 8 3 s
    have hs : base + rsi.read (repLodsSegAfter base 8 3 s) = base + rsi.read s + BitVec.ofNat 64 1 := by
      rw [hsreg, BitVec.add_assoc]
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 8).read (repLodsSegAfter base 8 3 s) =
          (Operand.mem a : Operand 8).read s := by
      simp only [Operand.read, repLodsSegAfter_external]
    have ih' := ih (repLodsSegAfter base 8 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repLodsSegAfter base 8 3 s).RIP = s.RIP := by
      rw [repLodsSegAfter_rip base 8 3 s h.ready.msr, h.counter]
      have := h.srcLow
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hsreg, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.raxAfter, repLodsSegAfter_rax, mergeGPR_mergeGPR 8 (by decide), hs, add_ofNat_add_ofNat,
        hm, show 1 + 1 * (m + 1 - 1) = 1 * (m + 1 + 1 - 1) by omega]
    · refine ((AgreesExcept.repLodsSeg base 8 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepLodsbSegPre (p : BitVec 64) (r : SegReg) (base : BitVec 64) (s : RamState) :
    Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (base + rsi.read s).toNat + 1 * (rcx.read s).toNat ≤ 2^32
  srcMem : ∀ i < 1 * (rcx.read s).toNat,
    (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  seg : r.Ready base s

def repLodsbSegEffect (p base : BitVec 64) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (1 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.reg 0 : Operand 64), if rcx.read s = 0 then (Operand.reg 0 : Operand 64).read s else
      mergeGPR 8 ((Operand.mem (base + rsi.read s + BitVec.ofNat 64 (1 * ((rcx.read s).toNat - 1))) :
        Operand 8).read s)
        ((Operand.reg 0 : Operand 64).read s)⟩]

@[simp] theorem repLodsbSegEffect_components (p base : BitVec 64) (s : RamState) :
    (repLodsbSegEffect p base s).components = [.reg 6, .reg 1, .reg 0, .rip] := by
  simp [repLodsbSegEffect, Effect.components]

theorem rep_lodsb_seg_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF3, 0xAC]) s) (hpre : RepLodsbSegPre p r base s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF3, 0xAC]) t ∧ (repLodsbSegEffect p base s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF3, 0xAC] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  have hrep := h.ready.repeatClear
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3] (noSegPrefix_cons noSegPrefix_f3 noSegPrefix_nil)]
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_lodsb_step_zero s h.midRep [r.prefixByte, 0xF3]
        (scanPrefix_seg_cons r (by simpa using scanPrefix_f3)) (by simp)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        (by rw [hsc]; rfl)
        hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repZeroAfter 3 s) :=
      (AgreesExcept.repZero 3 s).of_clearRep hrep (repZeroAfter_repeat 3 s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables,
      hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, ?_, ?_⟩, trivial,
      hag.mono (by simp)⟩
    · rw [repZeroAfter_rip _ s h.ready.msr, hpre.rip]; rfl
    · rw [hag.read (by simp), hn]; simp
    · rw [hag.read (by simp), hz]
    · show (Operand.reg 0 : Operand 64).read _ = _
      rw [hag.read (by simp)]; simp [hz]
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.srcLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hnz : rcx.read s ≠ 0 := fun h0 => by simp [h0] at hn
    have hready : RepLodsbSegLoop r base s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.srcMem, hpre.seg⟩
    have hd := rep_lodsb_seg_loop hstride c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, hd.rcxZero, ?_⟩,
      trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · rw [hd.rsiAfter, hn]
    · show _ = if rcx.read s = 0 then _ else _
      simp only [hnz, ↓reduceIte]
      rw [hd.raxAfter, hn]
    · rw [repLodsbSegEffect_components]
      refine hag.mono ?_
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem rep_lodsb_seg_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (RepLodsbSegPre p r base) (codeRange p [r.prefixByte, 0xF3, 0xAC]) (Effect.post (repLodsbSegEffect p base)) :=
  fun s h hcode hpre => ⟨_, rep_lodsb_seg_steps hstride p r base s h hcode hpre⟩

structure RepLodsqA32Loop [Bindings] (rex : UInt8) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF3, rex, 0xAD]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 8 * count < 2^32
  srcMem : ∀ i < 8 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome

theorem RepLodsqA32Loop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepLodsqA32Loop rex s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodsqA32Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState} {count : Nat} (h : RepLodsqA32Loop rex s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repLodsAfter 64 4 s)) := by
  have hr := hrex.rexPrefix
  have := h.srcLow
  exact rep_lodsq_a32_step hstride s h.ready [0x67, 0xF3, rex] (scanPrefix_asz_cons (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
    h.df h.code h.codeLow (h.rcx_ne hpos) ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
    (by omega) (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)

theorem RepLodsqA32Loop.rcx_after [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepLodsqA32Loop rex s (count + 1)) : rcx.read (repLodsAfter 64 4 s) = BitVec.ofNat 64 count := by
  rw [repLodsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepLodsqA32Loop.next [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepLodsqA32Loop rex s (count + 2)) : RepLodsqA32Loop rex (repLodsAfter 64 4 s) (count + 1) := by
  have hsl := h.srcLow
  have hrip : (repLodsAfter 64 4 s).RIP = s.RIP := by
    rw [repLodsAfter_rip 64 4 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : rsi.read (repLodsAfter 64 4 s) = rsi.read s + BitVec.ofNat 64 8 :=
    repLodsAfter_rsi 64 4 s
  have hsn : (rsi.read (repLodsAfter 64 4 s)).toNat = (rsi.read s).toNat + 8 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repLods 64 4, h.df, ?_, ?_, h.rcx_after, ?_, ?_⟩
  · intro i hi
    rw [hrip, repLodsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repLodsAfter_external]
    exact h.srcMem (8 + i) (by omega)

structure RepLodsqA32Done [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 4)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (8 * count)
  raxAfter : (Operand.reg 0 : Operand 64).read t =
    mergeGPR 64
      ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * (count - 1))) : Operand 64).read s)
      ((Operand.reg 0 : Operand 64).read s)
  agrees : AgreesExcept [.reg 0, .reg 1, .reg 6, .rip] (clearRep s) t

theorem rep_lodsq_a32_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (count : Nat) (s : RamState) (h : RepLodsqA32Loop rex s (count + 1)) :
    RepLodsqA32Done s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repLodsAfter 64 4 s) :=
      nextState_of_step (h.step hstride hrex (by omega))
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repLodsAfter 64 4 s).Repeat_String_Operation = false := by
      rw [repLodsAfter_repeat, hc]; rfl
    refine ⟨(h.ready.repLods 64 4).ready hflag, ?_, ?_, repLodsAfter_rsi 64 4 s, ?_, ?_⟩
    · rw [repLodsAfter_rip 64 4 s h.ready.msr, hc]; rfl
    · rw [repLodsAfter_rcx, hc]
    · rw [repLodsAfter_rax]
      simp only [Nat.zero_add, Nat.sub_self, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repLods 64 4 s
  | succ m ih =>
    have hnext : nextState s = (repLodsAfter 64 4 s) :=
      nextState_of_step (h.step hstride hrex (by omega))
    have hs : rsi.read (repLodsAfter 64 4 s) = rsi.read s + BitVec.ofNat 64 8 :=
      repLodsAfter_rsi 64 4 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 64).read (repLodsAfter 64 4 s) =
          (Operand.mem a : Operand 64).read s := by
      simp only [Operand.read, repLodsAfter_external]
    have ih' := ih (repLodsAfter 64 4 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repLodsAfter 64 4 s).RIP = s.RIP := by
      rw [repLodsAfter_rip 64 4 s h.ready.msr, h.counter]
      have := h.srcLow
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.raxAfter, repLodsAfter_rax, mergeGPR_mergeGPR 64 (by decide), hs, add_ofNat_add_ofNat,
        hm, show 8 + 8 * (m + 1 - 1) = 8 * (m + 1 + 1 - 1) by omega]
    · refine ((AgreesExcept.repLods 64 4 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepLodsqA32Pre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (rsi.read s).toNat + 8 * (rcx.read s).toNat < 2^32
  srcMem : ∀ i < 8 * (rcx.read s).toNat, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome

def repLodsqA32Effect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 4
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (8 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.reg 0 : Operand 64), if rcx.read s = 0 then (Operand.reg 0 : Operand 64).read s else
      ((Operand.mem (rsi.read s + BitVec.ofNat 64 (8 * ((rcx.read s).toNat - 1))) :
        Operand 64).read s)⟩]

@[simp] theorem repLodsqA32Effect_components (p : BitVec 64) (s : RamState) :
    (repLodsqA32Effect p s).components = [.reg 6, .reg 1, .reg 0, .rip] := by
  simp [repLodsqA32Effect, Effect.components]

theorem rep_lodsq_a32_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF3, rex, 0xAD]) s) (hpre : RepLodsqA32Pre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF3, rex, 0xAD]) t ∧ (repLodsqA32Effect p s).Holds s t := by
  intro t
  have hr := hrex.rexPrefix
  have hcodeS : BytesAt s s.RIP [0x67, 0xF3, rex, 0xAD] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 4 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_lodsq_a32_step_zero s h.midRep [0x67, 0xF3, rex]
        (scanPrefix_asz_cons (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp)
        (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
        (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
        (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
        (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
        (by rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]; rfl)
        hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repZeroAfter 4 s) :=
      (AgreesExcept.repZero 4 s).of_clearRep hrep (repZeroAfter_repeat 4 s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables,
      hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, ?_, ?_⟩, trivial,
      hag.mono (by simp)⟩
    · rw [repZeroAfter_rip _ s h.ready.msr, hpre.rip]; rfl
    · rw [hag.read (by simp), hn]; simp
    · rw [hag.read (by simp), hz]
    · show (Operand.reg 0 : Operand 64).read _ = _
      rw [hag.read (by simp)]; simp [hz]
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.srcLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hnz : rcx.read s ≠ 0 := fun h0 => by simp [h0] at hn
    have hready : RepLodsqA32Loop rex s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.srcMem⟩
    have hd := rep_lodsq_a32_loop hstride hrex c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, hd.rcxZero, ?_⟩,
      trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · rw [hd.rsiAfter, hn]
    · show _ = if rcx.read s = 0 then _ else _
      simp only [hnz, ↓reduceIte]
      rw [hd.raxAfter, hn]
      exact mergeGPR_64 _ _
    · rw [repLodsqA32Effect_components]
      refine hag.mono ?_
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem rep_lodsq_a32_triple_of_bytes [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepLodsqA32Pre p) (codeRange p [0x67, 0xF3, rex, 0xAD]) (Effect.post (repLodsqA32Effect p)) :=
  fun s h hcode hpre => ⟨_, rep_lodsq_a32_steps hstride p rex hrex s h hcode hpre⟩

theorem rep_lodsq_a32_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) :
    Triple (RepLodsqA32Pre p) (codeRange p [0x67, 0xF3, 0x48, 0xAD]) (Effect.post (repLodsqA32Effect p)) :=
  rep_lodsq_a32_triple_of_bytes hstride p 0x48 (by unfold RexWPrefix; decide)

structure RepLodsdA32Loop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF3, 0xAD]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 4 * count < 2^32
  srcMem : ∀ i < 4 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome

theorem RepLodsdA32Loop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepLodsdA32Loop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodsdA32Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count : Nat} (h : RepLodsdA32Loop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repLodsAfter 32 3 s)) := by
  have := h.srcLow
  exact rep_lodsd_a32_step hstride s h.ready [0x67, 0xF3] (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    h.df h.code h.codeLow (h.rcx_ne hpos) ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
    (by omega) (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)

theorem RepLodsdA32Loop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepLodsdA32Loop s (count + 1)) : rcx.read (repLodsAfter 32 3 s) = BitVec.ofNat 64 count := by
  rw [repLodsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepLodsdA32Loop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepLodsdA32Loop s (count + 2)) : RepLodsdA32Loop (repLodsAfter 32 3 s) (count + 1) := by
  have hsl := h.srcLow
  have hrip : (repLodsAfter 32 3 s).RIP = s.RIP := by
    rw [repLodsAfter_rip 32 3 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : rsi.read (repLodsAfter 32 3 s) = rsi.read s + BitVec.ofNat 64 4 :=
    repLodsAfter_rsi 32 3 s
  have hsn : (rsi.read (repLodsAfter 32 3 s)).toNat = (rsi.read s).toNat + 4 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repLods 32 3, h.df, ?_, ?_, h.rcx_after, ?_, ?_⟩
  · intro i hi
    rw [hrip, repLodsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repLodsAfter_external]
    exact h.srcMem (4 + i) (by omega)

structure RepLodsdA32Done [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (4 * count)
  raxAfter : (Operand.reg 0 : Operand 64).read t =
    mergeGPR 32
      ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * (count - 1))) : Operand 32).read s)
      ((Operand.reg 0 : Operand 64).read s)
  agrees : AgreesExcept [.reg 0, .reg 1, .reg 6, .rip] (clearRep s) t

theorem rep_lodsd_a32_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (count : Nat) (s : RamState) (h : RepLodsdA32Loop s (count + 1)) :
    RepLodsdA32Done s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repLodsAfter 32 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repLodsAfter 32 3 s).Repeat_String_Operation = false := by
      rw [repLodsAfter_repeat, hc]; rfl
    refine ⟨(h.ready.repLods 32 3).ready hflag, ?_, ?_, repLodsAfter_rsi 32 3 s, ?_, ?_⟩
    · rw [repLodsAfter_rip 32 3 s h.ready.msr, hc]; rfl
    · rw [repLodsAfter_rcx, hc]
    · rw [repLodsAfter_rax]
      simp only [Nat.zero_add, Nat.sub_self, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repLods 32 3 s
  | succ m ih =>
    have hnext : nextState s = (repLodsAfter 32 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hs : rsi.read (repLodsAfter 32 3 s) = rsi.read s + BitVec.ofNat 64 4 :=
      repLodsAfter_rsi 32 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 32).read (repLodsAfter 32 3 s) =
          (Operand.mem a : Operand 32).read s := by
      simp only [Operand.read, repLodsAfter_external]
    have ih' := ih (repLodsAfter 32 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repLodsAfter 32 3 s).RIP = s.RIP := by
      rw [repLodsAfter_rip 32 3 s h.ready.msr, h.counter]
      have := h.srcLow
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.raxAfter, repLodsAfter_rax, mergeGPR_mergeGPR 32 (by decide), hs, add_ofNat_add_ofNat,
        hm, show 4 + 4 * (m + 1 - 1) = 4 * (m + 1 + 1 - 1) by omega]
    · refine ((AgreesExcept.repLods 32 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepLodsdA32Pre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (rsi.read s).toNat + 4 * (rcx.read s).toNat < 2^32
  srcMem : ∀ i < 4 * (rcx.read s).toNat, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome

def repLodsdA32Effect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (4 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.reg 0 : Operand 64), if rcx.read s = 0 then (Operand.reg 0 : Operand 64).read s else
      ((Operand.mem (rsi.read s + BitVec.ofNat 64 (4 * ((rcx.read s).toNat - 1))) :
        Operand 32).read s).setWidth 64⟩]

@[simp] theorem repLodsdA32Effect_components (p : BitVec 64) (s : RamState) :
    (repLodsdA32Effect p s).components = [.reg 6, .reg 1, .reg 0, .rip] := by
  simp [repLodsdA32Effect, Effect.components]

theorem rep_lodsd_a32_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF3, 0xAD]) s) (hpre : RepLodsdA32Pre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF3, 0xAD]) t ∧ (repLodsdA32Effect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0x67, 0xF3, 0xAD] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_lodsd_a32_step_zero s h.midRep [0x67, 0xF3]
        (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repZeroAfter 3 s) :=
      (AgreesExcept.repZero 3 s).of_clearRep hrep (repZeroAfter_repeat 3 s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables,
      hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, ?_, ?_⟩, trivial,
      hag.mono (by simp)⟩
    · rw [repZeroAfter_rip _ s h.ready.msr, hpre.rip]; rfl
    · rw [hag.read (by simp), hn]; simp
    · rw [hag.read (by simp), hz]
    · show (Operand.reg 0 : Operand 64).read _ = _
      rw [hag.read (by simp)]; simp [hz]
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.srcLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hnz : rcx.read s ≠ 0 := fun h0 => by simp [h0] at hn
    have hready : RepLodsdA32Loop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.srcMem⟩
    have hd := rep_lodsd_a32_loop hstride c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, hd.rcxZero, ?_⟩,
      trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · rw [hd.rsiAfter, hn]
    · show _ = if rcx.read s = 0 then _ else _
      simp only [hnz, ↓reduceIte]
      rw [hd.raxAfter, hn]
      exact mergeGPR_32 _ _
    · rw [repLodsdA32Effect_components]
      refine hag.mono ?_
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem rep_lodsd_a32_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepLodsdA32Pre p) (codeRange p [0x67, 0xF3, 0xAD]) (Effect.post (repLodsdA32Effect p)) :=
  fun s h hcode hpre => ⟨_, rep_lodsd_a32_steps hstride p s h hcode hpre⟩

structure RepLodswA32Loop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF3, 0x66, 0xAD]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 2 * count < 2^32
  srcMem : ∀ i < 2 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome

theorem RepLodswA32Loop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepLodswA32Loop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodswA32Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count : Nat} (h : RepLodswA32Loop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repLodsAfter 16 4 s)) := by
  have := h.srcLow
  exact rep_lodsw_a32_step hstride s h.ready [0x67, 0xF3, 0x66] (scanPrefix_asz_cons (by simp [scanPrefix_f3, scanPrefix_66])) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    h.df h.code h.codeLow (h.rcx_ne hpos) ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
    (by omega) (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)

theorem RepLodswA32Loop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepLodswA32Loop s (count + 1)) : rcx.read (repLodsAfter 16 4 s) = BitVec.ofNat 64 count := by
  rw [repLodsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepLodswA32Loop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepLodswA32Loop s (count + 2)) : RepLodswA32Loop (repLodsAfter 16 4 s) (count + 1) := by
  have hsl := h.srcLow
  have hrip : (repLodsAfter 16 4 s).RIP = s.RIP := by
    rw [repLodsAfter_rip 16 4 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : rsi.read (repLodsAfter 16 4 s) = rsi.read s + BitVec.ofNat 64 2 :=
    repLodsAfter_rsi 16 4 s
  have hsn : (rsi.read (repLodsAfter 16 4 s)).toNat = (rsi.read s).toNat + 2 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repLods 16 4, h.df, ?_, ?_, h.rcx_after, ?_, ?_⟩
  · intro i hi
    rw [hrip, repLodsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repLodsAfter_external]
    exact h.srcMem (2 + i) (by omega)

structure RepLodswA32Done [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 4)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (2 * count)
  raxAfter : (Operand.reg 0 : Operand 64).read t =
    mergeGPR 16
      ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * (count - 1))) : Operand 16).read s)
      ((Operand.reg 0 : Operand 64).read s)
  agrees : AgreesExcept [.reg 0, .reg 1, .reg 6, .rip] (clearRep s) t

theorem rep_lodsw_a32_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (count : Nat) (s : RamState) (h : RepLodswA32Loop s (count + 1)) :
    RepLodswA32Done s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repLodsAfter 16 4 s) :=
      nextState_of_step (h.step hstride (by omega))
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repLodsAfter 16 4 s).Repeat_String_Operation = false := by
      rw [repLodsAfter_repeat, hc]; rfl
    refine ⟨(h.ready.repLods 16 4).ready hflag, ?_, ?_, repLodsAfter_rsi 16 4 s, ?_, ?_⟩
    · rw [repLodsAfter_rip 16 4 s h.ready.msr, hc]; rfl
    · rw [repLodsAfter_rcx, hc]
    · rw [repLodsAfter_rax]
      simp only [Nat.zero_add, Nat.sub_self, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repLods 16 4 s
  | succ m ih =>
    have hnext : nextState s = (repLodsAfter 16 4 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hs : rsi.read (repLodsAfter 16 4 s) = rsi.read s + BitVec.ofNat 64 2 :=
      repLodsAfter_rsi 16 4 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 16).read (repLodsAfter 16 4 s) =
          (Operand.mem a : Operand 16).read s := by
      simp only [Operand.read, repLodsAfter_external]
    have ih' := ih (repLodsAfter 16 4 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repLodsAfter 16 4 s).RIP = s.RIP := by
      rw [repLodsAfter_rip 16 4 s h.ready.msr, h.counter]
      have := h.srcLow
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.raxAfter, repLodsAfter_rax, mergeGPR_mergeGPR 16 (by decide), hs, add_ofNat_add_ofNat,
        hm, show 2 + 2 * (m + 1 - 1) = 2 * (m + 1 + 1 - 1) by omega]
    · refine ((AgreesExcept.repLods 16 4 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepLodswA32Pre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (rsi.read s).toNat + 2 * (rcx.read s).toNat < 2^32
  srcMem : ∀ i < 2 * (rcx.read s).toNat, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome

def repLodswA32Effect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 4
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (2 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.reg 0 : Operand 64), if rcx.read s = 0 then (Operand.reg 0 : Operand 64).read s else
      mergeGPR 16 ((Operand.mem (rsi.read s + BitVec.ofNat 64 (2 * ((rcx.read s).toNat - 1))) :
        Operand 16).read s)
        ((Operand.reg 0 : Operand 64).read s)⟩]

@[simp] theorem repLodswA32Effect_components (p : BitVec 64) (s : RamState) :
    (repLodswA32Effect p s).components = [.reg 6, .reg 1, .reg 0, .rip] := by
  simp [repLodswA32Effect, Effect.components]

theorem rep_lodsw_a32_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF3, 0x66, 0xAD]) s) (hpre : RepLodswA32Pre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF3, 0x66, 0xAD]) t ∧ (repLodswA32Effect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0x67, 0xF3, 0x66, 0xAD] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 4 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_lodsw_a32_step_zero s h.midRep [0x67, 0xF3, 0x66]
        (scanPrefix_asz_cons (by simp [scanPrefix_f3, scanPrefix_66])) (by simp)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repZeroAfter 4 s) :=
      (AgreesExcept.repZero 4 s).of_clearRep hrep (repZeroAfter_repeat 4 s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables,
      hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, ?_, ?_⟩, trivial,
      hag.mono (by simp)⟩
    · rw [repZeroAfter_rip _ s h.ready.msr, hpre.rip]; rfl
    · rw [hag.read (by simp), hn]; simp
    · rw [hag.read (by simp), hz]
    · show (Operand.reg 0 : Operand 64).read _ = _
      rw [hag.read (by simp)]; simp [hz]
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.srcLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hnz : rcx.read s ≠ 0 := fun h0 => by simp [h0] at hn
    have hready : RepLodswA32Loop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.srcMem⟩
    have hd := rep_lodsw_a32_loop hstride c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, hd.rcxZero, ?_⟩,
      trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · rw [hd.rsiAfter, hn]
    · show _ = if rcx.read s = 0 then _ else _
      simp only [hnz, ↓reduceIte]
      rw [hd.raxAfter, hn]
    · rw [repLodswA32Effect_components]
      refine hag.mono ?_
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem rep_lodsw_a32_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepLodswA32Pre p) (codeRange p [0x67, 0xF3, 0x66, 0xAD]) (Effect.post (repLodswA32Effect p)) :=
  fun s h hcode hpre => ⟨_, rep_lodsw_a32_steps hstride p s h hcode hpre⟩

structure RepLodsbA32Loop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0x67, 0xF3, 0xAC]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 1 * count < 2^32
  srcMem : ∀ i < 1 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome

theorem RepLodsbA32Loop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepLodsbA32Loop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodsbA32Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count : Nat} (h : RepLodsbA32Loop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repLodsAfter 8 3 s)) := by
  have := h.srcLow
  exact rep_lodsb_a32_step hstride s h.ready [0x67, 0xF3] (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    h.df h.code h.codeLow (h.rcx_ne hpos) ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
    (by omega) (by rw [h.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)

theorem RepLodsbA32Loop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepLodsbA32Loop s (count + 1)) : rcx.read (repLodsAfter 8 3 s) = BitVec.ofNat 64 count := by
  rw [repLodsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepLodsbA32Loop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepLodsbA32Loop s (count + 2)) : RepLodsbA32Loop (repLodsAfter 8 3 s) (count + 1) := by
  have hsl := h.srcLow
  have hrip : (repLodsAfter 8 3 s).RIP = s.RIP := by
    rw [repLodsAfter_rip 8 3 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : rsi.read (repLodsAfter 8 3 s) = rsi.read s + BitVec.ofNat 64 1 :=
    repLodsAfter_rsi 8 3 s
  have hsn : (rsi.read (repLodsAfter 8 3 s)).toNat = (rsi.read s).toNat + 1 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.ready.repLods 8 3, h.df, ?_, ?_, h.rcx_after, ?_, ?_⟩
  · intro i hi
    rw [hrip, repLodsAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, repLodsAfter_external]
    exact h.srcMem (1 + i) (by omega)

structure RepLodsbA32Done [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (1 * count)
  raxAfter : (Operand.reg 0 : Operand 64).read t =
    mergeGPR 8
      ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * (count - 1))) : Operand 8).read s)
      ((Operand.reg 0 : Operand 64).read s)
  agrees : AgreesExcept [.reg 0, .reg 1, .reg 6, .rip] (clearRep s) t

theorem rep_lodsb_a32_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (count : Nat) (s : RamState) (h : RepLodsbA32Loop s (count + 1)) :
    RepLodsbA32Done s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repLodsAfter 8 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repLodsAfter 8 3 s).Repeat_String_Operation = false := by
      rw [repLodsAfter_repeat, hc]; rfl
    refine ⟨(h.ready.repLods 8 3).ready hflag, ?_, ?_, repLodsAfter_rsi 8 3 s, ?_, ?_⟩
    · rw [repLodsAfter_rip 8 3 s h.ready.msr, hc]; rfl
    · rw [repLodsAfter_rcx, hc]
    · rw [repLodsAfter_rax]
      simp only [Nat.zero_add, Nat.sub_self, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repLods 8 3 s
  | succ m ih =>
    have hnext : nextState s = (repLodsAfter 8 3 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hs : rsi.read (repLodsAfter 8 3 s) = rsi.read s + BitVec.ofNat 64 1 :=
      repLodsAfter_rsi 8 3 s
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 8).read (repLodsAfter 8 3 s) =
          (Operand.mem a : Operand 8).read s := by
      simp only [Operand.read, repLodsAfter_external]
    have ih' := ih (repLodsAfter 8 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repLodsAfter 8 3 s).RIP = s.RIP := by
      rw [repLodsAfter_rip 8 3 s h.ready.msr, h.counter]
      have := h.srcLow
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.raxAfter, repLodsAfter_rax, mergeGPR_mergeGPR 8 (by decide), hs, add_ofNat_add_ofNat,
        hm, show 1 + 1 * (m + 1 - 1) = 1 * (m + 1 + 1 - 1) by omega]
    · refine ((AgreesExcept.repLods 8 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepLodsbA32Pre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (rsi.read s).toNat + 1 * (rcx.read s).toNat < 2^32
  srcMem : ∀ i < 1 * (rcx.read s).toNat, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome

def repLodsbA32Effect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (1 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.reg 0 : Operand 64), if rcx.read s = 0 then (Operand.reg 0 : Operand 64).read s else
      mergeGPR 8 ((Operand.mem (rsi.read s + BitVec.ofNat 64 (1 * ((rcx.read s).toNat - 1))) :
        Operand 8).read s)
        ((Operand.reg 0 : Operand 64).read s)⟩]

@[simp] theorem repLodsbA32Effect_components (p : BitVec 64) (s : RamState) :
    (repLodsbA32Effect p s).components = [.reg 6, .reg 1, .reg 0, .rip] := by
  simp [repLodsbA32Effect, Effect.components]

theorem rep_lodsb_a32_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0x67, 0xF3, 0xAC]) s) (hpre : RepLodsbA32Pre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0x67, 0xF3, 0xAC]) t ∧ (repLodsbA32Effect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0x67, 0xF3, 0xAC] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_lodsb_a32_step_zero s h.midRep [0x67, 0xF3]
        (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        (by rw [scanContext_asz_cons]; rfl)
        hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repZeroAfter 3 s) :=
      (AgreesExcept.repZero 3 s).of_clearRep hrep (repZeroAfter_repeat 3 s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables,
      hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, ?_, ?_⟩, trivial,
      hag.mono (by simp)⟩
    · rw [repZeroAfter_rip _ s h.ready.msr, hpre.rip]; rfl
    · rw [hag.read (by simp), hn]; simp
    · rw [hag.read (by simp), hz]
    · show (Operand.reg 0 : Operand 64).read _ = _
      rw [hag.read (by simp)]; simp [hz]
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.srcLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hnz : rcx.read s ≠ 0 := fun h0 => by simp [h0] at hn
    have hready : RepLodsbA32Loop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.srcMem⟩
    have hd := rep_lodsb_a32_loop hstride c' s hready
    have ht : t = nextStates (c' + 1) s := by
      simp only [t, hn, show max (c' + 1) 1 = c' + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, hag.codeIn (by simp [Component.Covers]) hcode, ?_, ⟨?_, hd.rcxZero, ?_⟩,
      trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · rw [hd.rsiAfter, hn]
    · show _ = if rcx.read s = 0 then _ else _
      simp only [hnz, ↓reduceIte]
      rw [hd.raxAfter, hn]
    · rw [repLodsbA32Effect_components]
      refine hag.mono ?_
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem rep_lodsb_a32_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepLodsbA32Pre p) (codeRange p [0x67, 0xF3, 0xAC]) (Effect.post (repLodsbA32Effect p)) :=
  fun s h hcode hpre => ⟨_, rep_lodsb_a32_steps hstride p s h hcode hpre⟩

attribute [x86_compose] repLodsqEffect repLodsqSegEffect repLodsdEffect repLodsdSegEffect repLodswEffect repLodswSegEffect repLodsbEffect repLodsbSegEffect repLodsqA32Effect repLodsdA32Effect repLodswA32Effect repLodsbA32Effect

@[x86_local] theorem repLodsqEffect_local {p : BitVec 64} : Effect.Local (repLodsqEffect p) := by
  effect_local [repLodsqEffect]

@[x86_local] theorem repLodsqSegEffect_local {p base : BitVec 64} :
    Effect.Local (repLodsqSegEffect p base) := by
  effect_local [repLodsqSegEffect]

@[x86_local] theorem repLodsdEffect_local {p : BitVec 64} : Effect.Local (repLodsdEffect p) := by
  effect_local [repLodsdEffect]

@[x86_local] theorem repLodsdSegEffect_local {p base : BitVec 64} :
    Effect.Local (repLodsdSegEffect p base) := by
  effect_local [repLodsdSegEffect]

@[x86_local] theorem repLodswEffect_local {p : BitVec 64} : Effect.Local (repLodswEffect p) := by
  effect_local [repLodswEffect]

@[x86_local] theorem repLodswSegEffect_local {p base : BitVec 64} :
    Effect.Local (repLodswSegEffect p base) := by
  effect_local [repLodswSegEffect]

@[x86_local] theorem repLodsbEffect_local {p : BitVec 64} : Effect.Local (repLodsbEffect p) := by
  effect_local [repLodsbEffect]

@[x86_local] theorem repLodsbSegEffect_local {p base : BitVec 64} :
    Effect.Local (repLodsbSegEffect p base) := by
  effect_local [repLodsbSegEffect]

@[x86_local] theorem repLodsqA32Effect_local {p : BitVec 64} : Effect.Local (repLodsqA32Effect p) := by
  effect_local [repLodsqA32Effect]

@[x86_local] theorem repLodsdA32Effect_local {p : BitVec 64} : Effect.Local (repLodsdA32Effect p) := by
  effect_local [repLodsdA32Effect]

@[x86_local] theorem repLodswA32Effect_local {p : BitVec 64} : Effect.Local (repLodswA32Effect p) := by
  effect_local [repLodswA32Effect]

@[x86_local] theorem repLodsbA32Effect_local {p : BitVec 64} : Effect.Local (repLodsbA32Effect p) := by
  effect_local [repLodsbA32Effect]

end X86Proofs
