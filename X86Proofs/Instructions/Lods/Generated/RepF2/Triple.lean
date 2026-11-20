
import X86Proofs.Instructions.Lods.Generated.RepF2.Step
import X86Proofs.Instructions.Lods.Generated.Rep.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

structure RepLodsqF2Loop [Bindings] (rex : UInt8) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF2, rex, 0xAD]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 8 * count ≤ 2^32
  srcMem : ∀ i < 8 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome

theorem RepLodsqF2Loop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepLodsqF2Loop rex s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodsqF2Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState} {count : Nat} (h : RepLodsqF2Loop rex s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repLodsAfter 64 3 s)) := by
  have hr := hrex.rexPrefix
  have := h.srcLow
  exact rep_lodsq_f2_step hstride s h.ready [0xF2, rex] (by simp [scanPrefix_f2, hr.scanPrefix]) (by simp)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    (by rw [scanContext_f2_rex _ _ hr]; rfl)
    h.df h.code h.codeLow (h.rcx_ne hpos) ⟨by omega, fun i hi => h.srcMem i (by omega)⟩

theorem RepLodsqF2Loop.rcx_after [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepLodsqF2Loop rex s (count + 1)) : rcx.read (repLodsAfter 64 3 s) = BitVec.ofNat 64 count := by
  rw [repLodsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepLodsqF2Loop.next [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepLodsqF2Loop rex s (count + 2)) : RepLodsqF2Loop rex (repLodsAfter 64 3 s) (count + 1) := by
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

theorem rep_lodsq_f2_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (count : Nat) (s : RamState) (h : RepLodsqF2Loop rex s (count + 1)) :
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

theorem rep_lodsq_f2_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, rex, 0xAD]) s) (hpre : RepLodsqPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, rex, 0xAD]) t ∧ (repLodsqEffect p s).Holds s t := by
  intro t
  have hr := hrex.rexPrefix
  have hcodeS : BytesAt s s.RIP [0xF2, rex, 0xAD] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_lodsq_f2_step_zero s h.midRep [0xF2, rex]
        (by simp [scanPrefix_f2, hr.scanPrefix]) (by simp)
        (by rw [scanContext_f2_rex _ _ hr]; rfl)
        (by rw [scanContext_f2_rex _ _ hr]; exact hrex.rex_w s.DS)
        (by rw [scanContext_f2_rex _ _ hr]; rfl)
        (by rw [scanContext_f2_rex _ _ hr]; rfl)
        (by rw [scanContext_f2_rex _ _ hr]; rfl)
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
    have hready : RepLodsqF2Loop rex s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.srcMem⟩
    have hd := rep_lodsq_f2_loop hstride hrex c' s hready
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

theorem rep_lodsq_f2_triple_of_bytes [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepLodsqPre p) (codeRange p [0xF2, rex, 0xAD]) (Effect.post (repLodsqEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_lodsq_f2_steps hstride p rex hrex s h hcode hpre⟩

theorem rep_lodsq_f2_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) :
    Triple (RepLodsqPre p) (codeRange p [0xF2, 0x48, 0xAD]) (Effect.post (repLodsqEffect p)) :=
  rep_lodsq_f2_triple_of_bytes hstride p 0x48 (by unfold RexWPrefix; decide)

structure RepLodsqF2SegLoop [Bindings] (r : SegReg) (base : BitVec 64) (rex : UInt8) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF2, rex, 0xAD]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (base + rsi.read s).toNat + 8 * count ≤ 2^32
  srcMem : ∀ i < 8 * count, (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  seg : r.Ready base s

theorem RepLodsqF2SegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepLodsqF2SegLoop r base rex s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodsqF2SegLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {r : SegReg} {base : BitVec 64} {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState} {count : Nat} (h : RepLodsqF2SegLoop r base rex s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repLodsSegAfter base 64 4 s)) := by
  have hr := hrex.rexPrefix
  have := h.srcLow
  have hsrc : MemReadable s (base + rsi.read s) 8 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2, rex] =
      withSeg (repneRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF2, rex] (noSegPrefix_cons noSegPrefix_f2 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_f2_rex _ _ hr]
  have hstep := rep_lodsq_f2_seg_step hstride s h.ready [r.prefixByte, 0xF2, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_f2, hr.scanPrefix])) (by simp)
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

theorem RepLodsqF2SegLoop.rcx_after [Bindings] {r : SegReg} {base : BitVec 64} {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepLodsqF2SegLoop r base rex s (count + 1)) : rcx.read (repLodsSegAfter base 64 4 s) = BitVec.ofNat 64 count := by
  rw [repLodsSegAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepLodsqF2SegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {rex : UInt8} {s : RamState} {count : Nat}
    (h : RepLodsqF2SegLoop r base rex s (count + 2)) : RepLodsqF2SegLoop r base rex (repLodsSegAfter base 64 4 s) (count + 1) := by
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

theorem rep_lodsq_f2_seg_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {r : SegReg} {base : BitVec 64} {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (count : Nat) (s : RamState) (h : RepLodsqF2SegLoop r base rex s (count + 1)) :
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

theorem rep_lodsq_f2_seg_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF2, rex, 0xAD]) s) (hpre : RepLodsqSegPre p r base s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF2, rex, 0xAD]) t ∧ (repLodsqSegEffect p base s).Holds s t := by
  intro t
  have hr := hrex.rexPrefix
  have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF2, rex, 0xAD] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  have hrep := h.ready.repeatClear
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2, rex] =
      withSeg (repneRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF2, rex] (noSegPrefix_cons noSegPrefix_f2 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_f2_rex _ _ hr]
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 4 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_lodsq_f2_step_zero s h.midRep [r.prefixByte, 0xF2, rex]
        (scanPrefix_seg_cons r (by simp [scanPrefix_f2, hr.scanPrefix])) (by simp)
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
    have hready : RepLodsqF2SegLoop r base rex s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.srcMem, hpre.seg⟩
    have hd := rep_lodsq_f2_seg_loop hstride hrex c' s hready
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

theorem rep_lodsq_f2_seg_triple_of_bytes [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepLodsqSegPre p r base) (codeRange p [r.prefixByte, 0xF2, rex, 0xAD]) (Effect.post (repLodsqSegEffect p base)) :=
  fun s h hcode hpre => ⟨_, rep_lodsq_f2_seg_steps hstride p r base rex hrex s h hcode hpre⟩

theorem rep_lodsq_f2_seg_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (RepLodsqSegPre p r base) (codeRange p [r.prefixByte, 0xF2, 0x48, 0xAD]) (Effect.post (repLodsqSegEffect p base)) :=
  rep_lodsq_f2_seg_triple_of_bytes hstride p r base 0x48 (by unfold RexWPrefix; decide)

structure RepLodsdF2Loop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF2, 0xAD]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 4 * count ≤ 2^32
  srcMem : ∀ i < 4 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome

theorem RepLodsdF2Loop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepLodsdF2Loop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodsdF2Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count : Nat} (h : RepLodsdF2Loop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repLodsAfter 32 2 s)) := by
  have := h.srcLow
  exact rep_lodsd_f2_step hstride s h.ready [0xF2] (by simpa using scanPrefix_f2) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne hpos) ⟨by omega, fun i hi => h.srcMem i (by omega)⟩

theorem RepLodsdF2Loop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepLodsdF2Loop s (count + 1)) : rcx.read (repLodsAfter 32 2 s) = BitVec.ofNat 64 count := by
  rw [repLodsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepLodsdF2Loop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepLodsdF2Loop s (count + 2)) : RepLodsdF2Loop (repLodsAfter 32 2 s) (count + 1) := by
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

theorem rep_lodsd_f2_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (count : Nat) (s : RamState) (h : RepLodsdF2Loop s (count + 1)) :
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

theorem rep_lodsd_f2_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, 0xAD]) s) (hpre : RepLodsdPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, 0xAD]) t ∧ (repLodsdEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF2, 0xAD] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 2 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_lodsd_f2_step_zero s h.midRep [0xF2]
        (by simpa using scanPrefix_f2) (by simp)
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
    have hready : RepLodsdF2Loop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.srcMem⟩
    have hd := rep_lodsd_f2_loop hstride c' s hready
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

theorem rep_lodsd_f2_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepLodsdPre p) (codeRange p [0xF2, 0xAD]) (Effect.post (repLodsdEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_lodsd_f2_steps hstride p s h hcode hpre⟩

structure RepLodsdF2SegLoop [Bindings] (r : SegReg) (base : BitVec 64) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF2, 0xAD]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (base + rsi.read s).toNat + 4 * count ≤ 2^32
  srcMem : ∀ i < 4 * count, (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  seg : r.Ready base s

theorem RepLodsdF2SegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepLodsdF2SegLoop r base s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodsdF2SegLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat} (h : RepLodsdF2SegLoop r base s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repLodsSegAfter base 32 3 s)) := by
  have := h.srcLow
  have hsrc : MemReadable s (base + rsi.read s) 4 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF2]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF2] (noSegPrefix_cons noSegPrefix_f2 noSegPrefix_nil)]
  have hstep := rep_lodsd_f2_seg_step hstride s h.ready [r.prefixByte, 0xF2] (scanPrefix_seg_cons r (by simpa using scanPrefix_f2)) (by simp)
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

theorem RepLodsdF2SegLoop.rcx_after [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepLodsdF2SegLoop r base s (count + 1)) : rcx.read (repLodsSegAfter base 32 3 s) = BitVec.ofNat 64 count := by
  rw [repLodsSegAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepLodsdF2SegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepLodsdF2SegLoop r base s (count + 2)) : RepLodsdF2SegLoop r base (repLodsSegAfter base 32 3 s) (count + 1) := by
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

theorem rep_lodsd_f2_seg_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {r : SegReg} {base : BitVec 64} (count : Nat) (s : RamState) (h : RepLodsdF2SegLoop r base s (count + 1)) :
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

theorem rep_lodsd_f2_seg_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF2, 0xAD]) s) (hpre : RepLodsdSegPre p r base s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF2, 0xAD]) t ∧ (repLodsdSegEffect p base s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF2, 0xAD] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  have hrep := h.ready.repeatClear
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF2]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF2] (noSegPrefix_cons noSegPrefix_f2 noSegPrefix_nil)]
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_lodsd_f2_step_zero s h.midRep [r.prefixByte, 0xF2]
        (scanPrefix_seg_cons r (by simpa using scanPrefix_f2)) (by simp)
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
    have hready : RepLodsdF2SegLoop r base s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.srcMem, hpre.seg⟩
    have hd := rep_lodsd_f2_seg_loop hstride c' s hready
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

theorem rep_lodsd_f2_seg_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (RepLodsdSegPre p r base) (codeRange p [r.prefixByte, 0xF2, 0xAD]) (Effect.post (repLodsdSegEffect p base)) :=
  fun s h hcode hpre => ⟨_, rep_lodsd_f2_seg_steps hstride p r base s h hcode hpre⟩

structure RepLodswF2Loop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF2, 0x66, 0xAD]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 2 * count ≤ 2^32
  srcMem : ∀ i < 2 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome

theorem RepLodswF2Loop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepLodswF2Loop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodswF2Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count : Nat} (h : RepLodswF2Loop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repLodsAfter 16 3 s)) := by
  have := h.srcLow
  exact rep_lodsw_f2_step hstride s h.ready [0xF2, 0x66] (by simp [scanPrefix_f2, scanPrefix_66]) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne hpos) ⟨by omega, fun i hi => h.srcMem i (by omega)⟩

theorem RepLodswF2Loop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepLodswF2Loop s (count + 1)) : rcx.read (repLodsAfter 16 3 s) = BitVec.ofNat 64 count := by
  rw [repLodsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepLodswF2Loop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepLodswF2Loop s (count + 2)) : RepLodswF2Loop (repLodsAfter 16 3 s) (count + 1) := by
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

theorem rep_lodsw_f2_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (count : Nat) (s : RamState) (h : RepLodswF2Loop s (count + 1)) :
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

theorem rep_lodsw_f2_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, 0x66, 0xAD]) s) (hpre : RepLodswPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, 0x66, 0xAD]) t ∧ (repLodswEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF2, 0x66, 0xAD] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_lodsw_f2_step_zero s h.midRep [0xF2, 0x66]
        (by simp [scanPrefix_f2, scanPrefix_66]) (by simp)
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
    have hready : RepLodswF2Loop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.srcMem⟩
    have hd := rep_lodsw_f2_loop hstride c' s hready
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

theorem rep_lodsw_f2_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepLodswPre p) (codeRange p [0xF2, 0x66, 0xAD]) (Effect.post (repLodswEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_lodsw_f2_steps hstride p s h hcode hpre⟩

structure RepLodswF2SegLoop [Bindings] (r : SegReg) (base : BitVec 64) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF2, 0x66, 0xAD]
  codeLow : s.RIP.toNat + 4 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (base + rsi.read s).toNat + 2 * count ≤ 2^32
  srcMem : ∀ i < 2 * count, (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  seg : r.Ready base s

theorem RepLodswF2SegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepLodswF2SegLoop r base s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodswF2SegLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat} (h : RepLodswF2SegLoop r base s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repLodsSegAfter base 16 4 s)) := by
  have := h.srcLow
  have hsrc : MemReadable s (base + rsi.read s) 2 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF2, 0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF2, 0x66] (noSegPrefix_cons noSegPrefix_f2 (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil))]
  have hstep := rep_lodsw_f2_seg_step hstride s h.ready [r.prefixByte, 0xF2, 0x66] (scanPrefix_seg_cons r (by simp [scanPrefix_f2, scanPrefix_66])) (by simp)
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

theorem RepLodswF2SegLoop.rcx_after [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepLodswF2SegLoop r base s (count + 1)) : rcx.read (repLodsSegAfter base 16 4 s) = BitVec.ofNat 64 count := by
  rw [repLodsSegAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepLodswF2SegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepLodswF2SegLoop r base s (count + 2)) : RepLodswF2SegLoop r base (repLodsSegAfter base 16 4 s) (count + 1) := by
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

theorem rep_lodsw_f2_seg_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {r : SegReg} {base : BitVec 64} (count : Nat) (s : RamState) (h : RepLodswF2SegLoop r base s (count + 1)) :
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

theorem rep_lodsw_f2_seg_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF2, 0x66, 0xAD]) s) (hpre : RepLodswSegPre p r base s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF2, 0x66, 0xAD]) t ∧ (repLodswSegEffect p base s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF2, 0x66, 0xAD] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  have hrep := h.ready.repeatClear
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF2, 0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF2, 0x66] (noSegPrefix_cons noSegPrefix_f2 (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil))]
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 4 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_lodsw_f2_step_zero s h.midRep [r.prefixByte, 0xF2, 0x66]
        (scanPrefix_seg_cons r (by simp [scanPrefix_f2, scanPrefix_66])) (by simp)
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
    have hready : RepLodswF2SegLoop r base s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.srcMem, hpre.seg⟩
    have hd := rep_lodsw_f2_seg_loop hstride c' s hready
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

theorem rep_lodsw_f2_seg_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (RepLodswSegPre p r base) (codeRange p [r.prefixByte, 0xF2, 0x66, 0xAD]) (Effect.post (repLodswSegEffect p base)) :=
  fun s h hcode hpre => ⟨_, rep_lodsw_f2_seg_steps hstride p r base s h hcode hpre⟩

structure RepLodsbF2Loop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF2, 0xAC]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 1 * count ≤ 2^32
  srcMem : ∀ i < 1 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome

theorem RepLodsbF2Loop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : RepLodsbF2Loop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodsbF2Loop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count : Nat} (h : RepLodsbF2Loop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repLodsAfter 8 2 s)) := by
  have := h.srcLow
  exact rep_lodsb_f2_step hstride s h.ready [0xF2] (by simpa using scanPrefix_f2) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne hpos) ⟨by omega, fun i hi => h.srcMem i (by omega)⟩

theorem RepLodsbF2Loop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : RepLodsbF2Loop s (count + 1)) : rcx.read (repLodsAfter 8 2 s) = BitVec.ofNat 64 count := by
  rw [repLodsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepLodsbF2Loop.next [Bindings] {s : RamState} {count : Nat}
    (h : RepLodsbF2Loop s (count + 2)) : RepLodsbF2Loop (repLodsAfter 8 2 s) (count + 1) := by
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

theorem rep_lodsb_f2_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (count : Nat) (s : RamState) (h : RepLodsbF2Loop s (count + 1)) :
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

theorem rep_lodsb_f2_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF2, 0xAC]) s) (hpre : RepLodsbPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF2, 0xAC]) t ∧ (repLodsbEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF2, 0xAC] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 2 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_lodsb_f2_step_zero s h.midRep [0xF2]
        (by simpa using scanPrefix_f2) (by simp)
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
    have hready : RepLodsbF2Loop s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.srcMem⟩
    have hd := rep_lodsb_f2_loop hstride c' s hready
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

theorem rep_lodsb_f2_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepLodsbPre p) (codeRange p [0xF2, 0xAC]) (Effect.post (repLodsbEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_lodsb_f2_steps hstride p s h hcode hpre⟩

structure RepLodsbF2SegLoop [Bindings] (r : SegReg) (base : BitVec 64) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [r.prefixByte, 0xF2, 0xAC]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (base + rsi.read s).toNat + 1 * count ≤ 2^32
  srcMem : ∀ i < 1 * count, (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome
  seg : r.Ready base s

theorem RepLodsbF2SegLoop.rcx_ne [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepLodsbF2SegLoop r base s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodsbF2SegLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat} (h : RepLodsbF2SegLoop r base s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repLodsSegAfter base 8 3 s)) := by
  have := h.srcLow
  have hsrc : MemReadable s (base + rsi.read s) 1 :=
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
  obtain ⟨hseg, hbase⟩ := h.seg
  subst hbase
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF2]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF2] (noSegPrefix_cons noSegPrefix_f2 noSegPrefix_nil)]
  have hstep := rep_lodsb_f2_seg_step hstride s h.ready [r.prefixByte, 0xF2] (scanPrefix_seg_cons r (by simpa using scanPrefix_f2)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    h.df h.code h.codeLow (h.rcx_ne hpos) (by rw [hsc]; exact hsrc)
  rw [hsc] at hstep
  exact hstep

theorem RepLodsbF2SegLoop.rcx_after [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepLodsbF2SegLoop r base s (count + 1)) : rcx.read (repLodsSegAfter base 8 3 s) = BitVec.ofNat 64 count := by
  rw [repLodsSegAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem RepLodsbF2SegLoop.next [Bindings] {r : SegReg} {base : BitVec 64} {s : RamState} {count : Nat}
    (h : RepLodsbF2SegLoop r base s (count + 2)) : RepLodsbF2SegLoop r base (repLodsSegAfter base 8 3 s) (count + 1) := by
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

theorem rep_lodsb_f2_seg_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {r : SegReg} {base : BitVec 64} (count : Nat) (s : RamState) (h : RepLodsbF2SegLoop r base s (count + 1)) :
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

theorem rep_lodsb_f2_seg_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (r : SegReg) (base : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [r.prefixByte, 0xF2, 0xAC]) s) (hpre : RepLodsbSegPre p r base s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [r.prefixByte, 0xF2, 0xAC]) t ∧ (repLodsbSegEffect p base s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [r.prefixByte, 0xF2, 0xAC] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  have hrep := h.ready.repeatClear
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF2] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF2]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF2] (noSegPrefix_cons noSegPrefix_f2 noSegPrefix_nil)]
  rcases hn : (rcx.read s).toNat with _ | c'
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repZeroAfter 3 s := by
      simp only [t, hn]
      exact nextState_of_step (rep_lodsb_f2_step_zero s h.midRep [r.prefixByte, 0xF2]
        (scanPrefix_seg_cons r (by simpa using scanPrefix_f2)) (by simp)
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
    have hready : RepLodsbF2SegLoop r base s (c' + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.srcMem, hpre.seg⟩
    have hd := rep_lodsb_f2_seg_loop hstride c' s hready
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

theorem rep_lodsb_f2_seg_triple [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (RepLodsbSegPre p r base) (codeRange p [r.prefixByte, 0xF2, 0xAC]) (Effect.post (repLodsbSegEffect p base)) :=
  fun s h hcode hpre => ⟨_, rep_lodsb_f2_seg_steps hstride p r base s h hcode hpre⟩

end X86Proofs
