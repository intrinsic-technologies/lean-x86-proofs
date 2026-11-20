
import X86Proofs.Instructions.Lods.Generated.RepDown.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

structure RepLodsqDownLoop [Bindings] (rex : UInt8) (s : RamState) (slo : Nat) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF3, rex, 0xAD]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcTop : (rsi.read s).toNat + 8 = slo + 8 * count
  srcLow : slo + 8 * count ≤ 2^32
  srcMem : ∀ i < 8 * count, (s.external[BitVec.ofNat 64 slo + BitVec.ofNat 64 i]?).isSome

theorem RepLodsqDownLoop.rcx_ne [Bindings] {rex : UInt8} {s : RamState} {slo count : Nat}
    (h : RepLodsqDownLoop rex s slo count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodsqDownLoop.stop [Bindings] {rex : UInt8} {s : RamState} {slo count : Nat}
    (h : RepLodsqDownLoop rex s slo (count + 1)) (i : Nat) :
    BitVec.ofNat 64 slo + BitVec.ofNat 64 (8 * count + i) = rsi.read s + BitVec.ofNat 64 i :=
  ofNat_add_ofNat_eq (by have := h.srcTop; omega) i

theorem RepLodsqDownLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {s : RamState} {slo count : Nat}
    (h : RepLodsqDownLoop rex s slo (count + 1)) :
    X86.Machine.step s = some (.next (repLodsDownAfter 64 3 s)) := by
  have hr := hrex.rexPrefix
  have := h.srcLow
  have := h.srcTop
  exact rep_lodsq_down_step hstride s h.ready [0xF3, rex] (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl)
    h.df h.code h.codeLow (h.rcx_ne (by omega))
    ⟨by omega, fun i hi => h.stop i ▸ h.srcMem (8 * count + i) (by omega)⟩

theorem RepLodsqDownLoop.next [Bindings] {rex : UInt8} {s : RamState} {slo count : Nat}
    (h : RepLodsqDownLoop rex s slo (count + 2)) : RepLodsqDownLoop rex (repLodsDownAfter 64 3 s) slo (count + 1) := by
  have hsl := h.srcLow
  have hstop := h.srcTop
  have hrip : (repLodsDownAfter 64 3 s).RIP = s.RIP := by
    rw [repLodsDownAfter_rip 64 3 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hsn : (rsi.read (repLodsDownAfter 64 3 s)).toNat = (rsi.read s).toNat - 8 := by
    rw [repLodsDownAfter_rsi, toNat_sub_ofNat _ _ (by omega)]
  refine ⟨h.ready.repLodsDown 64 3, h.df, ?_, ?_,
    by rw [repLodsDownAfter_rcx, h.counter, ofNat_succ_sub_one], ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repLodsDownAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · omega
  · intro i hi
    rw [repLodsDownAfter_external]
    exact h.srcMem i (by omega)

structure RepLodsqDownDone [Bindings] (s t : RamState) (slo count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s - BitVec.ofNat 64 (8 * count)
  raxAfter : (Operand.reg 0 : Operand 64).read t =
    mergeGPR 64 ((Operand.mem (BitVec.ofNat 64 slo) : Operand 64).read s)
      ((Operand.reg 0 : Operand 64).read s)
  agrees : AgreesExcept [.reg 0, .reg 1, .reg 6, .rip] (clearRep s) t

theorem rep_lodsq_down_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (count : Nat) (s : RamState) (slo : Nat)
    (h : RepLodsqDownLoop rex s slo (count + 1)) :
    RepLodsqDownDone s (nextStates (count + 1) s) slo (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repLodsDownAfter 64 3 s) :=
      nextState_of_step (h.step hstride hrex )
    have hsl := h.srcLow
    have hstop := h.srcTop
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repLodsDownAfter 64 3 s).Repeat_String_Operation = false := by
      rw [repLodsDownAfter_repeat, hc]; rfl
    have hslo : rsi.read s = BitVec.ofNat 64 slo := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
    refine ⟨(h.ready.repLodsDown 64 3).ready hflag, ?_, ?_, repLodsDownAfter_rsi 64 3 s, ?_, ?_⟩
    · rw [repLodsDownAfter_rip 64 3 s h.ready.msr, hc]; rfl
    · rw [repLodsDownAfter_rcx, hc]
    · rw [repLodsDownAfter_rax, hslo]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repLodsDown 64 3 s
  | succ m ih =>
    have hnext : nextState s = (repLodsDownAfter 64 3 s) :=
      nextState_of_step (h.step hstride hrex )
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 64).read (repLodsDownAfter 64 3 s) =
          (Operand.mem a : Operand 64).read s := by
      simp only [Operand.read, repLodsDownAfter_external]
    have ih' := ih (repLodsDownAfter 64 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repLodsDownAfter 64 3 s).RIP = s.RIP := by
      rw [repLodsDownAfter_rip 64 3 s h.ready.msr, h.counter]
      have := h.srcLow
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, repLodsDownAfter_rsi, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.raxAfter, repLodsDownAfter_rax, mergeGPR_mergeGPR 64 (by decide), hm]
    · refine ((AgreesExcept.repLodsDown 64 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepLodsqDownPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  srcBase : 8 * (rcx.read s).toNat ≤ (rsi.read s).toNat + 8
  srcLow : (rsi.read s).toNat + 8 ≤ 2^32
  srcMem : ∀ i < 8 * (rcx.read s).toNat,
    (s.external[downBase rsi 8 s + BitVec.ofNat 64 i]?).isSome

def repLodsqDownEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s - BitVec.ofNat 64 (8 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.reg 0 : Operand 64), if rcx.read s = 0 then (Operand.reg 0 : Operand 64).read s else
      ((Operand.mem (downBase rsi 8 s) : Operand 64).read s)⟩]

@[simp] theorem repLodsqDownEffect_components (p : BitVec 64) (s : RamState) :
    (repLodsqDownEffect p s).components = [.reg 6, .reg 1, .reg 0, .rip] := by
  simp [repLodsqDownEffect, Effect.components]

theorem rep_lodsq_down_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, rex, 0xAD]) s) (hpre : RepLodsqDownPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, rex, 0xAD]) t ∧ (repLodsqDownEffect p s).Holds s t := by
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
    · rw [hag.read (by simp), hn, Nat.mul_zero]
      exact (BitVec.sub_zero _).symm
    · rw [hag.read (by simp), hz]
    · show (Operand.reg 0 : Operand 64).read _ = _
      rw [hag.read (by simp)]; simp [hz]
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.srcLow
      have := hpre.srcBase
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hnz : rcx.read s ≠ 0 := fun h0 => by simp [h0] at hn
    have hsb : downBase rsi 8 s =
        BitVec.ofNat 64 ((rsi.read s).toNat + 8 - 8 * (c' + 1)) := by
      rw [downBase, hn]
    have hready : RepLodsqDownLoop rex s ((rsi.read s).toNat + 8 - 8 * (c' + 1)) (c' + 1) := by
      have := hpre.srcBase
      have := hpre.srcLow
      exact ⟨h.midRep, hpre.df, hcodeS, hlow, hc, by omega, by omega,
        fun i hi => hsb ▸ hpre.srcMem i (by omega)⟩
    have hd := rep_lodsq_down_loop hstride hrex c' s _ hready
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
      rw [hd.raxAfter, hsb]
      exact mergeGPR_64 _ _
    · rw [repLodsqDownEffect_components]
      refine hag.mono ?_
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem rep_lodsq_down_triple_of_bytes [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    Triple (RepLodsqDownPre p) (codeRange p [0xF3, rex, 0xAD]) (Effect.post (repLodsqDownEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_lodsq_down_steps hstride p rex hrex s h hcode hpre⟩

theorem rep_lodsq_down_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (p : BitVec 64) :
    Triple (RepLodsqDownPre p) (codeRange p [0xF3, 0x48, 0xAD]) (Effect.post (repLodsqDownEffect p)) :=
  rep_lodsq_down_triple_of_bytes hstride p 0x48 (by unfold RexWPrefix; decide)

structure RepLodsdDownLoop [Bindings] (s : RamState) (slo : Nat) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0xAD]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcTop : (rsi.read s).toNat + 4 = slo + 4 * count
  srcLow : slo + 4 * count ≤ 2^32
  srcMem : ∀ i < 4 * count, (s.external[BitVec.ofNat 64 slo + BitVec.ofNat 64 i]?).isSome

theorem RepLodsdDownLoop.rcx_ne [Bindings] {s : RamState} {slo count : Nat}
    (h : RepLodsdDownLoop s slo count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodsdDownLoop.stop [Bindings] {s : RamState} {slo count : Nat}
    (h : RepLodsdDownLoop s slo (count + 1)) (i : Nat) :
    BitVec.ofNat 64 slo + BitVec.ofNat 64 (4 * count + i) = rsi.read s + BitVec.ofNat 64 i :=
  ofNat_add_ofNat_eq (by have := h.srcTop; omega) i

theorem RepLodsdDownLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {slo count : Nat}
    (h : RepLodsdDownLoop s slo (count + 1)) :
    X86.Machine.step s = some (.next (repLodsDownAfter 32 2 s)) := by
  have := h.srcLow
  have := h.srcTop
  exact rep_lodsd_down_step hstride s h.ready [0xF3] (by simpa using scanPrefix_f3) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne (by omega))
    ⟨by omega, fun i hi => h.stop i ▸ h.srcMem (4 * count + i) (by omega)⟩

theorem RepLodsdDownLoop.next [Bindings] {s : RamState} {slo count : Nat}
    (h : RepLodsdDownLoop s slo (count + 2)) : RepLodsdDownLoop (repLodsDownAfter 32 2 s) slo (count + 1) := by
  have hsl := h.srcLow
  have hstop := h.srcTop
  have hrip : (repLodsDownAfter 32 2 s).RIP = s.RIP := by
    rw [repLodsDownAfter_rip 32 2 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hsn : (rsi.read (repLodsDownAfter 32 2 s)).toNat = (rsi.read s).toNat - 4 := by
    rw [repLodsDownAfter_rsi, toNat_sub_ofNat _ _ (by omega)]
  refine ⟨h.ready.repLodsDown 32 2, h.df, ?_, ?_,
    by rw [repLodsDownAfter_rcx, h.counter, ofNat_succ_sub_one], ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repLodsDownAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · omega
  · intro i hi
    rw [repLodsDownAfter_external]
    exact h.srcMem i (by omega)

structure RepLodsdDownDone [Bindings] (s t : RamState) (slo count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s - BitVec.ofNat 64 (4 * count)
  raxAfter : (Operand.reg 0 : Operand 64).read t =
    mergeGPR 32 ((Operand.mem (BitVec.ofNat 64 slo) : Operand 32).read s)
      ((Operand.reg 0 : Operand 64).read s)
  agrees : AgreesExcept [.reg 0, .reg 1, .reg 6, .rip] (clearRep s) t

theorem rep_lodsd_down_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (count : Nat) (s : RamState) (slo : Nat)
    (h : RepLodsdDownLoop s slo (count + 1)) :
    RepLodsdDownDone s (nextStates (count + 1) s) slo (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repLodsDownAfter 32 2 s) :=
      nextState_of_step (h.step hstride )
    have hsl := h.srcLow
    have hstop := h.srcTop
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repLodsDownAfter 32 2 s).Repeat_String_Operation = false := by
      rw [repLodsDownAfter_repeat, hc]; rfl
    have hslo : rsi.read s = BitVec.ofNat 64 slo := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
    refine ⟨(h.ready.repLodsDown 32 2).ready hflag, ?_, ?_, repLodsDownAfter_rsi 32 2 s, ?_, ?_⟩
    · rw [repLodsDownAfter_rip 32 2 s h.ready.msr, hc]; rfl
    · rw [repLodsDownAfter_rcx, hc]
    · rw [repLodsDownAfter_rax, hslo]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repLodsDown 32 2 s
  | succ m ih =>
    have hnext : nextState s = (repLodsDownAfter 32 2 s) :=
      nextState_of_step (h.step hstride )
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 32).read (repLodsDownAfter 32 2 s) =
          (Operand.mem a : Operand 32).read s := by
      simp only [Operand.read, repLodsDownAfter_external]
    have ih' := ih (repLodsDownAfter 32 2 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repLodsDownAfter 32 2 s).RIP = s.RIP := by
      rw [repLodsDownAfter_rip 32 2 s h.ready.msr, h.counter]
      have := h.srcLow
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, repLodsDownAfter_rsi, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.raxAfter, repLodsDownAfter_rax, mergeGPR_mergeGPR 32 (by decide), hm]
    · refine ((AgreesExcept.repLodsDown 32 2 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepLodsdDownPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  srcBase : 4 * (rcx.read s).toNat ≤ (rsi.read s).toNat + 4
  srcLow : (rsi.read s).toNat + 4 ≤ 2^32
  srcMem : ∀ i < 4 * (rcx.read s).toNat,
    (s.external[downBase rsi 4 s + BitVec.ofNat 64 i]?).isSome

def repLodsdDownEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rsi, rsi.read s - BitVec.ofNat 64 (4 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.reg 0 : Operand 64), if rcx.read s = 0 then (Operand.reg 0 : Operand 64).read s else
      ((Operand.mem (downBase rsi 4 s) : Operand 32).read s).setWidth 64⟩]

@[simp] theorem repLodsdDownEffect_components (p : BitVec 64) (s : RamState) :
    (repLodsdDownEffect p s).components = [.reg 6, .reg 1, .reg 0, .rip] := by
  simp [repLodsdDownEffect, Effect.components]

theorem rep_lodsd_down_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0xAD]) s) (hpre : RepLodsdDownPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0xAD]) t ∧ (repLodsdDownEffect p s).Holds s t := by
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
    · rw [hag.read (by simp), hn, Nat.mul_zero]
      exact (BitVec.sub_zero _).symm
    · rw [hag.read (by simp), hz]
    · show (Operand.reg 0 : Operand 64).read _ = _
      rw [hag.read (by simp)]; simp [hz]
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.srcLow
      have := hpre.srcBase
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hnz : rcx.read s ≠ 0 := fun h0 => by simp [h0] at hn
    have hsb : downBase rsi 4 s =
        BitVec.ofNat 64 ((rsi.read s).toNat + 4 - 4 * (c' + 1)) := by
      rw [downBase, hn]
    have hready : RepLodsdDownLoop s ((rsi.read s).toNat + 4 - 4 * (c' + 1)) (c' + 1) := by
      have := hpre.srcBase
      have := hpre.srcLow
      exact ⟨h.midRep, hpre.df, hcodeS, hlow, hc, by omega, by omega,
        fun i hi => hsb ▸ hpre.srcMem i (by omega)⟩
    have hd := rep_lodsd_down_loop hstride c' s _ hready
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
      rw [hd.raxAfter, hsb]
      exact mergeGPR_32 _ _
    · rw [repLodsdDownEffect_components]
      refine hag.mono ?_
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem rep_lodsd_down_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepLodsdDownPre p) (codeRange p [0xF3, 0xAD]) (Effect.post (repLodsdDownEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_lodsd_down_steps hstride p s h hcode hpre⟩

structure RepLodswDownLoop [Bindings] (s : RamState) (slo : Nat) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0x66, 0xAD]
  codeLow : s.RIP.toNat + 3 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcTop : (rsi.read s).toNat + 2 = slo + 2 * count
  srcLow : slo + 2 * count ≤ 2^32
  srcMem : ∀ i < 2 * count, (s.external[BitVec.ofNat 64 slo + BitVec.ofNat 64 i]?).isSome

theorem RepLodswDownLoop.rcx_ne [Bindings] {s : RamState} {slo count : Nat}
    (h : RepLodswDownLoop s slo count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodswDownLoop.stop [Bindings] {s : RamState} {slo count : Nat}
    (h : RepLodswDownLoop s slo (count + 1)) (i : Nat) :
    BitVec.ofNat 64 slo + BitVec.ofNat 64 (2 * count + i) = rsi.read s + BitVec.ofNat 64 i :=
  ofNat_add_ofNat_eq (by have := h.srcTop; omega) i

theorem RepLodswDownLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {slo count : Nat}
    (h : RepLodswDownLoop s slo (count + 1)) :
    X86.Machine.step s = some (.next (repLodsDownAfter 16 3 s)) := by
  have := h.srcLow
  have := h.srcTop
  exact rep_lodsw_down_step hstride s h.ready [0xF3, 0x66] (by simp [scanPrefix_f3, scanPrefix_66]) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne (by omega))
    ⟨by omega, fun i hi => h.stop i ▸ h.srcMem (2 * count + i) (by omega)⟩

theorem RepLodswDownLoop.next [Bindings] {s : RamState} {slo count : Nat}
    (h : RepLodswDownLoop s slo (count + 2)) : RepLodswDownLoop (repLodsDownAfter 16 3 s) slo (count + 1) := by
  have hsl := h.srcLow
  have hstop := h.srcTop
  have hrip : (repLodsDownAfter 16 3 s).RIP = s.RIP := by
    rw [repLodsDownAfter_rip 16 3 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hsn : (rsi.read (repLodsDownAfter 16 3 s)).toNat = (rsi.read s).toNat - 2 := by
    rw [repLodsDownAfter_rsi, toNat_sub_ofNat _ _ (by omega)]
  refine ⟨h.ready.repLodsDown 16 3, h.df, ?_, ?_,
    by rw [repLodsDownAfter_rcx, h.counter, ofNat_succ_sub_one], ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repLodsDownAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · omega
  · intro i hi
    rw [repLodsDownAfter_external]
    exact h.srcMem i (by omega)

structure RepLodswDownDone [Bindings] (s t : RamState) (slo count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 3)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s - BitVec.ofNat 64 (2 * count)
  raxAfter : (Operand.reg 0 : Operand 64).read t =
    mergeGPR 16 ((Operand.mem (BitVec.ofNat 64 slo) : Operand 16).read s)
      ((Operand.reg 0 : Operand 64).read s)
  agrees : AgreesExcept [.reg 0, .reg 1, .reg 6, .rip] (clearRep s) t

theorem rep_lodsw_down_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (count : Nat) (s : RamState) (slo : Nat)
    (h : RepLodswDownLoop s slo (count + 1)) :
    RepLodswDownDone s (nextStates (count + 1) s) slo (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repLodsDownAfter 16 3 s) :=
      nextState_of_step (h.step hstride )
    have hsl := h.srcLow
    have hstop := h.srcTop
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repLodsDownAfter 16 3 s).Repeat_String_Operation = false := by
      rw [repLodsDownAfter_repeat, hc]; rfl
    have hslo : rsi.read s = BitVec.ofNat 64 slo := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
    refine ⟨(h.ready.repLodsDown 16 3).ready hflag, ?_, ?_, repLodsDownAfter_rsi 16 3 s, ?_, ?_⟩
    · rw [repLodsDownAfter_rip 16 3 s h.ready.msr, hc]; rfl
    · rw [repLodsDownAfter_rcx, hc]
    · rw [repLodsDownAfter_rax, hslo]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repLodsDown 16 3 s
  | succ m ih =>
    have hnext : nextState s = (repLodsDownAfter 16 3 s) :=
      nextState_of_step (h.step hstride )
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 16).read (repLodsDownAfter 16 3 s) =
          (Operand.mem a : Operand 16).read s := by
      simp only [Operand.read, repLodsDownAfter_external]
    have ih' := ih (repLodsDownAfter 16 3 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repLodsDownAfter 16 3 s).RIP = s.RIP := by
      rw [repLodsDownAfter_rip 16 3 s h.ready.msr, h.counter]
      have := h.srcLow
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, repLodsDownAfter_rsi, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.raxAfter, repLodsDownAfter_rax, mergeGPR_mergeGPR 16 (by decide), hm]
    · refine ((AgreesExcept.repLodsDown 16 3 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepLodswDownPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  srcBase : 2 * (rcx.read s).toNat ≤ (rsi.read s).toNat + 2
  srcLow : (rsi.read s).toNat + 2 ≤ 2^32
  srcMem : ∀ i < 2 * (rcx.read s).toNat,
    (s.external[downBase rsi 2 s + BitVec.ofNat 64 i]?).isSome

def repLodswDownEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 3
  writes := [⟨rsi, rsi.read s - BitVec.ofNat 64 (2 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.reg 0 : Operand 64), if rcx.read s = 0 then (Operand.reg 0 : Operand 64).read s else
      mergeGPR 16 ((Operand.mem (downBase rsi 2 s) : Operand 16).read s)
        ((Operand.reg 0 : Operand 64).read s)⟩]

@[simp] theorem repLodswDownEffect_components (p : BitVec 64) (s : RamState) :
    (repLodswDownEffect p s).components = [.reg 6, .reg 1, .reg 0, .rip] := by
  simp [repLodswDownEffect, Effect.components]

theorem rep_lodsw_down_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0x66, 0xAD]) s) (hpre : RepLodswDownPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0x66, 0xAD]) t ∧ (repLodswDownEffect p s).Holds s t := by
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
    · rw [hag.read (by simp), hn, Nat.mul_zero]
      exact (BitVec.sub_zero _).symm
    · rw [hag.read (by simp), hz]
    · show (Operand.reg 0 : Operand 64).read _ = _
      rw [hag.read (by simp)]; simp [hz]
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.srcLow
      have := hpre.srcBase
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hnz : rcx.read s ≠ 0 := fun h0 => by simp [h0] at hn
    have hsb : downBase rsi 2 s =
        BitVec.ofNat 64 ((rsi.read s).toNat + 2 - 2 * (c' + 1)) := by
      rw [downBase, hn]
    have hready : RepLodswDownLoop s ((rsi.read s).toNat + 2 - 2 * (c' + 1)) (c' + 1) := by
      have := hpre.srcBase
      have := hpre.srcLow
      exact ⟨h.midRep, hpre.df, hcodeS, hlow, hc, by omega, by omega,
        fun i hi => hsb ▸ hpre.srcMem i (by omega)⟩
    have hd := rep_lodsw_down_loop hstride c' s _ hready
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
      rw [hd.raxAfter, hsb]
    · rw [repLodswDownEffect_components]
      refine hag.mono ?_
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem rep_lodsw_down_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepLodswDownPre p) (codeRange p [0xF3, 0x66, 0xAD]) (Effect.post (repLodswDownEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_lodsw_down_steps hstride p s h hcode hpre⟩

structure RepLodsbDownLoop [Bindings] (s : RamState) (slo : Nat) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagSet s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0xAC]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcTop : (rsi.read s).toNat + 1 = slo + 1 * count
  srcLow : slo + 1 * count ≤ 2^32
  srcMem : ∀ i < 1 * count, (s.external[BitVec.ofNat 64 slo + BitVec.ofNat 64 i]?).isSome

theorem RepLodsbDownLoop.rcx_ne [Bindings] {s : RamState} {slo count : Nat}
    (h : RepLodsbDownLoop s slo count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem RepLodsbDownLoop.stop [Bindings] {s : RamState} {slo count : Nat}
    (h : RepLodsbDownLoop s slo (count + 1)) (i : Nat) :
    BitVec.ofNat 64 slo + BitVec.ofNat 64 (1 * count + i) = rsi.read s + BitVec.ofNat 64 i :=
  ofNat_add_ofNat_eq (by have := h.srcTop; omega) i

theorem RepLodsbDownLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {slo count : Nat}
    (h : RepLodsbDownLoop s slo (count + 1)) :
    X86.Machine.step s = some (.next (repLodsDownAfter 8 2 s)) := by
  have := h.srcLow
  have := h.srcTop
  exact rep_lodsb_down_step hstride s h.ready [0xF3] (by simpa using scanPrefix_f3) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne (by omega))
    ⟨by omega, fun i hi => h.stop i ▸ h.srcMem (1 * count + i) (by omega)⟩

theorem RepLodsbDownLoop.next [Bindings] {s : RamState} {slo count : Nat}
    (h : RepLodsbDownLoop s slo (count + 2)) : RepLodsbDownLoop (repLodsDownAfter 8 2 s) slo (count + 1) := by
  have hsl := h.srcLow
  have hstop := h.srcTop
  have hrip : (repLodsDownAfter 8 2 s).RIP = s.RIP := by
    rw [repLodsDownAfter_rip 8 2 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hsn : (rsi.read (repLodsDownAfter 8 2 s)).toNat = (rsi.read s).toNat - 1 := by
    rw [repLodsDownAfter_rsi, toNat_sub_ofNat _ _ (by omega)]
  refine ⟨h.ready.repLodsDown 8 2, h.df, ?_, ?_,
    by rw [repLodsDownAfter_rcx, h.counter, ofNat_succ_sub_one], ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repLodsDownAfter_external]
    exact h.code i hi
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · omega
  · intro i hi
    rw [repLodsDownAfter_external]
    exact h.srcMem i (by omega)

structure RepLodsbDownDone [Bindings] (s t : RamState) (slo count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s - BitVec.ofNat 64 (1 * count)
  raxAfter : (Operand.reg 0 : Operand 64).read t =
    mergeGPR 8 ((Operand.mem (BitVec.ofNat 64 slo) : Operand 8).read s)
      ((Operand.reg 0 : Operand 64).read s)
  agrees : AgreesExcept [.reg 0, .reg 1, .reg 6, .rip] (clearRep s) t

theorem rep_lodsb_down_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (count : Nat) (s : RamState) (slo : Nat)
    (h : RepLodsbDownLoop s slo (count + 1)) :
    RepLodsbDownDone s (nextStates (count + 1) s) slo (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repLodsDownAfter 8 2 s) :=
      nextState_of_step (h.step hstride )
    have hsl := h.srcLow
    have hstop := h.srcTop
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repLodsDownAfter 8 2 s).Repeat_String_Operation = false := by
      rw [repLodsDownAfter_repeat, hc]; rfl
    have hslo : rsi.read s = BitVec.ofNat 64 slo := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
    refine ⟨(h.ready.repLodsDown 8 2).ready hflag, ?_, ?_, repLodsDownAfter_rsi 8 2 s, ?_, ?_⟩
    · rw [repLodsDownAfter_rip 8 2 s h.ready.msr, hc]; rfl
    · rw [repLodsDownAfter_rcx, hc]
    · rw [repLodsDownAfter_rax, hslo]
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repLodsDown 8 2 s
  | succ m ih =>
    have hnext : nextState s = (repLodsDownAfter 8 2 s) :=
      nextState_of_step (h.step hstride )
    have hm (a : BitVec 64) :
        (Operand.mem a : Operand 8).read (repLodsDownAfter 8 2 s) =
          (Operand.mem a : Operand 8).read s := by
      simp only [Operand.read, repLodsDownAfter_external]
    have ih' := ih (repLodsDownAfter 8 2 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repLodsDownAfter 8 2 s).RIP = s.RIP := by
      rw [repLodsDownAfter_rip 8 2 s h.ready.msr, h.counter]
      have := h.srcLow
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, repLodsDownAfter_rsi, sub_ofNat_sub_ofNat]; congr 2; omega
    · rw [ih'.raxAfter, repLodsDownAfter_rax, mergeGPR_mergeGPR 8 (by decide), hm]
    · refine ((AgreesExcept.repLodsDown 8 2 s).trans ih'.agrees).mono ?_
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc <;> exact hc

structure RepLodsbDownPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  srcBase : 1 * (rcx.read s).toNat ≤ (rsi.read s).toNat + 1
  srcLow : (rsi.read s).toNat + 1 ≤ 2^32
  srcMem : ∀ i < 1 * (rcx.read s).toNat,
    (s.external[downBase rsi 1 s + BitVec.ofNat 64 i]?).isSome

def repLodsbDownEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rsi, rsi.read s - BitVec.ofNat 64 (1 * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.reg 0 : Operand 64), if rcx.read s = 0 then (Operand.reg 0 : Operand 64).read s else
      mergeGPR 8 ((Operand.mem (downBase rsi 1 s) : Operand 8).read s)
        ((Operand.reg 0 : Operand 64).read s)⟩]

@[simp] theorem repLodsbDownEffect_components (p : BitVec 64) (s : RamState) :
    (repLodsbDownEffect p s).components = [.reg 6, .reg 1, .reg 0, .rip] := by
  simp [repLodsbDownEffect, Effect.components]

theorem rep_lodsb_down_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0xAC]) s) (hpre : RepLodsbDownPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0xAC]) t ∧ (repLodsbDownEffect p s).Holds s t := by
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
    · rw [hag.read (by simp), hn, Nat.mul_zero]
      exact (BitVec.sub_zero _).symm
    · rw [hag.read (by simp), hz]
    · show (Operand.reg 0 : Operand 64).read _ = _
      rw [hag.read (by simp)]; simp [hz]
  · have hc : rcx.read s = BitVec.ofNat 64 (c' + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.srcLow
      have := hpre.srcBase
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hnz : rcx.read s ≠ 0 := fun h0 => by simp [h0] at hn
    have hsb : downBase rsi 1 s =
        BitVec.ofNat 64 ((rsi.read s).toNat + 1 - 1 * (c' + 1)) := by
      rw [downBase, hn]
    have hready : RepLodsbDownLoop s ((rsi.read s).toNat + 1 - 1 * (c' + 1)) (c' + 1) := by
      have := hpre.srcBase
      have := hpre.srcLow
      exact ⟨h.midRep, hpre.df, hcodeS, hlow, hc, by omega, by omega,
        fun i hi => hsb ▸ hpre.srcMem i (by omega)⟩
    have hd := rep_lodsb_down_loop hstride c' s _ hready
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
      rw [hd.raxAfter, hsb]
    · rw [repLodsbDownEffect_components]
      refine hag.mono ?_
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem rep_lodsb_down_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepLodsbDownPre p) (codeRange p [0xF3, 0xAC]) (Effect.post (repLodsbDownEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_lodsb_down_steps hstride p s h hcode hpre⟩

attribute [x86_compose] repLodsqDownEffect repLodsdDownEffect repLodswDownEffect repLodsbDownEffect

@[x86_local] theorem repLodsqDownEffect_local {p : BitVec 64} : Effect.Local (repLodsqDownEffect p) := by
  effect_local [repLodsqDownEffect, downBase]

@[x86_local] theorem repLodsdDownEffect_local {p : BitVec 64} : Effect.Local (repLodsdDownEffect p) := by
  effect_local [repLodsdDownEffect, downBase]

@[x86_local] theorem repLodswDownEffect_local {p : BitVec 64} : Effect.Local (repLodswDownEffect p) := by
  effect_local [repLodswDownEffect, downBase]

@[x86_local] theorem repLodsbDownEffect_local {p : BitVec 64} : Effect.Local (repLodsbDownEffect p) := by
  effect_local [repLodsbDownEffect, downBase]

end X86Proofs

