import X86Proofs.Program.ReadWrite.String
import X86Proofs.Program.Compose

/-!
# REP string instructions: the iteration bookkeeping

Shared by the `REP` and `REPE` string forms (`rep movsq` in `Instructions/Movs`, the rep_string
and repe_string families). With the stride binding answering 1 (`Prelude.UnitStringStride`), one
`step` of a `REP` form with RCX ≠ 0 is one iteration followed by `repCount` (RCX decremented, the
repeat flag set to whether it is still non-zero); RIP stays on the instruction until RCX reaches
0. The states between iterations have the repeat flag set, so they are `ReadyMidRep`, and frames
are stated between the states with the flag cleared (`clearRep`).

- `repCount`, `clearRep` and its lemmas, `ReadyMidRep.clear`, `ReadyMidRep.dataReady`,
  `ReadyMidRep.msr`; `repRexContext_rex_w`.
- `repZeroAfter len s`: the state a `REP` step with RCX = 0 ends in (nothing done, RIP moved on),
  with its RIP, memory and frame; `RepZeroPre p`, `repZeroEffect p len` (RIP := `p + len`, nothing
  else) and `Triple.of_repZero`: the triple of a `REP`, `REPE` or `REPNE` form with RCX = 0 from its
  `_step_zero` theorem.
- Address arithmetic (`add_ofNat_add_ofNat`, `toNat_add_ofNat`, `ofNat_succ_sub_one`,
  `ofNat_ne_zero`; for DF = 1 `ofNat_add_ofNat_eq`, `sub_ofNat_sub_ofNat`, `sub_ofNat_add_ofNat`,
  `toNat_sub_ofNat` and `downBase`, the block a DF = 1 `REP` goes through), `nextStates_succ`,
  `memByte_congr`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The rest of one `rep movsq` iteration after the move: RCX decremented, and
`Repeat_String_Operation` set to whether it is still non-zero. -/
def repCount (u : RamState) : RamState :=
  { rcx.write u (rcx.read u - 1) with Repeat_String_Operation := !(rcx.read u - 1 == 0#64) }

/-- `s` with the repeat flag cleared. `ReadyMidRep s` is `ReadyToStep (clearRep s)`. -/
def clearRep (s : RamState) : RamState := { s with Repeat_String_Operation := false }

theorem clearRep_eq {s : RamState} (h : s.Repeat_String_Operation = false) : clearRep s = s := by
  have : ∀ b, s.Repeat_String_Operation = b → { s with Repeat_String_Operation := b } = s := by
    rintro b rfl; rfl
  exact this _ h

@[simp] theorem clearRep_external (s : RamState) : (clearRep s).external = s.external := rfl
@[simp] theorem clearRep_RIP (s : RamState) : (clearRep s).RIP = s.RIP := rfl
@[simp] theorem Operand.read_clearRep {n : Nat} (s : RamState) (op : Operand n) :
    op.read (clearRep s) = op.read s :=
  Operand.read_of_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl op

@[simp] theorem clearRep_ZMM (s : RamState) : (clearRep s).ZMM = s.ZMM := rfl
@[simp] theorem finishStep_ZMM (s : RamState) : (finishStep s).ZMM = s.ZMM := rfl
@[simp] theorem clearRep_MXCSR (s : RamState) : (clearRep s).MXCSR = s.MXCSR := rfl
@[simp] theorem finishStep_MXCSR (s : RamState) : (finishStep s).MXCSR = s.MXCSR := rfl
@[simp] theorem clearRep_FP87 (s : RamState) : (clearRep s).FP87 = s.FP87 := rfl
@[simp] theorem finishStep_FP87 (s : RamState) : (finishStep s).FP87 = s.FP87 := rfl
@[simp] theorem clearRep_FP87_Status (s : RamState) :
    (clearRep s).FP87_Status = s.FP87_Status := rfl
@[simp] theorem finishStep_FP87_Status (s : RamState) :
    (finishStep s).FP87_Status = s.FP87_Status := rfl
@[simp] theorem clearRep_FP87_Tag_Word (s : RamState) :
    (clearRep s).FP87_Tag_Word = s.FP87_Tag_Word := rfl
@[simp] theorem finishStep_FP87_Tag_Word (s : RamState) :
    (finishStep s).FP87_Tag_Word = s.FP87_Tag_Word := rfl
@[simp] theorem clearRep_FP87_Control (s : RamState) :
    (clearRep s).FP87_Control = s.FP87_Control := rfl
@[simp] theorem finishStep_FP87_Control (s : RamState) :
    (finishStep s).FP87_Control = s.FP87_Control := rfl
@[simp] theorem fpuPtrOf_clearRep (s : RamState) : fpuPtrOf (clearRep s) = fpuPtrOf s := rfl
@[simp] theorem fpuPtrOf_finishStep (s : RamState) : fpuPtrOf (finishStep s) = fpuPtrOf s := rfl

/-- The part of the state `AgreesExcept` always keeps is the same before and after `finishStep`
(which sets only RIP), with the repeat flag cleared. -/
theorem fixedPart_clearRep_finishStep (s : RamState) :
    fixedPart (clearRep (finishStep s)) = fixedPart (clearRep s) := rfl

/-- An `AgreesExcept` between the states with the flag cleared is one between the states, when
both flags are clear. -/
theorem AgreesExcept.of_clearRep {cs : List Component} {s t : RamState}
    (h : AgreesExcept cs (clearRep s) (clearRep t)) (hs : s.Repeat_String_Operation = false)
    (ht : t.Repeat_String_Operation = false) : AgreesExcept cs s t := by
  rwa [clearRep_eq hs, clearRep_eq ht] at h

/-- `ReadyMidRep` with the flag cleared reads as `ReadyToStep`. -/
theorem ReadyMidRep.clear [Bindings] {s : RamState} (h : ReadyMidRep s) : ReadyToStep (clearRep s) := h

theorem ReadyMidRep.dataReady [Bindings] {s : RamState} (h : ReadyMidRep s) : DataReady s :=
  (ReadyToStep.dataReady (s := clearRep s) h).of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
    (ReadyToStep.memory (s := clearRep s) h).tables

theorem repRexContext_rex_w {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (seg : Segment) :
    (repRexContext seg rex.toBitVec).rex_w = 1 := by
  simp only [RexWPrefix, List.mem_cons, List.not_mem_nil, or_false] at hrex
  rcases hrex with h | h | h | h | h | h | h | h <;> simp [repRexContext, rexContext, h]

theorem add_ofNat_add_ofNat (a : BitVec 64) (i j : Nat) :
    a + BitVec.ofNat 64 i + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (i + j) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem toNat_add_ofNat (a : BitVec 64) (i : Nat) (h : a.toNat + i < 2^64) :
    (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2^64 by omega),
    Nat.mod_eq_of_lt h]

theorem ofNat_succ_sub_one (c : Nat) :
    BitVec.ofNat 64 (c + 1) - 1 = BitVec.ofNat 64 c := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, h1]
  omega

theorem ofNat_ne_zero {c : Nat} (h0 : 0 < c) (h : c < 2^64) : BitVec.ofNat 64 c ≠ 0 := by
  intro he
  have := congrArg BitVec.toNat he
  have h1 : (0 : BitVec 64).toNat = 0 := rfl
  simp only [BitVec.toNat_ofNat, h1] at this
  omega

/-- `lo + (j + i)` is `a + i` when `a` is `lo + j`, as 64-bit addresses: the byte `i` of the element
at `a` in a block starting at `lo` (the DF = 1 loops count elements from the block's start). -/
theorem ofNat_add_ofNat_eq {a : BitVec 64} {lo j : Nat} (h : a.toNat = lo + j) (i : Nat) :
    BitVec.ofNat 64 lo + BitVec.ofNat 64 (j + i) = a + BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := a.isLt
  omega

theorem sub_ofNat_sub_ofNat (a : BitVec 64) (i j : Nat) :
    a - BitVec.ofNat 64 i - BitVec.ofNat 64 j = a - BitVec.ofNat 64 (i + j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := a.isLt
  omega

theorem sub_ofNat_add_ofNat (a : BitVec 64) (x j : Nat) :
    a - BitVec.ofNat 64 x + BitVec.ofNat 64 (x + j) = a + BitVec.ofNat 64 j := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := a.isLt
  omega

theorem toNat_sub_ofNat (a : BitVec 64) (i : Nat) (h : i ≤ a.toNat) :
    (a - BitVec.ofNat 64 i).toNat = a.toNat - i := by
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := a.isLt
  omega

/-- The lowest address of the `k * RCX` bytes a `REP` string instruction with DF = 1 goes through
from register `r` (RSI or RDI) down: its elements of `k` bytes end at `r + k`, the first at `r`. -/
def downBase (r : Operand 64) (k : Nat) (s : RamState) : BitVec 64 :=
  BitVec.ofNat 64 ((r.read s).toNat + k - k * (rcx.read s).toNat)

theorem ReadyMidRep.msr [Bindings] {s : RamState} (h : ReadyMidRep s) :
    s.«MSRLIST::In_Process» = false :=
  (ReadyToStep.ready (s := clearRep s) h).msr

theorem nextStates_succ [Bindings] (n : Nat) (s : RamState) : nextStates (n + 1) s = nextStates n (nextState s) :=
  nextStates_add n 1 s

/-- Bytes equal as `Option`s are equal as `memByte`s. -/
theorem memByte_congr {m m' : Ram} {a b : BitVec 64} (h : m[a]? = m'[b]?) :
    memByte m a = memByte m' b := by
  simp only [memByte, PhysicalMemory.read]
  exact congrArg (·.getD 0) h

/-! ### The step with RCX = 0 -/

/-- The state a `REP` string step of `len` bytes with RCX = 0 ends in: nothing is done, `Next_IP`
is set and the repeat flag cleared, so RIP moves past the instruction. -/
def repZeroAfter (len : Nat) (s : RamState) : RamState :=
  afterStep s len fun t =>
    { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 len), Repeat_String_Operation := false }

@[simp] theorem repZeroAfter_external (len : Nat) (s : RamState) :
    (repZeroAfter len s).external = s.external := rfl

theorem repZeroAfter_rip (len : Nat) (s : RamState) (hmsr : s.«MSRLIST::In_Process» = false) :
    (repZeroAfter len s).RIP = BitVec.add s.RIP (BitVec.ofNat 64 len) := by
  simp [repZeroAfter, afterStep, finishStep, afterFetches, beforeFetch, resetStepFields, hmsr]

theorem repZeroAfter_repeat (len : Nat) (s : RamState) :
    (repZeroAfter len s).Repeat_String_Operation = false := rfl

/-- The step with RCX = 0 changes only RIP (besides the bookkeeping and the repeat flag). -/
theorem AgreesExcept.repZero (len : Nat) (s : RamState) :
    AgreesExcept [.rip] (clearRep s) (clearRep (repZeroAfter len s)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r => rfl
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => rfl
  · simp only [fixedPart, clearRep, repZeroAfter, afterStep, finishStep, afterFetches,
      beforeFetch, resetStepFields]

/-! ### Triples with RCX = 0 -/

/-- The precondition of a `REP`, `REPE` or `REPNE` string triple with RCX = 0 at `p` (the
instruction reads and writes nothing, and moves RIP past itself): RIP = `p` and RCX = 0. -/
structure RepZeroPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  rcxZero : rcx.read s = 0

/-- The effect of a `len`-byte `REP`, `REPE` or `REPNE` string instruction at `p` with RCX = 0:
RIP := `p + len`; no register, memory location or flag changes. -/
def repZeroEffect (p : BitVec 64) (len : Nat) (_s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len

@[simp] theorem repZeroEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (repZeroEffect p len s).components = [.rip] := rfl

/-- A triple for a `REP` string instruction with RCX = 0 from its `_step_zero` theorem: every
ready state at `p` with the code and RCX = 0 steps to `repZeroAfter len`. -/
theorem Triple.of_repZero [Bindings] {p : BitVec 64} {len : Nat} {code : CodeMap}
    (hstep : ∀ s, ReadyToStep s → CodeIn code s → RepZeroPre p s →
      X86.Machine.step s = some (.next (repZeroAfter len s))) :
    Triple (RepZeroPre p) code (Effect.post (repZeroEffect p len)) := by
  refine Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [repZeroEffect_components]; simp [Component.Covers]) _) ?_
  intro s h hcode hpre
  have hag : AgreesExcept [.rip] s (repZeroAfter len s) :=
    (AgreesExcept.repZero len s).of_clearRep h.ready.repeatClear (repZeroAfter_repeat len s)
  refine ⟨_, hstep s h hcode hpre, ReadyToStep.of_agreesExcept h hag h.memory.tables,
    ?_, trivial, trivial, hag⟩
  rw [repZeroAfter_rip _ s h.ready.msr, hpre.rip]
  rfl

attribute [x86_compose] repZeroEffect

@[x86_local] theorem repZeroEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (repZeroEffect p len) := by
  effect_local [repZeroEffect]

/-- Close `Effect.Local` of a `REP MOVS` or `REP STOS` effect (its definition and `downBase` among
the lemmas): RIP is a constant, the flags untouched, and the writes read RSI, RDI, RCX and
memory, where RCX is also the width of the written block (rewritten everywhere at once); every
write is whole bytes. -/
syntax "rep_effect_local" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| rep_effect_local [$ls,*]) => `(tactic| (
    refine ⟨fun _ _ _ => rfl, fun t t' h => ?_, fun _ _ _ => rfl, fun t t' h i hi => ?_,
      fun t => ?_⟩
    · have hc : rcx.read t = rcx.read t' := h.read_reg 1
      simp only [$ls,*]
      rw [hc]
      simp only [h.read_reg, h.read_mem]
    · simpa [$ls,*, Effect.flag] using hi
    · simp (config := { decide := true }) only [$ls,*, x86_compose, List.forall_mem_cons,
        List.forall_mem_nil, and_true]))

/-! ### Preconditions after a block -/

section Carry

variable {e : Effect} {s s' : RamState}

@[x86_pre] theorem RepZeroPre.of_holds (h : e.Holds s s') (ho : Obs (e.after s true) s')
    {p : BitVec 64} (hrip : e.rip = p) (hc : rcx.read (e.after s true) = 0) : RepZeroPre p s' :=
  ⟨h.rip_of hrip, by rw [Obs.back_reg ho]; exact hc⟩

/-- The block a DF = 1 `REP` goes through, read after an effect: read in the canonical state
(it reads only the register and RCX). -/
@[x86_obs] theorem Obs.back_downBase {t t' : RamState} (ho : Obs t t') (n : BitVec 5) (k : Nat) :
    downBase (Operand.reg n) k t' = downBase (Operand.reg n) k t := by
  simp only [downBase, ho.read_reg]

end Carry

end X86Proofs
