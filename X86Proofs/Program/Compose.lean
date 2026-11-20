import X86Proofs.Program.Effect
import X86Proofs.Program.ReadWrite.Load
import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Program.ComposeAttr
import X86Proofs.Step.Address
import X86Proofs.Step.Sse
import X86Proofs.Step.Selector
import X86Proofs.Step.Umip

/-!
# Composing effects: one effect for a straight-line block

Phase 3 of Myreen et al.'s *Decompilation into Logic — Improved*: a block of instructions gets one
triple whose postcondition is a single effect of the start state, computed from the instructions'
effects. `Effect.seq e₁ e₂` is that composition, `Triple.seq_block` the rule that runs it, and
`x86_then` the tactic step that discharges the glue and normalizes the composed effect.

## Canonical states

An effect only partly determines the state it leads to (undefined flags, the oracle, the trace),
so `e₂` cannot be evaluated "at the state after `e₁`". It is evaluated at a *canonical* state
instead: `(e₁ s).after s b` is `s` with `e₁`'s writes applied (`applyWrites`, DF among them) and
its flags set, the undefined ones to `b`. Any real state after `e₁` agrees with it on everything
an instruction effect reads (`Obs`: the general-purpose registers, the bytes of memory, the vector
registers, the non-status bits of RFLAGS, MXCSR, the x87 state but its condition codes, and the
code segment), so `e₂` gives the same RIP and writes there,
provided `e₂` reads only those (`Effect.Local`; every instruction effect of the library does, see its `_local`
lemma at the end of the instruction's `Triple.lean`, proved with `effect_local`).

`Effect.seq e₁ e₂ s`:
- RIP: `e₂`'s, at the canonical state.
- writes: `e₁`'s locations, each re-read in the canonical state after both (so a later write to
  the same or an overlapping location is accounted for), then `e₂`'s writes. A register `e₂`
  writes again is dropped from `e₁`'s list.
- flags: per flag, `e₂`'s value if it is the same whether `e₁`'s undefined flags are all set or
  all clear, else undefined. A flag `e₂` passes through from an undefined one stays undefined; one
  it computes from registers is kept. This is sound because an instruction's output flag depends
  on the old flags only through the same flag (`Effect.Local.flag`).

Reads of the canonical states normalize with the simp set `x86_compose`: a register read after a
register write is the written value or the old read, a memory read after a store at the same
address is the stored value, and after a store at a provably disjoint offset from the same base
(`[rsp + c₁]` vs `[rsp + c₂]`) the old read. What does not normalize (a load after a store through
an unrelated base) stays as a read of the canonical state, which is still correct.

## Use

```
theorem block : Triple P (codeRange p bytes) (Effect.post stated) := by
  x86_begin t₁          -- the first instruction's triple, at p
  x86_then t₂           -- each next one, at p + offset
  …
  x86_finish [lemmas]   -- the composed effect implies `stated`
```

Each step's side goals (the instruction's `Local` fact, its code inside the block, its
precondition after the block so far, its writes missing the block's code) are discharged by
`x86_local`, `x86_sub`, `x86_mid` (and `x86_begin` for the first instruction); what they cannot
do is left as a goal after the main one, normalized, with the block's precondition `hP`, the block
so far `hH : (E s).Holds s s'` and its canonical state `hO` at hand.

## Preconditions after a block

`x86_mid` proves the next instruction's precondition at the state `s'` after the block so far.
It first splits the block's precondition into its parts (conjunctions all the way, structures
such as `StackFramePre` or `Sse2Pre` and their fields, normalized like the goals), then carries
the precondition over (`Carry.run`):
- reads of `s'` (registers, memory, XMM, MXCSR, DF, the x87 words, addresses, `downBase`, …) are
  rewritten to reads of the canonical state (the `@[x86_obs]` lemmas `Obs.back_*` applied to
  `hO`), the status flags of `s'` to the block's (`Effect.Holds.ofRFLAGS_eq`), and what every
  effect keeps (control registers, CPUID, the segment registers, IOPL, CPL, …, the `@[x86_inv]`
  lemmas) to the start state;
- a carry-over lemma (`@[x86_pre]`, `X.of_holds`) is applied by the head of the goal: from
  `h : e.Holds s s'` and `ho : Obs (e.after s true) s'`, `X … s'` follows from facts about the
  start state (what every effect keeps) and the canonical state (what depends on the data). The
  building blocks are `Effect.Holds.rip_of`, `MemReadable.of_holds`, `MemWritable.of_holds`,
  `Effect.Holds.present`, `LoadPre.of_holds`, `StorePre.of_holds` and their segment forms (any
  address function that reads only what `Obs` sees, `AddrObs`, shown by unfolding it,
  `@[x86_addr]`), and the shapes with facts of their own (`SsePre`, `MmxPre`, `X87Pre`,
  `MxcsrPre`, `LockedRmwPre`, `PopfqPre`, `CpuidPre`, the string preconditions, …);
- a structure without a lemma (a generated `REP` precondition, `EnterL1Pre`, …) or a conjunction
  (`CallPre`, `PushMemPre`, `LoopePre`, …) is split into its fields, each carried over in turn;
  a `∀` is introduced and a definition (an instruction's `…Ok` predicate) unfolded.

The facts left (`x86_side`) are closed after normalizing them (`x86_norm`) by a part of the
block's precondition, a stack-frame slot (`x86_frame`), or a range apart from the whole block
(`RangeApart.sub`). A parameter equation (the carry ADC is given, the ZF of `LOOPE`, the stack top
of an x87 instruction) becomes a goal about the block's computed value that `x86_norm` closes or
the block's precondition states. What still fails is a fact about the data the block's
precondition does not state; it is left as a goal about the start state.

The carry-over lemmas also serve by hand (`SegLoadPre.of_holds`, `X87Pre.of_holds`, …), and
`x86_of_holds h ho` proves a new one (`Carry.run` with the lemma's own hypotheses).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-! ### Status flags by name -/

/-- One of the six status flags. -/
inductive StatusFlag where
  | CF | PF | AF | ZF | SF | OF
  deriving DecidableEq

/-- The value of flag `i`. -/
@[x86_compose] def StatusFlags.get (f : StatusFlags) : StatusFlag → Bool
  | .CF => f.CF | .PF => f.PF | .AF => f.AF | .ZF => f.ZF | .SF => f.SF | .OF => f.OF

/-- Flag `i` set to `b`. -/
def StatusFlags.set (f : StatusFlags) : StatusFlag → Bool → StatusFlags
  | .CF, b => { f with CF := b }
  | .PF, b => { f with PF := b }
  | .AF, b => { f with AF := b }
  | .ZF, b => { f with ZF := b }
  | .SF, b => { f with SF := b }
  | .OF, b => { f with OF := b }

/-- The position of a status flag among the six (`CF` 0, …, `OF` 5). -/
def StatusFlag.index : StatusFlag → Nat
  | .CF => 0 | .PF => 1 | .AF => 2 | .ZF => 3 | .SF => 4 | .OF => 5

/-- The status flag at position `i` (`OF` from 5 on). -/
def StatusFlag.ofIndex : Nat → StatusFlag
  | 0 => .CF | 1 => .PF | 2 => .AF | 3 => .ZF | 4 => .SF | _ => .OF

/-- What a flags outcome gives for flag `i`. -/
@[x86_compose] def StatusFlagsOutcome.get (fe : StatusFlagsOutcome) : StatusFlag → Option Bool
  | .CF => fe.CF | .PF => fe.PF | .AF => fe.AF | .ZF => fe.ZF | .SF => fe.SF | .OF => fe.OF

/-- The flags outcome with flag `i` given by `f i`. -/
@[x86_compose] def StatusFlagsOutcome.ofFun (f : StatusFlag → Option Bool) : StatusFlagsOutcome :=
  ⟨f .CF, f .PF, f .AF, f .ZF, f .SF, f .OF⟩

theorem StatusFlagsOutcome.get_ofFun (f : StatusFlag → Option Bool) (i : StatusFlag) :
    (StatusFlagsOutcome.ofFun f).get i = f i := by
  cases i <;> rfl

theorem StatusFlagsOutcome.allows_iff (fe : StatusFlagsOutcome) (f : StatusFlags) :
    fe.Allows f ↔ ∀ i, FlagAllows (fe.get i) (f.get i) :=
  ⟨fun ⟨a, b, c, d, e, g⟩ i => by cases i <;> assumption,
   fun h => ⟨h .CF, h .PF, h .AF, h .ZF, h .SF, h .OF⟩⟩

/-- What effect `e` from `s` leaves in flag `i`: `some v` if it is `v`, `none` if undefined. A flag
`e` leaves alone is its value in `s`. -/
@[x86_compose] def Effect.flag (e : Effect) (s : RamState) (i : StatusFlag) : Option Bool :=
  match e.flags with
  | none => some ((StatusFlags.ofRFLAGS s.RFLAGS).get i)
  | some fe => fe.get i

/-! ### Components -/

theorem Operand.component_ne_flags {n : Nat} (op : Operand n) : op.component ≠ .flags := by
  cases op <;> simp [Operand.component]

theorem Operand.component_ne_rip {n : Nat} (op : Operand n) : op.component ≠ .rip := by
  cases op <;> simp [Operand.component]

theorem Effect.mem_components {e : Effect} {c : Component} :
    c ∈ e.components ↔
      (∃ w ∈ e.writes, w.component = c) ∨ (e.flags.isSome ∧ c = .flags) ∨ c = .rip := by
  unfold Effect.components
  cases e.flags <;> simp [List.mem_map, eq_comm]

theorem Effect.flags_not_mem {e : Effect} (h : e.flags = none) : Component.flags ∉ e.components := by
  rw [Effect.mem_components]
  rintro (⟨w, -, hw⟩ | ⟨hs, -⟩ | h)
  · exact Operand.component_ne_flags _ hw
  · simp [h] at hs
  · cases h

theorem Effect.Holds.flag {e : Effect} {s s' : RamState} (h : e.Holds s s') (i : StatusFlag) :
    FlagAllows (e.flag s i) ((StatusFlags.ofRFLAGS s'.RFLAGS).get i) := by
  unfold Effect.flag
  cases hf : e.flags with
  | none =>
    show _ = _
    rw [h.agrees.statusFlags (Effect.flags_not_mem hf)]
  | some fe =>
    have := h.flags
    simp only [Effect.FlagsHold, hf] at this
    exact (StatusFlagsOutcome.allows_iff fe _).mp this i

/-! ### Writes -/

theorem Write.allHold_iff {s' : RamState} :
    ∀ {ws : List Write}, Write.AllHold s' ws ↔ ∀ w ∈ ws, w.dst.read s' = w.val
  | [] => by simp [Write.AllHold]
  | [w] => by simp [Write.AllHold]
  | w :: w' :: ws => by
    simp only [Write.AllHold]
    rw [allHold_iff (ws := w' :: ws)]
    simp

/-- The operand sizes composition supports: a 64-bit register, whole bytes of memory (any number,
so a `REP` string store's `8 * RCX` bytes too), an XMM register at 128 bits, MXCSR at 32 bits, DF
at 1 bit, a physical x87 register at 80 bits, the x87 status, tag and control words at 16 bits,
the last-instruction pointers at 171 bits, the condition codes at 4 bits. (Every write of the
library's instruction effects has one; a write of AH–BH is stated as a write of the whole
register, a write of an MMX register as the 80-bit write of its physical register, `mmxFpr`.) -/
def Operand.Full {n : Nat} : Operand n → Prop
  | .reg _ => n = 64
  | .mem _ => n % 8 = 0
  | .xmm _ => n = 128
  | .regHigh _ => False
  | .mxcsr => n = 32
  | .df => n = 1
  | .fpr _ => n = 80
  | .mmx _ => False
  | .fsw => n = 16
  | .ftw => n = 16
  | .fcw => n = 16
  | .fpuPtr => n = 171
  | .fcc _ => n = 4

/-- The write has a supported size (`Operand.Full`). -/
@[x86_compose] def Write.Full (w : Write) : Prop := w.dst.Full

@[x86_compose] theorem Operand.full_reg (r : BitVec 5) : (Operand.reg r : Operand 64).Full := id rfl
@[x86_compose] theorem Operand.full_xmm (r : BitVec 5) : (Operand.xmm r : Operand 128).Full := id rfl
@[x86_compose] theorem Operand.full_mxcsr : (Operand.mxcsr : Operand 32).Full := id rfl
@[x86_compose] theorem Operand.full_df : (Operand.df : Operand 1).Full := id rfl
@[x86_compose] theorem Operand.full_fpr (r : BitVec 3) : (Operand.fpr r : Operand 80).Full := id rfl
@[x86_compose] theorem Operand.full_fsw : (Operand.fsw : Operand 16).Full := id rfl
@[x86_compose] theorem Operand.full_ftw : (Operand.ftw : Operand 16).Full := id rfl
@[x86_compose] theorem Operand.full_fcw : (Operand.fcw : Operand 16).Full := id rfl
@[x86_compose] theorem Operand.full_fpuPtr : (Operand.fpuPtr : Operand 171).Full := id rfl
@[x86_compose] theorem Operand.full_fcc (m : BitVec 4) : (Operand.fcc m : Operand 4).Full :=
  id rfl
@[x86_compose] theorem Operand.full_mem {n : Nat} (a : BitVec 64) :
    (Operand.mem a : Operand n).Full ↔ n % 8 = 0 := id Iff.rfl

/-- A number of bits that is a multiple of 8 times something is whole bytes (a `REP` store's
size). -/
@[x86_compose] theorem mul_mod_eight {k : Nat} (x : Nat) (hk : k % 8 = 0) : k * x % 8 = 0 := by
  rw [Nat.mul_mod, hk, Nat.zero_mul, Nat.zero_mod]

/-- The bytes of a `REP` string store of `8 * n` bits. -/
@[x86_compose] theorem eight_mul_div_eight (n : Nat) : 8 * n / 8 = n :=
  Nat.mul_div_cancel_left n (by decide)

theorem Write.mk_eq_mk {n : Nat} {a b : Operand n} {v w : BitVec n} :
    (⟨a, v⟩ : Write) = ⟨b, w⟩ ↔ a = b ∧ v = w := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- `t` with write `w` applied. -/
def Write.apply (t : RamState) (w : Write) : RamState := w.dst.write t w.val

/-- `t` with the writes applied in order. -/
def applyWrites (t : RamState) (ws : List Write) : RamState := ws.foldl Write.apply t

@[x86_compose] theorem applyWrites_nil (t : RamState) : applyWrites t [] = t := id rfl

@[x86_compose] theorem applyWrites_cons (t : RamState) (w : Write) (ws : List Write) :
    applyWrites t (w :: ws) = applyWrites (w.apply t) ws := id rfl

@[x86_compose] theorem Write.apply_mk {n : Nat} (t : RamState) (op : Operand n) (v : BitVec n) :
    Write.apply t ⟨op, v⟩ = op.write t v := id rfl

/-- A write changes no bit of RFLAGS besides DF (only `Operand.df` writes RFLAGS at all). -/
theorem Operand.write_RFLAGS {n : Nat} (t : RamState) (op : Operand n) (v : BitVec n) :
    clearDirectionFlag (clearStatusFlags (op.write t v).RFLAGS) =
      clearDirectionFlag (clearStatusFlags t.RFLAGS) := by
  cases op with
  | df => simp only [Operand.write, clearDirectionFlag_clearStatusFlags_setSlice_df]
  | _ => rfl

/-- Writes change no bit of RFLAGS besides DF. -/
theorem applyWrites_RFLAGS (t : RamState) (ws : List Write) :
    clearDirectionFlag (clearStatusFlags (applyWrites t ws).RFLAGS) =
      clearDirectionFlag (clearStatusFlags t.RFLAGS) := by
  induction ws generalizing t with
  | nil => rfl
  | cons w ws ih => rw [applyWrites_cons, ih]; exact Operand.write_RFLAGS _ _ _

/-- An observation `o` of the state after some writes is `v` if each write either keeps `o` or
sets it to `v`, and `o` starts at `v` or some write sets it to `v` whatever the state. -/
theorem applyWrites_obs {α : Type} (o : RamState → α) (v : α) :
    ∀ (ws : List Write) (t : RamState),
      (∀ w ∈ ws, ∀ t, o (Write.apply t w) = o t ∨ o (Write.apply t w) = v) →
      (o t = v ∨ ∃ w ∈ ws, ∀ t, o (Write.apply t w) = v) → o (applyWrites t ws) = v
  | [], t, _, hi => by
    rcases hi with h | ⟨w, hw, _⟩
    · exact h
    · cases hw
  | w :: ws, t, hw, hi => by
    rw [applyWrites_cons]
    apply applyWrites_obs o v ws _ (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw'))
    rcases hw w List.mem_cons_self t with h | h
    · rcases hi with h' | ⟨w', hw', hd⟩
      · exact .inl (h.trans h')
      · rcases List.mem_cons.mp hw' with rfl | hw'
        · exact .inl (hd t)
        · exact .inr ⟨w', hw', hd⟩
    · exact .inl h

/-- No write changes the code segment register. -/
theorem applyWrites_CS (t : RamState) (ws : List Write) : (applyWrites t ws).CS = t.CS := by
  induction ws generalizing t with
  | nil => rfl
  | cons w ws ih =>
    rw [applyWrites_cons, ih]
    rcases w with @⟨n, dst, v⟩
    cases dst <;> rfl

/-! ### The x87 condition codes

Composition does not track the condition codes C0–C3 (`Obs` leaves them out), since most x87
instructions leave them undefined. A write of `Operand.fcc m` states the codes in `m`; after a list
of writes, a code that some write sets is the value of the last such write
(`Write.cc_applyWrites_holds`, `Write.cc_applyWrites_det`), which is how a composed effect's
re-read of such a write is justified. -/

/-- Write `w` sets condition code C`i`: a write of `Operand.fcc m` with C`i` in `m`. -/
def Write.SetsCC (i : Nat) (w : Write) : Prop :=
  match w with
  | ⟨.fcc m, _⟩ => m.getLsbD i = true
  | _ => False

/-- Condition code C`i` of a state. -/
def ccBit (i : Nat) (t : RamState) : Bool := (fswCC t.FP87_Status).getLsbD i

theorem lt4_of_getLsbD {m : BitVec 4} {i : Nat} (h : m.getLsbD i = true) : i < 4 := by
  by_cases hi : i < 4
  · exact hi
  · rw [BitVec.getLsbD_of_ge m i (by omega)] at h
    cases h

theorem Write.ccBit_apply_of_not (t : RamState) {i : Nat} (w : Write) (h : ¬ w.SetsCC i) :
    ccBit i (w.apply t) = ccBit i t := by
  rcases w with @⟨n, dst, v⟩
  cases dst with
  | fsw => simp only [ccBit, Write.apply_mk, Operand.write, fswCC_fswMerge]
  | fcc m =>
    have hm : m.getLsbD i = false := by simpa [Write.SetsCC] using h
    simp only [ccBit, Write.apply_mk, Operand.write, fswCC_fswSetCC, BitVec.getLsbD_or,
      BitVec.getLsbD_and, BitVec.getLsbD_not, hm]
    by_cases hi : i < 4
    · simp [hi]
    · simp [hi, BitVec.getLsbD_of_ge (fswCC t.FP87_Status) i (by omega)]
  | _ => rfl

theorem Write.ccBit_apply_fcc (t : RamState) {i n : Nat} (m : BitVec 4) (v : BitVec n)
    (h : m.getLsbD i = true) :
    ccBit i ((⟨.fcc m, v⟩ : Write).apply t) = (v.setWidth 4).getLsbD i := by
  have hi : i < 4 := lt4_of_getLsbD h
  simp only [ccBit, Write.apply_mk, Operand.write, fswCC_fswSetCC, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, h, hi]
  simp

/-- A condition code no write of the list sets is unchanged. -/
theorem Write.ccBit_applyWrites_of_none {i : Nat} :
    ∀ (ws : List Write) (t : RamState), (∀ w ∈ ws, ¬ w.SetsCC i) →
      ccBit i (applyWrites t ws) = ccBit i t
  | [], _, _ => rfl
  | w :: ws, t, h => by
    rw [applyWrites_cons, Write.ccBit_applyWrites_of_none ws _
      (fun w' hw' => h w' (List.mem_cons_of_mem _ hw')),
      Write.ccBit_apply_of_not t w (h w List.mem_cons_self)]

/-- A condition code some write of the list sets is the same after the list from any state. -/
theorem Write.cc_applyWrites_det {i : Nat} :
    ∀ (ws : List Write), (∃ w ∈ ws, w.SetsCC i) → ∀ (t t' : RamState),
      ccBit i (applyWrites t ws) = ccBit i (applyWrites t' ws)
  | [], h, _, _ => by obtain ⟨w, hw, -⟩ := h; cases hw
  | w :: ws, h, t, t' => by
    rw [applyWrites_cons, applyWrites_cons]
    by_cases hl : ∃ w' ∈ ws, w'.SetsCC i
    · exact Write.cc_applyWrites_det ws hl _ _
    · have hn : ∀ w' ∈ ws, ¬ w'.SetsCC i := fun w' hw' hs => hl ⟨w', hw', hs⟩
      have hw : w.SetsCC i := by
        obtain ⟨w', hw', hs⟩ := h
        rcases List.mem_cons.mp hw' with rfl | hw'
        · exact hs
        · exact absurd hs (hn w' hw')
      rw [Write.ccBit_applyWrites_of_none ws _ hn, Write.ccBit_applyWrites_of_none ws _ hn]
      rcases w with @⟨n, dst, v⟩
      cases dst with
      | fcc m => rw [Write.ccBit_apply_fcc t m v hw, Write.ccBit_apply_fcc t' m v hw]
      | _ => exact hw.elim

/-- A condition code some write of the list sets is, after the list, its value in any state where
the (full-size) writes hold. -/
theorem Write.cc_applyWrites_holds {i : Nat} (ws : List Write) (hs : ∃ w ∈ ws, w.SetsCC i)
    (hf : ∀ w ∈ ws, w.Full) (t u : RamState) (hu : Write.AllHold u ws) :
    ccBit i (applyWrites t ws) = ccBit i u := by
  have hall := Write.allHold_iff.mp hu
  apply applyWrites_obs (ccBit i) (ccBit i u)
  · intro w hwm t'
    by_cases hset : w.SetsCC i
    · refine .inr ?_
      rcases w with @⟨n, dst, v⟩
      cases dst with
      | fcc m =>
        have hn : n = 4 := hf _ hwm
        subst hn
        have hv := hall _ hwm
        simp only [Operand.read_fcc] at hv
        have hm : m.getLsbD i = true := hset
        rw [Write.ccBit_apply_fcc t' m v hset, BitVec.setWidth_eq, ← hv]
        simp [ccBit, BitVec.getLsbD_and, hm]
      | _ => exact hset.elim
    · exact .inl (Write.ccBit_apply_of_not t' w hset)
  · obtain ⟨w, hwm, hset⟩ := hs
    refine .inr ⟨w, hwm, fun t' => ?_⟩
    rcases w with @⟨n, dst, v⟩
    cases dst with
    | fcc m =>
      have hn : n = 4 := hf _ hwm
      subst hn
      have hv := hall _ hwm
      simp only [Operand.read_fcc] at hv
      have hm : m.getLsbD i = true := hset
      rw [Write.ccBit_apply_fcc t' m v hset, BitVec.setWidth_eq, ← hv]
      simp [ccBit, BitVec.getLsbD_and, hm]
    | _ => exact hset.elim

/-! ### Observational agreement -/

/-- `t` and `t'` agree on everything an instruction effect reads: the general-purpose registers,
every byte of memory (as `memByte` reads it), the vector registers, the bits of RFLAGS other
than the six status flags (DF among them), MXCSR, the x87 state (the physical registers, the
status word without its condition codes, the tag and control words and the last-instruction
pointers) and the code segment register (whose selector the x87 instructions record). Not the x87
condition codes C0–C3: most x87 instructions leave them undefined, so, like the status flags,
they are not part of what composition tracks (`Operand.Visible`). -/
structure Obs (t t' : RamState) : Prop where
  gpr : t.GPR = t'.GPR
  mem : ∀ x, memByte t.external x = memByte t'.external x
  zmm : t.ZMM = t'.ZMM
  rflags : clearStatusFlags t.RFLAGS = clearStatusFlags t'.RFLAGS
  mxcsr : t.MXCSR = t'.MXCSR
  fpr : t.FP87 = t'.FP87
  fsw : fswRest t.FP87_Status = fswRest t'.FP87_Status
  ftw : t.FP87_Tag_Word = t'.FP87_Tag_Word
  fcw : t.FP87_Control = t'.FP87_Control
  fpuPtr : fpuPtrOf t = fpuPtrOf t'
  cs : t.CS = t'.CS

theorem Obs.refl (t : RamState) : Obs t t :=
  ⟨rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Obs.symm {t t' : RamState} (h : Obs t t') : Obs t' t :=
  ⟨h.gpr.symm, fun x => (h.mem x).symm, h.zmm.symm, h.rflags.symm, h.mxcsr.symm, h.fpr.symm,
    h.fsw.symm, h.ftw.symm, h.fcw.symm, h.fpuPtr.symm, h.cs.symm⟩

theorem Obs.trans {t t' t'' : RamState} (h : Obs t t') (h' : Obs t' t'') : Obs t t'' :=
  ⟨h.gpr.trans h'.gpr, fun x => (h.mem x).trans (h'.mem x), h.zmm.trans h'.zmm,
    h.rflags.trans h'.rflags, h.mxcsr.trans h'.mxcsr, h.fpr.trans h'.fpr, h.fsw.trans h'.fsw,
    h.ftw.trans h'.ftw, h.fcw.trans h'.fcw, h.fpuPtr.trans h'.fpuPtr, h.cs.trans h'.cs⟩

/-- Observationally equal states have the same direction flag. -/
theorem Obs.dfBit {t t' : RamState} (h : Obs t t') : dfBit t.RFLAGS = dfBit t'.RFLAGS := by
  have := congrArg X86Proofs.dfBit h.rflags
  simpa only [dfBit_clearStatusFlags] using this

/-- Observationally equal states read the same operands (all but the x87 condition codes). -/
theorem Obs.read {t t' : RamState} (h : Obs t t') {n : Nat} (op : Operand n) (hv : op.Visible) :
    op.read t = op.read t' := by
  cases op with
  | reg r => simp [Operand.read, h.gpr]
  | mem a => exact memLoad_congr fun i _ => h.mem _
  | xmm r => simp [Operand.read, h.zmm]
  | regHigh r => simp [Operand.read, h.gpr]
  | mxcsr => simp [Operand.read, h.mxcsr]
  | df => simp [Operand.read, h.dfBit]
  | fpr r => simp [Operand.read, h.fpr]
  | mmx r => simp [Operand.read, h.fpr]
  | fsw => simp [Operand.read, h.fsw]
  | ftw => simp [Operand.read, h.ftw]
  | fcw => simp [Operand.read, h.fcw]
  | fpuPtr => simp [Operand.read, h.fpuPtr]
  | fcc m => exact hv.elim

section ObsRead

variable {t t' : RamState} (h : Obs t t') {n : Nat}
include h

/-! `Obs.read` for each kind of operand an effect reads, without the visibility side condition
(the form `effect_local` rewrites with). -/

theorem Obs.read_reg (r : BitVec 5) : (Operand.reg r : Operand n).read t = (Operand.reg r).read
    t' :=
  h.read _ trivial
theorem Obs.read_mem (a : BitVec 64) : (Operand.mem a : Operand n).read t = (Operand.mem a).read
    t' :=
  h.read _ trivial
theorem Obs.read_xmm (r : BitVec 5) : (Operand.xmm r : Operand n).read t = (Operand.xmm r).read
    t' :=
  h.read _ trivial
theorem Obs.read_regHigh (r : BitVec 5) :
    (Operand.regHigh r : Operand n).read t = (Operand.regHigh r).read t' := h.read _ trivial
theorem Obs.read_mxcsr : (Operand.mxcsr : Operand n).read t = Operand.mxcsr.read t' :=
  h.read _ trivial
theorem Obs.read_df : (Operand.df : Operand n).read t = Operand.df.read t' := h.read _ trivial
theorem Obs.read_fpr (r : BitVec 3) : (Operand.fpr r : Operand n).read t = (Operand.fpr r).read
    t' :=
  h.read _ trivial
theorem Obs.read_mmx (r : BitVec 3) : (Operand.mmx r : Operand n).read t = (Operand.mmx r).read
    t' :=
  h.read _ trivial
theorem Obs.read_fsw : (Operand.fsw : Operand n).read t = Operand.fsw.read t' := h.read _ trivial
theorem Obs.read_ftw : (Operand.ftw : Operand n).read t = Operand.ftw.read t' := h.read _ trivial
theorem Obs.read_fcw : (Operand.fcw : Operand n).read t = Operand.fcw.read t' := h.read _ trivial
theorem Obs.read_fpuPtr : (Operand.fpuPtr : Operand n).read t = Operand.fpuPtr.read t' :=
  h.read _ trivial
theorem Obs.read_gpr8 (r : BitVec 5) (rex : Bool) :
    (Operand.gpr8 r rex).read t = (Operand.gpr8 r rex).read t' :=
  h.read _ (Operand.visible_gpr8 r rex)
theorem Obs.read_byteReg (r : BitVec 3) : (Operand.byteReg r).read t = (Operand.byteReg r).read
    t' :=
  h.read _ (Operand.visible_byteReg r)

end ObsRead

/-- Observationally equal states give the same operand addresses. -/
theorem AddrMode.addr_obs {t t' : RamState} (h : Obs t t') (am : AddrMode) (nxt : BitVec 64) :
    am.addr t nxt = am.addr t' nxt := by
  unfold AddrMode.addr
  split <;> simp [reg64, h.gpr]

/-- Observationally equal states give the same operand addresses at address size 32. -/
theorem AddrMode.addr32_obs {t t' : RamState} (h : Obs t t') (am : AddrMode) (nxt : BitVec 64) :
    am.addr32 t nxt = am.addr32 t' nxt := by
  simp only [AddrMode.addr32, AddrMode.addr_obs h]

private theorem memByte_insert (m : Ram) (a x : BitVec 64) (b : UInt8) :
    memByte (m.insert a b) x = if a = x then b else memByte m x := by
  simp only [memByte, PhysicalMemory.read, Std.ExtHashMap.getElem?_insert]
  by_cases h : a = x <;> simp [h]

private theorem memByte_memStore_congr {m m' : Ram} (h : ∀ x, memByte m x = memByte m' x)
    (a : BitVec 64) {n : Nat} (v : BitVec n) (x : BitVec 64) :
    memByte (memStore m a v) x = memByte (memStore m' a v) x := by
  rw [memStore_eq_foldl, memStore_eq_foldl]
  generalize List.range (n / 8) = items
  induction items generalizing m m' with
  | nil => exact h x
  | cons j items ih =>
    apply ih
    intro y
    rw [memByte_insert, memByte_insert, h]

/-- Writing the same value keeps states observationally equal. -/
theorem Obs.write {t t' : RamState} (h : Obs t t') {n : Nat} (op : Operand n) (v : BitVec n) :
    Obs (op.write t v) (op.write t' v) := by
  cases op with
  | reg r => exact { h with gpr := by simp [Operand.write, h.gpr] }
  | mem a => exact { h with mem := memByte_memStore_congr h.mem a v }
  | xmm r => exact { h with zmm := by simp [Operand.write, h.zmm] }
  | regHigh r => exact { h with gpr := by simp [Operand.write, h.gpr] }
  | mxcsr => exact { h with mxcsr := rfl }
  | df => exact { h with
      rflags := by simp only [Operand.write, clearStatusFlags_setSlice_df, h.rflags] }
  | fpr r => exact { h with fpr := by simp [Operand.write, h.fpr] }
  | mmx r => exact { h with fpr := by simp [Operand.write, h.fpr] }
  | fsw => exact { h with fsw := by simp only [Operand.write, fswRest_fswMerge] }
  | ftw => exact { h with ftw := rfl }
  | fcw => exact { h with fcw := rfl }
  | fpuPtr => exact { h with fpuPtr := by simp [Operand.write, fpuPtrOf] }
  | fcc m => exact { h with fsw := by simpa only [Operand.write, fswRest_fswSetCC] using h.fsw }

theorem Obs.applyWrites {t t' : RamState} (h : Obs t t') (ws : List Write) :
    Obs (X86Proofs.applyWrites t ws) (X86Proofs.applyWrites t' ws) := by
  induction ws generalizing t t' with
  | nil => exact h
  | cons w ws ih => exact ih (h.write w.dst w.val)

/-! ### Real states after an effect agree with the canonical one -/

private theorem vector32_ext {α : Type} {a b : Vector α (Int.toNat 32)}
    (h : ∀ r : BitVec 5, a[gprIndex r] = b[gprIndex r]) : a = b := by
  apply Vector.ext
  intro k hk
  have := h (BitVec.ofNat 5 k)
  have hk' : k < 32 := hk
  simpa [gprIndex, Nat.mod_eq_of_lt hk'] using this

private theorem zmm_ext {a b : BitVec 512} (h1 : xmmClear a = xmmClear b)
    (h2 : a.setWidth 128 = b.setWidth 128) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hl : i < 128
  · have := congrArg (·.getLsbD i) h2
    simpa [BitVec.getLsbD_setWidth, hl] using this
  · have := congrArg (·.getLsbD i) h1
    simpa [xmmClear, getLsbD_xmmMerge, hl] using this

private theorem write_component_reg {w : Write} {r : BitVec 5} (hc : w.component = .reg r)
    (hf : w.Full) : ∃ v : BitVec 64, w = ⟨(Operand.reg r : Operand 64), v⟩ := by
  rcases w with @⟨n, dst, val⟩
  cases dst with
  | reg r' =>
    simp only [Write.Full, Operand.Full] at hf
    subst hf
    simp only [Write.component, Operand.component, Component.reg.injEq] at hc
    subst hc
    exact ⟨val, rfl⟩
  | mem a => simp [Write.component, Operand.component] at hc
  | xmm r' => simp [Write.component, Operand.component] at hc
  | regHigh r' => exact hf.elim
  | mxcsr => simp [Write.component, Operand.component] at hc
  | df => simp [Write.component, Operand.component] at hc
  | _ => simp [Write.component, Operand.component] at hc

private theorem write_component_xmm {w : Write} {r : BitVec 5} (hc : w.component = .xmm r)
    (hf : w.Full) : ∃ v : BitVec 128, w = ⟨(Operand.xmm r : Operand 128), v⟩ := by
  rcases w with @⟨n, dst, val⟩
  cases dst with
  | xmm r' =>
    simp only [Write.Full, Operand.Full] at hf
    subst hf
    simp only [Write.component, Operand.component, Component.xmm.injEq] at hc
    subst hc
    exact ⟨val, rfl⟩
  | mem a => simp [Write.component, Operand.component] at hc
  | reg r' => simp [Write.component, Operand.component] at hc
  | regHigh r' => simp [Write.component, Operand.component] at hc
  | mxcsr => simp [Write.component, Operand.component] at hc
  | df => simp [Write.component, Operand.component] at hc
  | _ => simp [Write.component, Operand.component] at hc

private theorem write_component_mxcsr {w : Write} (hc : w.component = .mxcsr)
    (hf : w.Full) : ∃ v : BitVec 32, w = ⟨(Operand.mxcsr : Operand 32), v⟩ := by
  rcases w with @⟨n, dst, val⟩
  cases dst with
  | mxcsr =>
    simp only [Write.Full, Operand.Full] at hf
    subst hf
    exact ⟨val, rfl⟩
  | _ => simp [Write.component, Operand.component] at hc

private theorem write_component_df {w : Write} (hc : w.component = .df)
    (hf : w.Full) : ∃ v : BitVec 1, w = ⟨(Operand.df : Operand 1), v⟩ := by
  rcases w with @⟨n, dst, val⟩
  cases dst with
  | df =>
    simp only [Write.Full, Operand.Full] at hf
    subst hf
    exact ⟨val, rfl⟩
  | _ => simp [Write.component, Operand.component] at hc

private theorem write_component_fpr {w : Write} {r : BitVec 3} (hc : w.component = .fpr r)
    (hf : w.Full) : ∃ v : BitVec 80, w = ⟨(Operand.fpr r : Operand 80), v⟩ := by
  rcases w with @⟨n, dst, val⟩
  cases dst with
  | fpr r' =>
    simp only [Write.Full, Operand.Full] at hf
    subst hf
    simp only [Write.component, Operand.component, Component.fpr.injEq] at hc
    subst hc
    exact ⟨val, rfl⟩
  | mmx r' => exact hf.elim
  | _ => simp [Write.component, Operand.component] at hc

private theorem write_component_fsw {w : Write} (hc : w.component = .fsw)
    (hf : w.Full) : ∃ v : BitVec 16, w = ⟨(Operand.fsw : Operand 16), v⟩ := by
  rcases w with @⟨n, dst, val⟩
  cases dst with
  | fsw =>
    simp only [Write.Full, Operand.Full] at hf
    subst hf
    exact ⟨val, rfl⟩
  | _ => simp [Write.component, Operand.component] at hc

private theorem write_component_ftw {w : Write} (hc : w.component = .ftw)
    (hf : w.Full) : ∃ v : BitVec 16, w = ⟨(Operand.ftw : Operand 16), v⟩ := by
  rcases w with @⟨n, dst, val⟩
  cases dst with
  | ftw =>
    simp only [Write.Full, Operand.Full] at hf
    subst hf
    exact ⟨val, rfl⟩
  | _ => simp [Write.component, Operand.component] at hc

private theorem write_component_fcw {w : Write} (hc : w.component = .fcw)
    (hf : w.Full) : ∃ v : BitVec 16, w = ⟨(Operand.fcw : Operand 16), v⟩ := by
  rcases w with @⟨n, dst, val⟩
  cases dst with
  | fcw =>
    simp only [Write.Full, Operand.Full] at hf
    subst hf
    exact ⟨val, rfl⟩
  | _ => simp [Write.component, Operand.component] at hc

private theorem write_component_fpuPtr {w : Write} (hc : w.component = .fpuPtr)
    (hf : w.Full) : ∃ v : BitVec 171, w = ⟨(Operand.fpuPtr : Operand 171), v⟩ := by
  rcases w with @⟨n, dst, val⟩
  cases dst with
  | fpuPtr =>
    simp only [Write.Full, Operand.Full] at hf
    subst hf
    exact ⟨val, rfl⟩
  | _ => simp [Write.component, Operand.component] at hc

private theorem vector8_ext {α : Type} {a b : Vector α (Int.toNat 8)}
    (h : ∀ r : BitVec 3, a[fprIndex r] = b[fprIndex r]) : a = b := by
  apply Vector.ext
  intro k hk
  have := h (BitVec.ofNat 3 k)
  have hk' : k < 8 := hk
  simpa [fprIndex, Nat.mod_eq_of_lt hk'] using this

/-- Applying an effect's writes to a state observationally equal to its start state gives one
observationally equal to its end state. -/
theorem Effect.Holds.obs {ε : Effect} {t u u' : RamState} (h : ε.Holds u u') (ho : Obs t u)
    (hf : ∀ w ∈ ε.writes, w.Full) : Obs (applyWrites t ε.writes) u' := by
  have hw := Write.allHold_iff.mp h.writes
  have hrest := h.agrees.rest
  refine ⟨?_, fun x => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- registers
    apply vector32_ext
    intro r
    let o : RamState → BitVec 64 := fun t => (Operand.reg r : Operand 64).read t
    have key : o (applyWrites t ε.writes) = o u' := by
      apply applyWrites_obs o (o u')
      · intro w hwm t
        rcases w with @⟨n, dst, val⟩
        cases dst with
        | reg r' =>
          have hn : n = 64 := hf _ hwm
          subst hn
          by_cases he : r' = r
          · subst he
            refine .inr ?_
            simp only [o, Write.apply_mk, Operand.write_reg64, Operand.read_reg64]
            simpa using (hw _ hwm).symm
          · exact .inl (Operand.read_write_reg_of_ne t he val)
        | mem a => exact .inl rfl
        | xmm r' => exact .inl rfl
        | regHigh r' => exact (hf _ hwm).elim
        | mxcsr => exact .inl rfl
        | df => exact .inl rfl
        | _ => exact .inl rfl
      · by_cases hc : Component.reg r ∈ ε.components
        · rcases Effect.mem_components.mp hc with ⟨w, hwm, hwc⟩ | ⟨-, h'⟩ | h'
          · obtain ⟨v, rfl⟩ := write_component_reg hwc (hf w hwm)
            refine .inr ⟨_, hwm, fun t => ?_⟩
            simp only [o, Write.apply_mk, Operand.write_reg64, Operand.read_reg64]
            simpa using (hw _ hwm).symm
          · cases h'
          · cases h'
        · exact .inl ((ho.read (Operand.reg r : Operand 64) trivial).trans
            (h.agrees.read hc).symm)
    simpa [o, Operand.read_reg64] using key
  · -- memory
    let o : RamState → UInt8 := fun t => memByte t.external x
    have byteOf : ∀ {n : Nat} (a : BitVec 64) (v : BitVec n), n % 8 = 0 →
        (Operand.mem a : Operand n).read u' = v → ∀ i < n / 8, a + BitVec.ofNat 64 i = x →
        ∀ t, o ((Operand.mem a : Operand n).write t v) = o u' := by
      intro n a v _ hv i hi hx t
      obtain ⟨j, hj, hjx, hst⟩ := memStore_getElem?_cover t.external a v x ⟨i, hi, hx⟩
      subst hjx
      simp only [o, Operand.write, memByte, PhysicalMemory.read]
      rw [hst]
      have := storedByte_memLoad u'.external a j hj
      simp only [Operand.read] at hv
      rw [hv] at this
      simpa [memByte, PhysicalMemory.read] using this
    show o (applyWrites t ε.writes) = o u'
    apply applyWrites_obs o (o u')
    · intro w hwm t
      rcases w with @⟨n, dst, val⟩
      cases dst with
      | reg r => exact .inl rfl
      | xmm r => exact .inl rfl
      | regHigh r => exact .inl rfl
      | mxcsr => exact .inl rfl
      | df => exact .inl rfl
      | mem a =>
        have h8 : n % 8 = 0 := hf _ hwm
        by_cases hcov : ∃ i < n / 8, a + BitVec.ofNat 64 i = x
        · obtain ⟨i, hi, hx⟩ := hcov
          exact .inr (byteOf a val h8 (hw _ hwm) i hi hx t)
        · refine .inl ?_
          simp only [o, Write.apply_mk, Operand.write, memByte, PhysicalMemory.read]
          rw [memStore_getElem?_of_ne _ _ _ _ fun i hi he => hcov ⟨i, hi, he⟩]
      | _ => exact .inl rfl
    · by_cases hcov : ∃ c ∈ ε.components, c.Covers x
      · obtain ⟨c, hc, hcx⟩ := hcov
        rcases Effect.mem_components.mp hc with ⟨w, hwm, rfl⟩ | ⟨-, rfl⟩ | rfl
        · rcases w with @⟨n, dst, val⟩
          cases dst with
          | reg r => exact hcx.elim
          | xmm r => exact hcx.elim
          | regHigh r => exact hcx.elim
          | mxcsr => exact hcx.elim
          | df => exact hcx.elim
          | mem a =>
            obtain ⟨i, hi, hx⟩ := hcx
            have h8 : n % 8 = 0 := hf _ hwm
            exact .inr ⟨_, hwm, byteOf a val h8 (hw _ hwm) i hi hx.symm⟩
          | _ => exact hcx.elim
        · exact hcx.elim
        · exact hcx.elim
      · refine .inl ((ho.mem x).trans ?_)
        simp only [o, memByte, PhysicalMemory.read]
        rw [h.agrees.byte fun c hc hcx => hcov ⟨c, hc, hcx⟩]
  · -- vector registers
    have hz : u'.ZMM.map xmmClear = u.ZMM.map xmmClear := by
      have := congrArg (fun t => t.ZMM) hrest
      simpa [fixedPart] using this
    apply vector32_ext
    intro r
    apply zmm_ext
    · -- the upper bits: no write changes them
      let o : RamState → BitVec 512 := fun t => xmmClear t.ZMM[gprIndex r]
      have key : o (applyWrites t ε.writes) = o t := by
        apply applyWrites_obs o (o t) _ _ _ (.inl rfl)
        intro w _ t'
        rcases w with @⟨n, dst, val⟩
        cases dst with
        | reg r' => exact .inl rfl
        | mem a => exact .inl rfl
        | regHigh r' => exact .inl rfl
        | mxcsr => exact .inl rfl
        | df => exact .inl rfl
        | xmm r' =>
          refine .inl ?_
          simp only [o, Write.apply_mk, Operand.write]
          by_cases he : r' = r
          · subst he
            simp [xmmIndex, gprIndex]
          · have hi : (xmmIndex r').val ≠ (gprIndex r).val := fun e =>
              he (BitVec.eq_of_toNat_eq e)
            simp [hi]
        | _ => exact .inl rfl
      have hu : xmmClear u'.ZMM[gprIndex r] = xmmClear u.ZMM[gprIndex r] := by
        have := congrArg (·[gprIndex r]) hz
        simpa using this
      simp only [o] at key
      rw [key, ho.zmm, hu]
    · -- the XMM part: the last write, or unchanged
      let o : RamState → BitVec 128 := fun t => (Operand.xmm r : Operand 128).read t
      have key : o (applyWrites t ε.writes) = o u' := by
        apply applyWrites_obs o (o u')
        · intro w hwm t
          rcases w with @⟨n, dst, val⟩
          cases dst with
          | reg r' => exact .inl rfl
          | mem a => exact .inl rfl
          | regHigh r' => exact .inl rfl
          | mxcsr => exact .inl rfl
          | df => exact .inl rfl
          | xmm r' =>
            have hn : n = 128 := hf _ hwm
            subst hn
            by_cases he : r' = r
            · subst he
              refine .inr ?_
              have := hw _ hwm
              simp only [o, Write.apply_mk, Operand.write, Operand.read] at this ⊢
              simpa using this.symm
            · refine .inl ?_
              have hi : (xmmIndex r').val ≠ (xmmIndex r).val := fun e =>
                he (BitVec.eq_of_toNat_eq e)
              simp [o, Write.apply_mk, Operand.write, Operand.read, hi]
          | _ => exact .inl rfl
        · by_cases hc : Component.xmm r ∈ ε.components
          · rcases Effect.mem_components.mp hc with ⟨w, hwm, hwc⟩ | ⟨-, h'⟩ | h'
            · obtain ⟨v, rfl⟩ := write_component_xmm hwc (hf w hwm)
              refine .inr ⟨_, hwm, fun t => ?_⟩
              have := hw _ hwm
              simp only [o, Write.apply_mk, Operand.write, Operand.read] at this ⊢
              simpa using this.symm
            · cases h'
            · cases h'
          · exact .inl ((ho.read (Operand.xmm r : Operand 128) trivial).trans
              (h.agrees.read_xmm hc).symm)
      simpa [o, Operand.read, xmmIndex, gprIndex] using key
  · -- non-status RFLAGS bits: DF is the last write or unchanged, the others are unchanged
    have := congrArg (fun t => t.RFLAGS) hrest
    simp only [fixedPart] at this
    apply eq_of_clearDirectionFlag_eq
    · have hc := congrArg clearDirectionFlag ho.rflags
      rw [applyWrites_RFLAGS, hc, this]
    · simp only [dfBit_clearStatusFlags]
      let o : RamState → BitVec 1 := fun t => dfBit t.RFLAGS
      show o (applyWrites t ε.writes) = o u'
      apply applyWrites_obs o (o u')
      · intro w hwm t
        rcases w with @⟨n, dst, val⟩
        cases dst with
        | df =>
          have hn : n = 1 := hf _ hwm
          subst hn
          refine .inr ?_
          have := hw _ hwm
          simp only [o, Write.apply_mk, Operand.write_df, Operand.read_df, dfBit_setSlice_df]
            at this ⊢
          exact this.symm
        | _ => exact .inl rfl
      · by_cases hc : Component.df ∈ ε.components
        · rcases Effect.mem_components.mp hc with ⟨w, hwm, hwc⟩ | ⟨-, h'⟩ | h'
          · obtain ⟨v, rfl⟩ := write_component_df hwc (hf w hwm)
            refine .inr ⟨_, hwm, fun t => ?_⟩
            have := hw _ hwm
            simp only [o, Write.apply_mk, Operand.write_df, Operand.read_df, dfBit_setSlice_df]
              at this ⊢
            exact this.symm
          · cases h'
          · cases h'
        · exact .inl (ho.dfBit.trans (h.agrees.df hc).symm)
  · -- MXCSR: the last write, or unchanged
    let o : RamState → BitVec 32 := fun t => t.MXCSR
    show o (applyWrites t ε.writes) = o u'
    apply applyWrites_obs o (o u')
    · intro w hwm t
      rcases w with @⟨n, dst, val⟩
      cases dst with
      | mxcsr =>
        have hn : n = 32 := hf _ hwm
        subst hn
        refine .inr ?_
        have := hw _ hwm
        simp only [o, Write.apply_mk, Operand.write_mxcsr, Operand.read_mxcsr] at this ⊢
        exact this.symm
      | _ => exact .inl rfl
    · by_cases hc : Component.mxcsr ∈ ε.components
      · rcases Effect.mem_components.mp hc with ⟨w, hwm, hwc⟩ | ⟨-, h'⟩ | h'
        · obtain ⟨v, rfl⟩ := write_component_mxcsr hwc (hf w hwm)
          refine .inr ⟨_, hwm, fun t => ?_⟩
          have := hw _ hwm
          simp only [o, Write.apply_mk, Operand.write_mxcsr, Operand.read_mxcsr] at this ⊢
          exact this.symm
        · cases h'
        · cases h'
      · exact .inl (ho.mxcsr.trans (h.agrees.mxcsr hc).symm)
  · -- the x87 registers: each the last write, or unchanged
    apply vector8_ext
    intro r
    let o : RamState → BitVec 80 := fun t => t.FP87[fprIndex r]
    show o (applyWrites t ε.writes) = o u'
    apply applyWrites_obs o (o u')
    · intro w hwm t
      rcases w with @⟨n, dst, val⟩
      cases dst with
      | fpr r' =>
        have hn : n = 80 := hf _ hwm
        subst hn
        by_cases he : r' = r
        · subst he
          refine .inr ?_
          have := hw _ hwm
          simp only [o, Write.apply_mk, Operand.write_fpr, Operand.read_fpr] at this ⊢
          simpa using this.symm
        · refine .inl ?_
          have hi : (fprIndex r').val ≠ (fprIndex r).val := fun e =>
            he (BitVec.eq_of_toNat_eq e)
          simp [o, Write.apply_mk, Operand.write_fpr, hi]
      | mmx r' => exact (hf _ hwm).elim
      | _ => exact .inl rfl
    · by_cases hc : Component.fpr r ∈ ε.components
      · rcases Effect.mem_components.mp hc with ⟨w, hwm, hwc⟩ | ⟨-, h'⟩ | h'
        · obtain ⟨v, rfl⟩ := write_component_fpr hwc (hf w hwm)
          refine .inr ⟨_, hwm, fun t => ?_⟩
          have := hw _ hwm
          simp only [o, Write.apply_mk, Operand.write_fpr, Operand.read_fpr] at this ⊢
          simpa using this.symm
        · cases h'
        · cases h'
      · exact .inl ((congrArg (·[fprIndex r]) ho.fpr).trans (h.agrees.fpr hc).symm)
  · -- the x87 status word without the condition codes: the last write, or unchanged
    let o : RamState → BitVec 16 := fun t => fswRest t.FP87_Status
    show o (applyWrites t ε.writes) = o u'
    apply applyWrites_obs o (o u')
    · intro w hwm t
      rcases w with @⟨n, dst, val⟩
      cases dst with
      | fsw =>
        have hn : n = 16 := hf _ hwm
        subst hn
        refine .inr ?_
        have := hw _ hwm
        simp only [o, Write.apply_mk, Operand.write_fsw, Operand.read_fsw, fswRest_fswMerge]
          at this ⊢
        rw [← this, fswRest_fswRest]
      | fcc m => exact .inl (by simp only [o, Write.apply_mk, Operand.write, fswRest_fswSetCC])
      | _ => exact .inl rfl
    · by_cases hc : Component.fsw ∈ ε.components
      · rcases Effect.mem_components.mp hc with ⟨w, hwm, hwc⟩ | ⟨-, h'⟩ | h'
        · obtain ⟨v, rfl⟩ := write_component_fsw hwc (hf w hwm)
          refine .inr ⟨_, hwm, fun t => ?_⟩
          have := hw _ hwm
          simp only [o, Write.apply_mk, Operand.write_fsw, Operand.read_fsw, fswRest_fswMerge]
            at this ⊢
          rw [← this, fswRest_fswRest]
        · cases h'
        · cases h'
      · exact .inl (ho.fsw.trans (h.agrees.fsw hc).symm)
  · -- the x87 tag word: the last write, or unchanged
    let o : RamState → BitVec 16 := fun t => t.FP87_Tag_Word
    show o (applyWrites t ε.writes) = o u'
    apply applyWrites_obs o (o u')
    · intro w hwm t
      rcases w with @⟨n, dst, val⟩
      cases dst with
      | ftw =>
        have hn : n = 16 := hf _ hwm
        subst hn
        refine .inr ?_
        have := hw _ hwm
        simp only [o, Write.apply_mk, Operand.write_ftw, Operand.read_ftw] at this ⊢
        exact this.symm
      | _ => exact .inl rfl
    · by_cases hc : Component.ftw ∈ ε.components
      · rcases Effect.mem_components.mp hc with ⟨w, hwm, hwc⟩ | ⟨-, h'⟩ | h'
        · obtain ⟨v, rfl⟩ := write_component_ftw hwc (hf w hwm)
          refine .inr ⟨_, hwm, fun t => ?_⟩
          have := hw _ hwm
          simp only [o, Write.apply_mk, Operand.write_ftw, Operand.read_ftw] at this ⊢
          exact this.symm
        · cases h'
        · cases h'
      · exact .inl (ho.ftw.trans (h.agrees.ftw hc).symm)
  · -- the x87 control word: the last write, or unchanged
    let o : RamState → BitVec 16 := fun t => t.FP87_Control
    show o (applyWrites t ε.writes) = o u'
    apply applyWrites_obs o (o u')
    · intro w hwm t
      rcases w with @⟨n, dst, val⟩
      cases dst with
      | fcw =>
        have hn : n = 16 := hf _ hwm
        subst hn
        refine .inr ?_
        have := hw _ hwm
        simp only [o, Write.apply_mk, Operand.write_fcw, Operand.read_fcw] at this ⊢
        exact this.symm
      | _ => exact .inl rfl
    · by_cases hc : Component.fcw ∈ ε.components
      · rcases Effect.mem_components.mp hc with ⟨w, hwm, hwc⟩ | ⟨-, h'⟩ | h'
        · obtain ⟨v, rfl⟩ := write_component_fcw hwc (hf w hwm)
          refine .inr ⟨_, hwm, fun t => ?_⟩
          have := hw _ hwm
          simp only [o, Write.apply_mk, Operand.write_fcw, Operand.read_fcw] at this ⊢
          exact this.symm
        · cases h'
        · cases h'
      · exact .inl (ho.fcw.trans (h.agrees.fcw hc).symm)
  · -- the x87 last-instruction pointers: the last write, or unchanged
    let o : RamState → BitVec 171 := fun t => fpuPtrOf t
    show o (applyWrites t ε.writes) = o u'
    apply applyWrites_obs o (o u')
    · intro w hwm t
      rcases w with @⟨n, dst, val⟩
      cases dst with
      | fpuPtr =>
        have hn : n = 171 := hf _ hwm
        subst hn
        refine .inr ?_
        have := hw _ hwm
        simp only [o, Write.apply_mk, Operand.write_fpuPtr, Operand.read_fpuPtr,
          fpuPtrOf_setFpuPtr] at this ⊢
        exact this.symm
      | _ => exact .inl rfl
    · by_cases hc : Component.fpuPtr ∈ ε.components
      · rcases Effect.mem_components.mp hc with ⟨w, hwm, hwc⟩ | ⟨-, h'⟩ | h'
        · obtain ⟨v, rfl⟩ := write_component_fpuPtr hwc (hf w hwm)
          refine .inr ⟨_, hwm, fun t => ?_⟩
          have := hw _ hwm
          simp only [o, Write.apply_mk, Operand.write_fpuPtr, Operand.read_fpuPtr,
          fpuPtrOf_setFpuPtr] at this ⊢
          exact this.symm
        · cases h'
        · cases h'
      · exact .inl (ho.fpuPtr.trans (h.agrees.fpuPtr hc).symm)
  · -- the code segment: no write changes it
    have hcs : u'.CS = u.CS := congrArg (fun t => t.CS) hrest
    rw [applyWrites_CS, ho.cs, hcs]

/-! ### The canonical state after an effect -/

/-- The flags after `e` from `s`, the undefined ones set to `b`. -/
@[x86_compose] def Effect.flagsAfter (e : Effect) (s : RamState) (b : Bool) : StatusFlags :=
  ⟨(e.flag s .CF).getD b, (e.flag s .PF).getD b, (e.flag s .AF).getD b, (e.flag s .ZF).getD b,
    (e.flag s .SF).getD b, (e.flag s .OF).getD b⟩

theorem Effect.flagsAfter_get (e : Effect) (s : RamState) (b : Bool) (i : StatusFlag) :
    (e.flagsAfter s b).get i = (e.flag s i).getD b := by
  cases i <;> rfl

/-- The canonical state after effect `e` from `s`: the writes applied, the flags set (the
undefined ones to `b`). -/
def Effect.after (e : Effect) (s : RamState) (b : Bool) : RamState :=
  { applyWrites s e.writes with
    RFLAGS := (e.flagsAfter s b).store (applyWrites s e.writes).RFLAGS }

@[x86_compose] theorem Effect.read_after {n : Nat} (e : Effect) (s : RamState) (b : Bool)
    (op : Operand n) : op.read (e.after s b) = op.read (applyWrites s e.writes) := by
  cases op with
  | df => simp only [Operand.read, Effect.after, dfBit_store]
  | _ => rfl

/-- The canonical state keeps the code segment register (no write changes it). -/
@[x86_compose] theorem Effect.after_CS (e : Effect) (s : RamState) (b : Bool) :
    (e.after s b).CS = s.CS :=
  applyWrites_CS s e.writes

/-- MXCSR of the canonical state, as an operand read (the form the effects' writes normalize
in; SSE effects read the field). -/
@[x86_compose] theorem Effect.after_MXCSR (e : Effect) (s : RamState) (b : Bool) :
    (e.after s b).MXCSR = (Operand.mxcsr : Operand 32).read (e.after s b) := by
  simp [Operand.read]

/-- The x87 control word of the canonical state, as an operand read. -/
@[x86_compose] theorem Effect.after_FP87_Control (e : Effect) (s : RamState) (b : Bool) :
    (e.after s b).FP87_Control = (Operand.fcw : Operand 16).read (e.after s b) := by
  simp [Operand.read]

/-- The x87 tag word of the canonical state, as an operand read. -/
@[x86_compose] theorem Effect.after_FP87_Tag_Word (e : Effect) (s : RamState) (b : Bool) :
    (e.after s b).FP87_Tag_Word = (Operand.ftw : Operand 16).read (e.after s b) := by
  simp [Operand.read]

@[x86_compose] theorem Effect.ofRFLAGS_after (e : Effect) (s : RamState) (b : Bool) :
    StatusFlags.ofRFLAGS (e.after s b).RFLAGS = e.flagsAfter s b :=
  StatusFlags.ofRFLAGS_store _ _

theorem Effect.after_obs (e : Effect) (s : RamState) (b : Bool) :
    Obs (e.after s b) (applyWrites s e.writes) :=
  ⟨rfl, fun _ => rfl, rfl, by simp only [Effect.after, clearStatusFlags_store], rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩

/-- A real state after `e` agrees with the canonical one. -/
theorem Effect.Holds.obsAfter {e : Effect} {s s' : RamState} (h : e.Holds s s')
    (hf : ∀ w ∈ e.writes, w.Full) (b : Bool) : Obs (e.after s b) s' :=
  (e.after_obs s b).trans (h.obs (Obs.refl s) hf)

/-- Canonical states built the same way from observationally equal states, with the same
writes, are observationally equal. -/
theorem Effect.after_obs_of {e e' : Effect} {t t' : RamState} (h : Obs t t')
    (hw : e.writes = e'.writes) (b : Bool) : Obs (e.after t b) (e'.after t' b) :=
  ((e.after_obs t b).trans (hw ▸ h.applyWrites e.writes)).trans (e'.after_obs t' b).symm

/-! ### Effects that read only what `Obs` sees -/

/--
`e` reads only the observable state: from observationally equal states it gives the same RIP,
the same writes and the same choice of touching the flags, and each output flag agrees whenever
the old value of that same flag does. All writes have supported sizes (`Write.Full`).
-/
structure Effect.Local (e : RamState → Effect) : Prop where
  rip : ∀ t t', Obs t t' → (e t).rip = (e t').rip
  writes : ∀ t t', Obs t t' → (e t).writes = (e t').writes
  flagsSome : ∀ t t', Obs t t' → (e t).flags.isSome = (e t').flags.isSome
  flag : ∀ t t', Obs t t' → ∀ i, (StatusFlags.ofRFLAGS t.RFLAGS).get i = (StatusFlags.ofRFLAGS t'.RFLAGS).get i →
    (e t).flag t i = (e t').flag t' i
  full : ∀ t, ∀ w ∈ (e t).writes, w.Full

theorem Effect.components_eq {e e' : Effect} (hw : e.writes = e'.writes)
    (hf : e.flags.isSome = e'.flags.isSome) : e.components = e'.components := by
  unfold Effect.components
  rw [hw]
  cases h : e.flags <;> cases h' : e'.flags <;> simp_all

/-- A local effect avoids code at a state if it does at an observationally equal one. -/
theorem Effect.Local.avoids {e : RamState → Effect} (hl : Effect.Local e) {t t' : RamState}
    (ho : Obs t t') {code : CodeMap} (h : (e t).Avoids code) : (e t').Avoids code := by
  unfold Effect.Avoids at *
  rw [← Effect.components_eq (hl.writes t t' ho) (hl.flagsSome t t' ho)]
  exact h

/-- A family of effects `e a`, each local, taken at a parameter `f s` read from the state (e.g. a
shift count in CL) that is the same at observationally equal states, is local. -/
theorem Effect.Local.of_param {α : Type} {e : α → RamState → Effect} {f : RamState → α}
    (hf : ∀ t t', Obs t t' → f t = f t') (hl : ∀ a, Effect.Local (e a)) :
    Effect.Local (fun s => e (f s) s) := by
  refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_, fun t t' h i hi => ?_,
    fun t => (hl _).full t⟩
  · rw [hf t t' h]
    exact (hl _).rip t t' h
  · rw [hf t t' h]
    exact (hl _).writes t t' h
  · rw [hf t t' h]
    exact (hl _).flagsSome t t' h
  · show (e (f t) t).flag t i = (e (f t') t').flag t' i
    rw [hf t t' h]
    exact (hl _).flag t t' h i hi

/-- An effect that leaves the flags and is the same at observationally equal states is local if its
writes are full (a `rep` string instruction's whole loop). -/
theorem Effect.Local.of_congr {e : RamState → Effect}
    (h : ∀ t t', Obs t t' → e t = e t') (hflags : ∀ t, (e t).flags = none)
    (hfull : ∀ t, ∀ w ∈ (e t).writes, w.Full) : Effect.Local e :=
  ⟨fun t t' ho => by rw [h t t' ho], fun t t' ho => by rw [h t t' ho],
    fun t t' ho => by rw [h t t' ho], fun t t' ho i hi => by simp only [Effect.flag, hflags, hi],
    hfull⟩

/-! ### Composition -/

/-- `w` re-read in `fin`: the same location with its value there. -/
@[x86_compose] def Write.reread (fin : RamState) (w : Write) : Write := ⟨w.dst, w.dst.read fin⟩

/-- A register (or MXCSR, DF, or x87) write of `w` is written again by `ws` (and can be
dropped). -/
@[x86_compose] def Write.shadowed (ws : List Write) (w : Write) : Bool :=
  match w.component with
  | .reg r => ws.any fun w' => w'.component == .reg r
  | .xmm r => ws.any fun w' => w'.component == .xmm r
  | .mxcsr => ws.any fun w' => w'.component == .mxcsr
  | .df => ws.any fun w' => w'.component == .df
  | .fpr r => ws.any fun w' => w'.component == .fpr r
  | .fsw => ws.any fun w' => w'.component == .fsw
  | .ftw => ws.any fun w' => w'.component == .ftw
  | .fcw => ws.any fun w' => w'.component == .fcw
  | .fpuPtr => ws.any fun w' => w'.component == .fpuPtr
  | .fcc => ws.any fun w' => w'.component == .fcc
  | _ => false

/-- A comparison of components is the decision of their equality (for symbolic register
numbers, e.g. the x87 stack top). -/
@[x86_compose] theorem Component.beq_eq (a b : Component) : (a == b) = decide (a = b) := rfl

theorem Write.shadowed_spec {ws : List Write} {w : Write} (h : Write.shadowed ws w = true) :
    ∃ w' ∈ ws, w'.component = w.component := by
  unfold Write.shadowed at h
  split at h <;>
  first
  | (rename_i hr
     obtain ⟨w', hw', he⟩ := List.any_eq_true.mp h
     exact ⟨w', hw', by rw [hr]; simpa using he⟩)
  | cases h

/-- A write that sets a condition code is a write of the condition codes. -/
theorem Write.component_of_setsCC {i : Nat} {w : Write} (h : w.SetsCC i) : w.component = .fcc := by
  rcases w with @⟨n, dst, v⟩
  cases dst with
  | fcc m => rfl
  | _ => exact h.elim

/-- No write of `ws` sets a condition code if a condition-code write is not shadowed by `ws`. -/
theorem Write.not_setsCC_of_shadowed {ws : List Write} {n : Nat} {m : BitVec 4} {v : BitVec n}
    (h : Write.shadowed ws ⟨.fcc m, v⟩ = false) (i : Nat) : ∀ w ∈ ws, ¬ w.SetsCC i := by
  intro w hw hs
  have h' : (ws.any fun w' => w'.component == .fcc) = false := h
  have := List.any_eq_false.mp h' w hw
  rw [Write.component_of_setsCC hs] at this
  exact this rfl

/-- The condition codes `m` selects agree if each selected code does. -/
theorem fcc_read_eq {n : Nat} {t t' : RamState} (m : BitVec 4)
    (h : ∀ i, m.getLsbD i = true → ccBit i t = ccBit i t') :
    (Operand.fcc m : Operand n).read t = (Operand.fcc m : Operand n).read t' := by
  simp only [Operand.read]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and]
  by_cases hm : m.getLsbD i = true
  · rw [show (fswCC t.FP87_Status).getLsbD i = ccBit i t from rfl, h i hm]
    rfl
  · simp [hm]

/-- `a` if it equals `b`, else undefined. -/
@[x86_compose] def Effect.pick (a b : Option Bool) : Option Bool := if a = b then a else none

theorem FlagAllows.pick {a b c : Option Bool} {x y : Bool} (ht : x = true → a = c)
    (hf : x = false → b = c) (h : FlagAllows c y) : FlagAllows (Effect.pick a b) y := by
  unfold Effect.pick
  split
  · rename_i hab
    cases x
    · rw [hab, hf rfl]; exact h
    · rw [ht rfl]; exact h
  · trivial

/--
`e₁` then `e₂`, as one effect of the start state `s`: `e₂` is evaluated at the canonical states
after `e₁` (`Effect.after`); `e₁`'s written locations are re-read in the canonical state after
both, except registers `e₂` writes again; each flag is `e₂`'s if the undefined flags of `e₁` do not
change it.
-/
@[x86_compose] def Effect.seq (e₁ e₂ : RamState → Effect) (s : RamState) : Effect :=
  let E := e₁ s
  let m := E.after s true
  let m' := E.after s false
  let F := e₂ m
  let F' := e₂ m'
  let fin := applyWrites m F.writes
  { rip := F.rip
    writes := (E.writes.filter fun w => !Write.shadowed F.writes w).map (Write.reread fin) ++
      F.writes
    flags := if E.flags.isNone && F.flags.isNone then none else
      some (StatusFlagsOutcome.ofFun fun i => Effect.pick (F.flag m i) (F'.flag m' i)) }

theorem Effect.seq_flag (e₁ e₂ : RamState → Effect) (s : RamState) (i : StatusFlag) :
    (Effect.seq e₁ e₂ s).flag s i =
      if (e₁ s).flags.isNone && (e₂ ((e₁ s).after s true)).flags.isNone then
        some ((StatusFlags.ofRFLAGS s.RFLAGS).get i)
      else Effect.pick ((e₂ ((e₁ s).after s true)).flag ((e₁ s).after s true) i)
        ((e₂ ((e₁ s).after s false)).flag ((e₁ s).after s false) i) := by
  by_cases hc : ((e₁ s).flags.isNone && (e₂ ((e₁ s).after s true)).flags.isNone) = true
  · simp only [Effect.seq, hc, ↓reduceIte]
    rfl
  · simp only [Effect.seq, hc]
    exact StatusFlagsOutcome.get_ofFun _ i

/-- The flags of `s'` are as `e` says if each flag is. -/
theorem Effect.flagsHold_of_flag {e : Effect} {s s' : RamState}
    (h : ∀ i, FlagAllows (e.flag s i) ((StatusFlags.ofRFLAGS s'.RFLAGS).get i)) : e.FlagsHold s' := by
  unfold Effect.FlagsHold
  split
  · rename_i fe hfe
    rw [StatusFlagsOutcome.allows_iff]
    intro i
    have := h i
    simp only [Effect.flag, hfe] at this
    exact this
  · trivial

theorem isSome_ite_none {α : Type} (c : Bool) (x : α) :
    (if c = true then none else some x).isSome = !c := by
  cases c <;> rfl

/-- The flag of the canonical state after `e`: the known value, or `b`. -/
theorem Effect.after_flag (e : Effect) (s : RamState) (b : Bool) (i : StatusFlag) :
    (StatusFlags.ofRFLAGS (e.after s b).RFLAGS).get i = (e.flag s i).getD b := by
  rw [Effect.ofRFLAGS_after, Effect.flagsAfter_get]

/-- Soundness of `Effect.seq`: `e₁` from `s` to `s₁` and `e₂` from `s₁` to `s₂` is the composed
effect from `s` to `s₂`. -/
theorem Effect.Holds.seq {e₁ e₂ : RamState → Effect} {s s₁ s₂ : RamState}
    (hl : Effect.Local e₂) (hf : ∀ w ∈ (e₁ s).writes, w.Full) (h₁ : (e₁ s).Holds s s₁)
    (h₂ : (e₂ s₁).Holds s₁ s₂) : (Effect.seq e₁ e₂ s).Holds s s₂ := by
  have hobs := h₁.obsAfter hf
  have hrip := hl.rip _ _ (hobs true)
  have hws := hl.writes _ _ (hobs true)
  have hfs := hl.flagsSome _ _ (hobs true)
  have hfin : Obs (applyWrites ((e₁ s).after s true) (e₂ ((e₁ s).after s true)).writes) s₂ := by
    rw [hws]
    exact h₂.obs (hobs true) (hl.full s₁)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Effect.seq]
    rw [h₂.rip, hrip]
  · rw [Write.allHold_iff]
    simp only [Effect.seq, List.mem_append, List.mem_map]
    rintro w (⟨w₀, hw₀, rfl⟩ | hw)
    · rcases w₀ with @⟨n, dst, v⟩
      by_cases hv : dst.Visible
      · exact (hfin.read dst hv).symm
      · cases dst with
        | fcc m =>
          obtain ⟨hwE, hsh⟩ := List.mem_filter.mp hw₀
          have hsh' : Write.shadowed (e₂ ((e₁ s).after s true)).writes ⟨.fcc m, v⟩ = false := by
            simpa using hsh
          show (Operand.fcc m : Operand n).read s₂ = (Operand.fcc m : Operand n).read _
          apply fcc_read_eq
          intro i hi
          have hnone := Write.not_setsCC_of_shadowed hsh' i
          have hagr : Component.fcc ∉ (e₂ s₁).components := by
            intro hc
            rcases Effect.mem_components.mp hc with ⟨w', hw', hwc⟩ | ⟨-, h'⟩ | h'
            · rw [← hws] at hw'
              have := List.any_eq_false.mp hsh' w' hw'
              rw [hwc] at this
              exact this rfl
            · cases h'
            · cases h'
          have h2 : ccBit i s₂ = ccBit i s₁ := by
            have := h₂.agrees.fcc hagr
            exact congrArg (fun x => x.getLsbD i) this
          rw [h2, Write.ccBit_applyWrites_of_none _ _ hnone]
          exact (Write.cc_applyWrites_holds _ ⟨_, hwE, hi⟩ hf s s₁ h₁.writes).symm
        | _ => exact absurd trivial hv
    · rw [hws] at hw
      exact Write.allHold_iff.mp h₂.writes w hw
  · by_cases hc : ((e₁ s).flags.isNone && (e₂ ((e₁ s).after s true)).flags.isNone) = true
    · simp only [Effect.FlagsHold, Effect.seq, hc, ↓reduceIte]
    · apply Effect.flagsHold_of_flag
      intro i
      rw [Effect.seq_flag]
      simp only [hc]
      let x := (StatusFlags.ofRFLAGS s₁.RFLAGS).get i
      have hx : ∀ b, x = b → (e₂ ((e₁ s).after s b)).flag ((e₁ s).after s b) i =
          (e₂ s₁).flag s₁ i := by
        intro b hb
        apply hl.flag _ _ (hobs b)
        rw [Effect.after_flag]
        have := h₁.flag i
        cases hk : (e₁ s).flag s i with
        | none => simp [← hb, x]
        | some v => rw [hk] at this; simp only [Option.getD_some]; exact this.symm
      exact FlagAllows.pick (hx true) (hx false) (h₂.flag i)
  · apply (h₁.agrees.trans h₂.agrees).mono
    intro c hc
    rw [List.mem_append] at hc
    rw [Effect.mem_components]
    rcases hc with hc | hc
    · rcases Effect.mem_components.mp hc with ⟨w, hw, rfl⟩ | ⟨hs, rfl⟩ | rfl
      · by_cases hsh : Write.shadowed (e₂ ((e₁ s).after s true)).writes w = true
        · obtain ⟨w', hw', he⟩ := Write.shadowed_spec hsh
          exact .inl ⟨w', by simp only [Effect.seq]; exact List.mem_append_right _ hw', he⟩
        · refine .inl ⟨Write.reread (applyWrites ((e₁ s).after s true)
            (e₂ ((e₁ s).after s true)).writes) w, ?_, rfl⟩
          simp only [Effect.seq]
          apply List.mem_append_left
          exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hw, by simpa using hsh⟩)
      · refine .inr (.inl ⟨?_, rfl⟩)
        simp only [Effect.seq]
        split
        · rename_i hc'
          simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc'
          simp [hc'.1] at hs
        · rfl
      · exact .inr (.inr rfl)
    · rcases Effect.mem_components.mp hc with ⟨w, hw, rfl⟩ | ⟨hs, rfl⟩ | rfl
      · rw [← hws] at hw
        exact .inl ⟨w, by simp only [Effect.seq]; exact List.mem_append_right _ hw, rfl⟩
      · refine .inr (.inl ⟨?_, rfl⟩)
        simp only [Effect.seq]
        split
        · rename_i hc'
          simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc'
          rw [← hfs, hc'.2] at hs
          cases hs
        · rfl
      · exact .inr (.inr rfl)

/-- The composition of local effects is local, so blocks compose further. -/
theorem Effect.Local.seq {e₁ e₂ : RamState → Effect} (h₁ : Effect.Local e₁)
    (h₂ : Effect.Local e₂) : Effect.Local (Effect.seq e₁ e₂) := by
  have hm : ∀ t t', Obs t t' → ∀ b, Obs ((e₁ t).after t b) ((e₁ t').after t' b) :=
    fun t t' h b => Effect.after_obs_of h (h₁.writes t t' h) b
  refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_, fun t t' h i hi => ?_,
    fun t w hw => ?_⟩
  · simp only [Effect.seq]
    exact h₂.rip _ _ (hm t t' h true)
  · simp only [Effect.seq]
    have hF := h₂.writes _ _ (hm t t' h true)
    have hfin := (hm t t' h true).applyWrites (e₂ ((e₁ t).after t true)).writes
    rw [h₁.writes t t' h, ← hF]
    congr 1
    apply List.map_congr_left
    intro w hw
    rcases w with @⟨n, dst, v⟩
    by_cases hv : dst.Visible
    · simp only [Write.reread, hfin.read dst hv]
    · cases dst with
      | fcc m =>
        obtain ⟨hwE, hsh⟩ := List.mem_filter.mp hw
        have hsh' : Write.shadowed (e₂ ((e₁ t).after t true)).writes ⟨.fcc m, v⟩ = false := by
          simpa using hsh
        simp only [Write.reread]
        congr 1
        apply fcc_read_eq
        intro i hi
        have hnone := Write.not_setsCC_of_shadowed hsh' i
        rw [Write.ccBit_applyWrites_of_none _ _ hnone, Write.ccBit_applyWrites_of_none _ _ hnone]
        show ccBit i (applyWrites t (e₁ t).writes) = ccBit i (applyWrites t' (e₁ t').writes)
        rw [h₁.writes t t' h]
        exact Write.cc_applyWrites_det _ ⟨_, hwE, hi⟩ t t'
      | _ => exact absurd trivial hv
  · have hc₁ := h₁.flagsSome t t' h
    have hc₂ := h₂.flagsSome _ _ (hm t t' h true)
    simp only [Effect.seq]
    rw [isSome_ite_none, isSome_ite_none]
    simp only [← Option.not_isSome, hc₁, hc₂]
  · rw [Effect.seq_flag, Effect.seq_flag]
    have hc₁ := h₁.flagsSome t t' h
    have hc₂ := h₂.flagsSome _ _ (hm t t' h true)
    simp only [← Option.not_isSome, hc₁, hc₂]
    have hb : ∀ b, (e₂ ((e₁ t).after t b)).flag ((e₁ t).after t b) i =
        (e₂ ((e₁ t').after t' b)).flag ((e₁ t').after t' b) i := fun b =>
      h₂.flag _ _ (hm t t' h b) i (by rw [Effect.after_flag, Effect.after_flag, h₁.flag t t' h i hi])
    rw [hb true, hb false, hi]
  · simp only [Effect.seq, List.mem_append, List.mem_map] at hw
    rcases hw with ⟨w₀, hw₀, rfl⟩ | hw
    · exact h₁.full t w₀ (List.mem_filter.mp hw₀).1
    · exact h₂.full _ w hw

/-! ### Triples -/

/-- The effect of no instructions: RIP as it is, nothing written. -/
@[x86_compose] def Effect.start (s : RamState) : Effect := { rip := s.RIP }

theorem Effect.start_holds (s : RamState) : (Effect.start s).Holds s s :=
  ⟨rfl, trivial, trivial, AgreesExcept.refl _ _⟩

theorem Effect.start_obs (s : RamState) : Obs ((Effect.start s).after s true) s :=
  (Effect.start_holds s).obsAfter (fun _ h => nomatch h) true

namespace Triple

variable [Bindings] {P pre₁ pre₂ : RamState → Prop} {code code₁ code₂ : CodeMap}
  {E E' e₁ e₂ : RamState → Effect}

/-- A block's first instruction, framed into the whole block's code. -/
theorem first (h₁ : Triple pre₁ code₁ (Effect.post e₁)) (hsub : ∀ x ∈ code₁, x ∈ code)
    (hpre : ∀ s, P s → pre₁ s) (hav : ∀ s, P s → (e₁ s).Avoids code) :
    Triple P code (Effect.post e₁) :=
  (h₁.conseq hpre fun _ _ _ h => h).subset_code hsub fun s _ hP hp hc => hp.codeIn (hav s hP) hc

/--
One more instruction after a block: the composed effect `Effect.seq E e₂`. The instruction's
code lies in the block's (`hsub`); after the block so far, its precondition holds and its writes
miss the block's code (`hmid`, which may use that the state after the block agrees with the
canonical one).
-/
theorem seq_block (h₁ : Triple P code (Effect.post E)) (h₂ : Triple pre₂ code₂ (Effect.post e₂))
    (hl : Effect.Local e₂) (hsub : ∀ x ∈ code₂, x ∈ code)
    (hfull : ∀ s, P s → ∀ w ∈ (E s).writes, w.Full)
    (hmid : ∀ s s', P s → (E s).Holds s s' → (∀ b, Obs ((E s).after s b) s') →
      pre₂ s' ∧ (e₂ s').Avoids code) :
    Triple P code (Effect.post fun s => Effect.seq E e₂ s) := by
  intro s hr hc hP
  obtain ⟨n₁, hr₁, hc₁, hp₁⟩ := h₁ s hr hc hP
  obtain ⟨hpre, hav⟩ := hmid _ _ hP hp₁ (hp₁.obsAfter (hfull s hP))
  obtain ⟨n₂, hr₂, -, hp₂⟩ := h₂ _ hr₁ (hc₁.mono hsub) hpre
  refine ⟨n₂ + n₁, ?_⟩
  rw [nextStates_add]
  exact ⟨hr₂, hp₂.codeIn hav hc₁, hp₁.seq hl (hfull s hP) hp₂⟩

/-- `Triple.first` with the rest of the proof as a continuation (for `x86_begin`). -/
theorem block_first {Q : RamState → RamState → Prop}
    (k : Triple P code (Effect.post fun s => e₁ s) → Triple P code Q)
    (h₁ : Triple pre₁ code₁ (Effect.post e₁)) (hsub : ∀ x ∈ code₁, x ∈ code)
    (hpre : ∀ s, P s → pre₁ s) (hav : ∀ s, P s → (e₁ s).Avoids code) : Triple P code Q :=
  k (first h₁ hsub hpre hav)

/-- `Triple.seq_block` with the rest of the proof as a continuation (for `x86_then`). -/
theorem block_then {Q : RamState → RamState → Prop}
    (k : Triple P code (Effect.post fun s => Effect.seq E e₂ s) → Triple P code Q)
    (h₂ : Triple pre₂ code₂ (Effect.post e₂)) (hl : Effect.Local e₂)
    (hsub : ∀ x ∈ code₂, x ∈ code) (hfull : ∀ s, P s → ∀ w ∈ (E s).writes, w.Full)
    (hmid : ∀ s s', P s → (E s).Holds s s' → (∀ b, Obs ((E s).after s b) s') →
      pre₂ s' ∧ (e₂ s').Avoids code) :
    Triple P code (Effect.post E) → Triple P code Q :=
  fun h₁ => k (h₁.seq_block h₂ hl hsub hfull hmid)

end Triple

/-! ### From the composed effect to a stated one -/

/-- Component `c` is kept by effect `e` from `s`: a register `e` writes with its old value. -/
@[x86_compose] def Component.KeptBy (e : Effect) (s : RamState) : Component → Prop
  | .reg r => (⟨(Operand.reg r : Operand 64), (Operand.reg r : Operand 64).read s⟩ : Write) ∈ e.writes
  | _ => False

/-- `b` claims at most what `a` does about a flag. -/
@[x86_compose] def FlagWeaker (a b : Option Bool) : Prop := b = none ∨ b = a

/--
Weakening an effect: the same RIP, a sublist of the writes, flags claimed at most as precisely,
and every component it drops is a register written with its old value.
-/
theorem Effect.Holds.weaken {E E' : Effect} {s s' : RamState} (h : E.Holds s s')
    (hrip : E.rip = E'.rip) (hw : ∀ w ∈ E'.writes, w ∈ E.writes)
    (hfl : ∀ i, FlagWeaker (E.flag s i) (E'.flag s i))
    (hc : ∀ c ∈ E.components, c ∈ E'.components ∨ c.KeptBy E s) : E'.Holds s s' := by
  have hall := Write.allHold_iff.mp h.writes
  refine ⟨h.rip.trans hrip, Write.allHold_iff.mpr fun w hw' => hall w (hw w hw'), ?_, ?_⟩
  · unfold Effect.FlagsHold
    split
    · rename_i fe hfe
      rw [StatusFlagsOutcome.allows_iff]
      intro i
      have := hfl i
      simp only [Effect.flag, hfe] at this
      rcases this with h0 | h0
      · rw [h0]; trivial
      · rw [h0]; exact h.flag i
    · trivial
  · refine h.agrees.narrow fun c hc' hn => ?_
    rcases hc c hc' with h' | h'
    · exact absurd h' hn
    · cases c with
      | reg r =>
        have := hall _ h'
        simpa [Component.Agrees, Operand.read_reg64] using this
      | _ => exact h'.elim

namespace Triple

variable [Bindings] {P : RamState → Prop} {code : CodeMap} {E E' : RamState → Effect}

/-- The end of a block: the composed effect implies the stated one. -/
theorem block_end (h : ∀ s s', P s → (E s).Holds s s' → (E' s).Holds s s') :
    Triple P code (Effect.post E) → Triple P code (Effect.post E') :=
  fun h₁ => h₁.conseq (fun _ h => h) h

end Triple

/-! ### Preconditions after a block -/

section Transport

variable {e : Effect} {s s' : RamState}

@[x86_pre] theorem Effect.Holds.rip_of {p : BitVec 64} (h : e.Holds s s') (hrip : e.rip = p) : s'.RIP = p :=
  h.rip.trans hrip

@[x86_pre] theorem MemReadable.of_holds {a : BitVec 64} {len : Nat} (h : e.Holds s s')
    (hm : MemReadable s a len) : MemReadable s' a len :=
  ⟨hm.low, fun i hi => h.agrees.grow _ (hm.mem i hi)⟩

@[x86_pre] theorem MemWritable.of_holds {a : BitVec 64} {len : Nat} (h : e.Holds s s')
    (hm : MemWritable s a len) : MemWritable s' a len :=
  ⟨hm.low, fun i hi => h.agrees.grow _ (hm.mem i hi), hm.tables⟩

/-- A segment register keeps its readiness and base across an effect: the segment registers are
in `fixedPart`. -/
theorem SegReg.Ready.of_holds {r : SegReg} {base : BitVec 64} (h : e.Holds s s')
    (hr : r.Ready base s) : r.Ready base s' := by
  have hseg : r.read s' = r.read s := by
    cases r
    · have := congrArg (fun t : RamState => t.FS) h.agrees.rest
      exact this
    · have := congrArg (fun t : RamState => t.GS) h.agrees.rest
      exact this
  exact ⟨hseg ▸ hr.seg, hseg ▸ hr.base⟩

/-- An effect avoids a block of code if each memory range it writes is apart from it. -/
theorem Effect.avoids_codeRange {e : Effect} {p : BitVec 64} {bytes : List UInt8}
    (h : ∀ c ∈ e.components, ∀ a len, c = .mem a len → RangeApart a len p bytes.length) :
    e.Avoids (codeRange p bytes) := by
  intro x hx c hc hcov
  cases c with
  | mem a len =>
    obtain ⟨i, hi, hxi⟩ := hcov
    obtain ⟨j, hj, hxj⟩ := exists_of_mem_codeRange hx
    exact h _ hc a len rfl i hi j hj (hxi.symm.trans hxj)
  | _ => exact hcov

/-- `addr` reads only what `Obs` sees, so it gives the same address in observationally equal
states. -/
def AddrObs (addr : RamState → BitVec 64) : Prop := ∀ t t', Obs t t' → addr t = addr t'

theorem AddrObs.eq {addr : RamState → BitVec 64} (ha : AddrObs addr)
    (ho : Obs (e.after s true) s') : addr s' = addr (e.after s true) :=
  (ha _ _ ho).symm

/-! #### Reads after an effect, in the canonical state -/

section ObsRewrite

variable {t t' : RamState} (ho : Obs t t') {n : Nat}
include ho

@[x86_obs] theorem Obs.back_reg (r : BitVec 5) :
    (Operand.reg r : Operand n).read t' = (Operand.reg r).read t :=
  (ho.read_reg r).symm

@[x86_obs] theorem Obs.back_mem (a : BitVec 64) :
    (Operand.mem a : Operand n).read t' = (Operand.mem a).read t :=
  (ho.read_mem a).symm

@[x86_obs] theorem Obs.back_xmm (r : BitVec 5) :
    (Operand.xmm r : Operand n).read t' = (Operand.xmm r).read t :=
  (ho.read_xmm r).symm

@[x86_obs] theorem Obs.back_regHigh (r : BitVec 5) :
    (Operand.regHigh r : Operand n).read t' = (Operand.regHigh r).read t :=
  (ho.read_regHigh r).symm

@[x86_obs] theorem Obs.back_mxcsr :
    (Operand.mxcsr : Operand n).read t' = Operand.mxcsr.read t :=
  ho.read_mxcsr.symm

@[x86_obs] theorem Obs.back_df :
    (Operand.df : Operand n).read t' = Operand.df.read t :=
  ho.read_df.symm

@[x86_obs] theorem Obs.back_fpr (r : BitVec 3) :
    (Operand.fpr r : Operand n).read t' = (Operand.fpr r).read t :=
  (ho.read_fpr r).symm

@[x86_obs] theorem Obs.back_mmx (r : BitVec 3) :
    (Operand.mmx r : Operand n).read t' = (Operand.mmx r).read t :=
  (ho.read_mmx r).symm

@[x86_obs] theorem Obs.back_fsw :
    (Operand.fsw : Operand n).read t' = Operand.fsw.read t :=
  ho.read_fsw.symm

@[x86_obs] theorem Obs.back_ftw :
    (Operand.ftw : Operand n).read t' = Operand.ftw.read t :=
  ho.read_ftw.symm

@[x86_obs] theorem Obs.back_fcw :
    (Operand.fcw : Operand n).read t' = Operand.fcw.read t :=
  ho.read_fcw.symm

@[x86_obs] theorem Obs.back_fpuPtr :
    (Operand.fpuPtr : Operand n).read t' = Operand.fpuPtr.read t :=
  ho.read_fpuPtr.symm

@[x86_obs] theorem Obs.back_addr (am : AddrMode) (nxt : BitVec 64) :
    am.addr t' nxt = am.addr t nxt :=
  (AddrMode.addr_obs ho am nxt).symm

@[x86_obs] theorem Obs.back_addr32 (am : AddrMode) (nxt : BitVec 64) :
    am.addr32 t' nxt = am.addr32 t nxt :=
  (AddrMode.addr32_obs ho am nxt).symm

end ObsRewrite

/-! #### What every effect keeps -/

section Inv

variable (h : e.Holds s s')
include h

theorem Effect.Holds.sameControls : SameControls s s' := SameControls.of_fixedPart h.agrees.rest

@[x86_inv] theorem Effect.Holds.CR0_eq : s'.CR0 = s.CR0 := congrArg (·.CR0) h.agrees.rest
@[x86_inv] theorem Effect.Holds.CR4_eq : s'.CR4 = s.CR4 := congrArg (·.CR4) h.agrees.rest
@[x86_inv] theorem Effect.Holds.XCR0_eq : s'.XCR0 = s.XCR0 := congrArg (·.XCR0) h.agrees.rest
@[x86_inv] theorem Effect.Holds.TR_eq : s'.TR = s.TR := congrArg (·.TR) h.agrees.rest
@[x86_inv] theorem Effect.Holds.LDTR_eq : s'.LDTR = s.LDTR := congrArg (·.LDTR) h.agrees.rest
@[x86_inv] theorem Effect.Holds.CS_eq : s'.CS = s.CS := congrArg (·.CS) h.agrees.rest
@[x86_inv] theorem Effect.Holds.SS_eq : s'.SS = s.SS := congrArg (·.SS) h.agrees.rest
@[x86_inv] theorem Effect.Holds.DS_eq : s'.DS = s.DS := congrArg (·.DS) h.agrees.rest
@[x86_inv] theorem Effect.Holds.ES_eq : s'.ES = s.ES := congrArg (·.ES) h.agrees.rest
@[x86_inv] theorem Effect.Holds.FS_eq : s'.FS = s.FS := congrArg (·.FS) h.agrees.rest
@[x86_inv] theorem Effect.Holds.GS_eq : s'.GS = s.GS := congrArg (·.GS) h.agrees.rest
@[x86_inv] theorem Effect.Holds.VMX_eq : s'.VMX_Operation_Mode = s.VMX_Operation_Mode :=
  congrArg (·.VMX_Operation_Mode) h.agrees.rest

@[x86_inv] theorem Effect.Holds.segSelector_eq (r : BitVec 3) :
    segSelector s' r = segSelector s r := by
  unfold segSelector
  rw [h.ES_eq, h.CS_eq, h.SS_eq, h.DS_eq, h.FS_eq, h.GS_eq]

@[x86_inv] theorem Effect.Holds.sysRegReadable_iff : SysRegReadable s' ↔ SysRegReadable s := by
  constructor <;> intro hs <;> constructor
  · rw [← h.CR4_eq]; exact hs.umip
  · rw [← h.VMX_eq]; exact hs.vmx
  · rw [h.CR4_eq]; exact hs.umip
  · rw [h.VMX_eq]; exact hs.vmx

@[x86_inv] theorem Effect.Holds.reportsCPUFeature_iff [Bindings] {f : CPUID_Feature} {b : Bool} :
    Prelude.ReportsCPUFeature Bindings.processor s' f b ↔
      Prelude.ReportsCPUFeature Bindings.processor s f b :=
  ⟨reportsCPUFeature_of_sameControls (SameControls.of_fixedPart h.agrees.rest.symm),
    reportsCPUFeature_of_sameControls h.sameControls⟩

@[x86_inv] theorem Effect.Holds.supportedSSE_iff [Bindings] :
    Prelude.SupportedSSE Bindings.processor s' ↔ Prelude.SupportedSSE Bindings.processor s :=
  ⟨SupportedSSE.of_sameControls (SameControls.of_fixedPart h.agrees.rest.symm),
    SupportedSSE.of_sameControls h.sameControls⟩

@[x86_inv] theorem Effect.Holds.segReady_iff {r : SegReg} {base : BitVec 64} :
    r.Ready base s' ↔ r.Ready base s := by
  have hseg : r.read s' = r.read s := by
    cases r
    · exact h.FS_eq
    · exact h.GS_eq
  exact ⟨fun hr => ⟨hseg ▸ hr.seg, hseg ▸ hr.base⟩, fun hr => ⟨hseg ▸ hr.seg, hseg ▸ hr.base⟩⟩

@[x86_inv] theorem Effect.Holds.lockReady_iff [Bindings] {a : BitVec 64} {len : Nat} :
    LockReady s' a len ↔ LockReady s a len :=
  ⟨fun hl => hl.of_sameControls (SameControls.of_fixedPart h.agrees.rest.symm),
    fun hl => hl.of_sameControls h.sameControls⟩

end Inv

/-! #### Fields as operand reads -/

@[x86_pre_simp] theorem read_mxcsr_field (t : RamState) :
    t.MXCSR = (Operand.mxcsr : Operand 32).read t := by
  simp [Operand.read]

@[x86_pre_simp] theorem read_fcw_field (t : RamState) :
    t.FP87_Control = (Operand.fcw : Operand 16).read t := by
  simp [Operand.read]

@[x86_pre_simp] theorem read_ftw_field (t : RamState) :
    t.FP87_Tag_Word = (Operand.ftw : Operand 16).read t := by
  simp [Operand.read]

@[x86_pre_simp] theorem read_fpr_field (t : RamState) (r : BitVec 3) :
    t.FP87[fprIndex r] = (Operand.fpr r : Operand 80).read t := by
  simp [Operand.read]

@[x86_pre_simp] theorem read_gpr_field (t : RamState) (r : BitVec 5) :
    t.GPR[gprIndex r] = (Operand.reg r : Operand 64).read t :=
  (Operand.read_reg64 t r).symm

@[x86_pre_simp] theorem read_df_field (t : RamState) :
    dfBit t.RFLAGS = (Operand.df : Operand 1).read t := by
  simp [Operand.read]

@[x86_pre_simp] theorem fswES_field (t : RamState) :
    fswES t.FP87_Status = fswES ((Operand.fsw : Operand 16).read t) := by
  simp [Operand.read]

/-- Adding two literals in turn adds their sum. -/
@[x86_pre_simp] theorem BitVec.add_ofNat_ofNat {n : Nat} (x : BitVec n) (a b : Nat) :
    x + BitVec.ofNat n a + BitVec.ofNat n b = x + BitVec.ofNat n (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

attribute [x86_pre_simp] BitVec.add_zero Nat.reduceAdd BitVec.reduceOfNat
  not_false_eq_true and_true true_and and_self implies_true Nat.mod_one
/-! #### The status flags after an effect -/

/-- The flags after `e` from `s`: the ones `e` defines, the undefined ones from `g`. -/
@[x86_compose] def Effect.flagsWith (e : Effect) (s : RamState) (g : StatusFlag → Bool) :
    StatusFlags :=
  ⟨(e.flag s .CF).getD (g .CF), (e.flag s .PF).getD (g .PF), (e.flag s .AF).getD (g .AF),
    (e.flag s .ZF).getD (g .ZF), (e.flag s .SF).getD (g .SF), (e.flag s .OF).getD (g .OF)⟩

/-- The flags after an effect are the ones it defines, the undefined ones some values `g`. -/
theorem Effect.Holds.ofRFLAGS_eq (h : e.Holds s s') :
    ∃ g, StatusFlags.ofRFLAGS s'.RFLAGS = e.flagsWith s g := by
  refine ⟨fun i => (StatusFlags.ofRFLAGS s'.RFLAGS).get i, ?_⟩
  have key : ∀ i, (StatusFlags.ofRFLAGS s'.RFLAGS).get i =
      (e.flag s i).getD ((StatusFlags.ofRFLAGS s'.RFLAGS).get i) := by
    intro i
    have := h.flag i
    revert this
    cases e.flag s i with
    | none => intro; rfl
    | some v => intro hv; exact hv
  have h1 := key .CF
  have h2 := key .PF
  have h3 := key .AF
  have h4 := key .ZF
  have h5 := key .SF
  have h6 := key .OF
  simp only [StatusFlags.get] at h1 h2 h3 h4 h5 h6
  unfold Effect.flagsWith
  simp only [StatusFlags.get]
  rw [← h1, ← h2, ← h3, ← h4, ← h5, ← h6]

/-! #### Carrying preconditions over -/

section Pre

@[x86_pre] theorem Effect.Holds.present (h : e.Holds s s') {a : BitVec 64} {len : Nat}
    (hp : ∀ i < len, (s.external[a + BitVec.ofNat 64 i]?).isSome) :
    ∀ i < len, (s'.external[a + BitVec.ofNat 64 i]?).isSome :=
  fun i hi => h.agrees.grow _ (hp i hi)


/-- A readable range at an address read from the state, carried over. -/
theorem MemReadable.carry (h : e.Holds s s') (ho : Obs (e.after s true) s')
    {addr : RamState → BitVec 64} (ha : AddrObs addr) {len : Nat}
    (hr : MemReadable s (addr (e.after s true)) len) : MemReadable s' (addr s') len := by
  rw [ha.eq ho]
  exact hr.of_holds h

/-- A writable range at an address read from the state, carried over. -/
theorem MemWritable.carry (h : e.Holds s s') (ho : Obs (e.after s true) s')
    {addr : RamState → BitVec 64} (ha : AddrObs addr) {len : Nat}
    (hw : MemWritable s (addr (e.after s true)) len) : MemWritable s' (addr s') len := by
  rw [ha.eq ho]
  exact hw.of_holds h

/-- A range at an address read from the state, apart from code, carried over. -/
theorem RangeApart.carry (ho : Obs (e.after s true) s') {addr : RamState → BitVec 64}
    (ha : AddrObs addr) {len : Nat} {p : BitVec 64} {n : Nat}
    (hap : RangeApart (addr (e.after s true)) len p n) : RangeApart (addr s') len p n := by
  rw [ha.eq ho]
  exact hap

/-- An address plus a constant (a segment base) reads what the address reads. -/
theorem AddrObs.add_left {addr : RamState → BitVec 64} (ha : AddrObs addr) (base : BitVec 64) :
    AddrObs (fun t => base + addr t) :=
  fun t t' ho => by simp only [ha t t' ho]

/-- A range apart from a block's code is apart from each instruction in it. -/
theorem RangeApart.sub {a p : BitVec 64} {len total : Nat} (h : RangeApart a len p total)
    (off n : Nat) (hn : off + n ≤ total) : RangeApart a len (p + BitVec.ofNat 64 off) n := by
  intro i hi j hj he
  apply h i hi (off + j) (by omega)
  rw [he, BitVec.add_assoc, BitVec.ofNat_add]

/-- `RangeApart.sub` for the block's first instruction. -/
theorem RangeApart.sub0 {a p : BitVec 64} {len total : Nat} (h : RangeApart a len p total)
    (n : Nat) (hn : n ≤ total) : RangeApart a len p n :=
  fun i hi j hj => h i hi j (by omega)

/-- A load's precondition after an effect, for any address that reads only what `Obs` sees. -/
@[x86_pre] theorem LoadPre.of_holds (h : e.Holds s s') (ho : Obs (e.after s true) s')
    {p : BitVec 64} {addr : RamState → BitVec 64} {len : Nat} (hrip : e.rip = p)
    (ha : AddrObs addr) (hr : MemReadable s (addr (e.after s true)) len) :
    LoadPre p addr len s' :=
  ⟨h.rip_of hrip, MemReadable.carry h ho ha hr⟩

/-- A store's precondition after an effect, for any address that reads only what `Obs` sees. -/
@[x86_pre] theorem StorePre.of_holds (h : e.Holds s s') (ho : Obs (e.after s true) s')
    {p : BitVec 64} {codeLen : Nat} {addr : RamState → BitVec 64} {len : Nat} (hrip : e.rip = p)
    (ha : AddrObs addr) (hw : MemWritable s (addr (e.after s true)) len)
    (hap : RangeApart (addr (e.after s true)) len p codeLen) :
    StorePre p codeLen addr len s' :=
  ⟨h.rip_of hrip, MemWritable.carry h ho ha hw, RangeApart.carry ho ha hap⟩

/-- A load's precondition through a segment override after an effect. -/
@[x86_pre] theorem SegLoadPre.of_holds (h : e.Holds s s') (ho : Obs (e.after s true) s')
    {p base : BitVec 64} {r : SegReg} {addr : RamState → BitVec 64} {len : Nat}
    (hrip : e.rip = p) (hr : r.Ready base s) (ha : AddrObs addr)
    (hm : MemReadable s (base + addr (e.after s true)) len) :
    SegLoadPre p r base addr len s' :=
  ⟨h.rip_of hrip, h.segReady_iff.mpr hr,
    MemReadable.carry h ho (ha.add_left base) (addr := fun t => base + addr t) hm⟩

/-- A store's precondition through a segment override after an effect. -/
@[x86_pre] theorem SegStorePre.of_holds (h : e.Holds s s') (ho : Obs (e.after s true) s')
    {p base : BitVec 64} {codeLen : Nat} {r : SegReg} {addr : RamState → BitVec 64} {len : Nat}
    (hrip : e.rip = p) (hr : r.Ready base s) (ha : AddrObs addr)
    (hw : MemWritable s (base + addr (e.after s true)) len)
    (hap : RangeApart (base + addr (e.after s true)) len p codeLen) :
    SegStorePre p codeLen r base addr len s' :=
  ⟨StorePre.of_holds h ho hrip (ha.add_left base) (addr := fun t => base + addr t) hw hap,
    h.segReady_iff.mpr hr⟩

end Pre

@[x86_inv] theorem Effect.Holds.CPL_eq (h : e.Holds s s') : s'.CPL = s.CPL :=
  congrArg (·.CPL) h.agrees.rest

@[x86_inv] theorem Effect.Holds.PLATFORM_INFO_eq (h : e.Holds s s') :
    s'.PLATFORM_INFO = s.PLATFORM_INFO :=
  congrArg (·.PLATFORM_INFO) h.agrees.rest

@[x86_inv] theorem Effect.Holds.IA32_MISC_ENABLE_eq (h : e.Holds s s') :
    s'.IA32_MISC_ENABLE = s.IA32_MISC_ENABLE :=
  congrArg (·.IA32_MISC_ENABLE) h.agrees.rest

/-- A bit of RFLAGS other than the status flags and DF is kept by every effect. -/
theorem Effect.Holds.rflags_getLsbD (h : e.Holds s s') {k : Nat}
    (hk : (0xCD5#64).getLsbD k = false) : s'.RFLAGS.getLsbD k = s.RFLAGS.getLsbD k := by
  have := congrArg (fun t => (t.RFLAGS).getLsbD k) h.agrees.rest
  simp only [fixedPart, beforeFetch, resetStepFields] at this
  have h1 : (0x8D5#64).getLsbD k = false := by
    by_cases hk64 : k < 64
    · revert hk; revert hk64; generalize k = k; decide +revert
    · exact BitVec.getLsbD_of_ge _ _ (by omega)
  have h2 : (0x400#64).getLsbD k = false := by
    by_cases hk64 : k < 64
    · revert hk; revert hk64; generalize k = k; decide +revert
    · exact BitVec.getLsbD_of_ge _ _ (by omega)
  by_cases hk64 : k < 64
  · rw [clearDirectionFlag, clearDirectionFlag, clearStatusFlags, clearStatusFlags,
      BitVec.getLsbD_and, BitVec.getLsbD_and, BitVec.getLsbD_and, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_not, h1, h2] at this
    simpa [hk64] using this
  · rw [BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)]

/-- IOPL (RFLAGS bits 12–13) is kept by every effect. -/
@[x86_inv] theorem Effect.Holds.iopl_eq (h : e.Holds s s') :
    s'.RFLAGS.extractLsb' 12 2 = s.RFLAGS.extractLsb' 12 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl
  · exact h.rflags_getLsbD (by decide)
  · exact h.rflags_getLsbD (by decide)

@[x86_inv] theorem Effect.Holds.cpuidResult_eq (h : e.Holds s s') (P : Processor)
    (eax ecx : BitVec 32) : cpuidResult P s' eax ecx = cpuidResult P s eax ecx :=
  cpuidResult_of_sameControls h.sameControls eax ecx

@[x86_pre] theorem Effect.Holds.present1 (h : e.Holds s s') {x : BitVec 64}
    (hp : (s.external[x]?).isSome) : (s'.external[x]?).isSome :=
  h.agrees.grow _ hp

attribute [x86_compose] rax rbx

end Transport

/-! ### Reads of canonical states -/

section Reads

variable {t : RamState}

@[x86_compose] theorem Operand.read_reg_write_reg {m : Nat} (r r' : BitVec 5) (v : BitVec 64) :
    (Operand.reg r : Operand m).read ((Operand.reg r' : Operand 64).write t v) =
      if r' = r then v.setWidth m else (Operand.reg r : Operand m).read t := by
  split
  · subst r'
    simp [Operand.read, Operand.write_reg64]
  · rename_i hne
    exact Operand.read_write_reg_of_ne t hne v

@[x86_compose] theorem Operand.read_reg_write_mem' {m n : Nat} (r : BitVec 5) (a : BitVec 64)
    (v : BitVec n) :
    (Operand.reg r : Operand m).read ((Operand.mem a : Operand n).write t v) =
      (Operand.reg r : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_reg_write_xmm' {m n : Nat} (r r' : BitVec 5) (v : BitVec n) :
    (Operand.reg r : Operand m).read ((Operand.xmm r' : Operand n).write t v) =
      (Operand.reg r : Operand m).read t := id rfl

/-- AH–BH after a 64-bit register write: bits 8–15 of the written value, or the old ones. -/
@[x86_compose] theorem Operand.read_regHigh_write_reg {m : Nat} (r r' : BitVec 5) (v : BitVec 64) :
    (Operand.regHigh r : Operand m).read ((Operand.reg r' : Operand 64).write t v) =
      if r' = r then v.extractLsb' 8 m else (Operand.regHigh r : Operand m).read t := by
  split
  · subst r'
    simp [Operand.read, Operand.write_reg64]
  · rename_i hne
    have hi : gprIndex r' ≠ gprIndex r := fun h =>
      hne (BitVec.eq_of_toNat_eq (Fin.mk.inj_iff.mp h))
    simp [Operand.write, Operand.read, Fin.val_ne_of_ne hi]

@[x86_compose] theorem Operand.read_regHigh_write_mem {m n : Nat} (r : BitVec 5) (a : BitVec 64)
    (v : BitVec n) :
    (Operand.regHigh r : Operand m).read ((Operand.mem a : Operand n).write t v) =
      (Operand.regHigh r : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_regHigh_write_xmm {m n : Nat} (r r' : BitVec 5)
    (v : BitVec n) :
    (Operand.regHigh r : Operand m).read ((Operand.xmm r' : Operand n).write t v) =
      (Operand.regHigh r : Operand m).read t := id rfl

/-- The low byte of a register after its low byte was replaced: the new byte. -/
@[x86_compose] theorem setWidth_mergeGPR8 (v : BitVec 8) (x : BitVec 64) :
    (mergeGPR 8 v x).setWidth 8 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [mergeGPR, show (8 : Nat) ≠ 32 by decide, ite_false, BitVec.getLsbD_setWidth,
    hk, decide_true, Bool.true_and]
  rw [getLsbD_setSlice _ _ _ _ _ (by omega)]
  simp [hk]

/-- Bits 8–15 of a register after its low byte was replaced: the old ones. -/
@[x86_compose] theorem extractLsb'_mergeGPR8 (v : BitVec 8) (x : BitVec 64) :
    (mergeGPR 8 v x).extractLsb' 8 8 = x.extractLsb' 8 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [mergeGPR, show (8 : Nat) ≠ 32 by decide, ite_false, BitVec.getLsbD_extractLsb',
    hk, decide_true, Bool.true_and]
  rw [getLsbD_setSlice _ _ _ _ _ (by omega)]
  simp

/-- The low byte of a register after bits 8–15 were replaced: the old one. -/
@[x86_compose] theorem setWidth_setSlice_high (v : BitVec 8) (x : BitVec 64) :
    (X86.Runtime.setSlice x 8 8 v).setWidth 8 = x.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_setWidth, hk, decide_true, Bool.true_and]
  rw [getLsbD_setSlice _ _ _ _ _ (by omega)]
  split <;> first | rfl | omega

/-- Bits 8–15 of a register after they were replaced: the new ones. -/
@[x86_compose] theorem extractLsb'_setSlice_high (v : BitVec 8) (x : BitVec 64) :
    (X86.Runtime.setSlice x 8 8 v).extractLsb' 8 8 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and]
  rw [getLsbD_setSlice _ _ _ _ _ (by omega)]
  simp [show 8 + k < 16 by omega]

/-- The low `m` bits of a 64-bit register read are the `m`-bit read. -/
@[x86_compose] theorem Operand.setWidth_read_reg64 {m : Nat} (r : BitVec 5) :
    ((Operand.reg r : Operand 64).read t).setWidth m = (Operand.reg r : Operand m).read t := rfl

/-- Bits 8 to `8 + m - 1` of a 64-bit register read are the `regHigh` read (AH–BH at `m = 8`). -/
@[x86_compose] theorem Operand.extractLsb'_read_reg64 {m : Nat} (r : BitVec 5) :
    ((Operand.reg r : Operand 64).read t).extractLsb' 8 m =
      (Operand.regHigh r : Operand m).read t := by
  simp [Operand.read]

attribute [x86_compose] Operand.byteReg_eq byteRegGpr mergeByteReg

@[x86_compose] theorem Operand.read_mem_write_reg {m n : Nat} (a : BitVec 64) (r : BitVec 5)
    (v : BitVec n) :
    (Operand.mem a : Operand m).read ((Operand.reg r : Operand n).write t v) =
      (Operand.mem a : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_mem_write_xmm {m n : Nat} (a : BitVec 64) (r : BitVec 5)
    (v : BitVec n) :
    (Operand.mem a : Operand m).read ((Operand.xmm r : Operand n).write t v) =
      (Operand.mem a : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_xmm_write_reg {m n : Nat} (r r' : BitVec 5) (v : BitVec n) :
    (Operand.xmm r : Operand m).read ((Operand.reg r' : Operand n).write t v) =
      (Operand.xmm r : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_xmm_write_mem {m n : Nat} (r : BitVec 5) (a : BitVec 64)
    (v : BitVec n) :
    (Operand.xmm r : Operand m).read ((Operand.mem a : Operand n).write t v) =
      (Operand.xmm r : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_xmm_write_xmm (r r' : BitVec 5) (v : BitVec 128) :
    (Operand.xmm r : Operand 128).read ((Operand.xmm r' : Operand 128).write t v) =
      if r' = r then v else (Operand.xmm r : Operand 128).read t := by
  split
  · subst r'
    simp [Operand.read, Operand.write]
  · rename_i hne
    have hi : xmmIndex r' ≠ xmmIndex r := fun e =>
      hne (BitVec.eq_of_toNat_eq (Fin.mk.inj_iff.mp e))
    simp [Operand.read, Operand.write, Fin.val_ne_of_ne hi]

/-- An XMM register at any width after a write to another one, at any width. -/
@[x86_compose] theorem Operand.read_xmm_write_xmm_of_ne {m n : Nat} (r r' : BitVec 5)
    (v : BitVec n) (h : r' ≠ r) :
    (Operand.xmm r : Operand m).read ((Operand.xmm r' : Operand n).write t v) =
      (Operand.xmm r : Operand m).read t := by
  have hi : xmmIndex r' ≠ xmmIndex r := fun e =>
    h (BitVec.eq_of_toNat_eq (Fin.mk.inj_iff.mp e))
  simp [Operand.read, Operand.write, Fin.val_ne_of_ne hi]

/-- The low `m` bits of an XMM register after a 128-bit write to it (a scalar read after a
packed write). -/
@[x86_compose] theorem Operand.read_xmm_write_xmm_self {m : Nat} (r : BitVec 5) (v : BitVec 128)
    (h : m ≤ 128) :
    (Operand.xmm r : Operand m).read ((Operand.xmm r : Operand 128).write t v) =
      v.setWidth m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [Operand.read, Operand.write, getLsbD_xmmMerge, show i < 128 by omega, hi]

@[x86_compose] theorem Operand.read_mxcsr_write_mxcsr (v : BitVec 32) :
    (Operand.mxcsr : Operand 32).read ((Operand.mxcsr : Operand 32).write t v) = v := by
  simp

@[x86_compose] theorem Operand.read_mxcsr_write_reg {m n : Nat} (r : BitVec 5) (v : BitVec n) :
    (Operand.mxcsr : Operand m).read ((Operand.reg r : Operand n).write t v) =
      (Operand.mxcsr : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_mxcsr_write_mem {m n : Nat} (a : BitVec 64) (v : BitVec n) :
    (Operand.mxcsr : Operand m).read ((Operand.mem a : Operand n).write t v) =
      (Operand.mxcsr : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_mxcsr_write_xmm {m n : Nat} (r : BitVec 5) (v : BitVec n) :
    (Operand.mxcsr : Operand m).read ((Operand.xmm r : Operand n).write t v) =
      (Operand.mxcsr : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_reg_write_mxcsr {m n : Nat} (r : BitVec 5) (v : BitVec n) :
    (Operand.reg r : Operand m).read ((Operand.mxcsr : Operand n).write t v) =
      (Operand.reg r : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_regHigh_write_mxcsr {m n : Nat} (r : BitVec 5)
    (v : BitVec n) :
    (Operand.regHigh r : Operand m).read ((Operand.mxcsr : Operand n).write t v) =
      (Operand.regHigh r : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_mem_write_mxcsr {m n : Nat} (a : BitVec 64) (v : BitVec n) :
    (Operand.mem a : Operand m).read ((Operand.mxcsr : Operand n).write t v) =
      (Operand.mem a : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_xmm_write_mxcsr {m n : Nat} (r : BitVec 5) (v : BitVec n) :
    (Operand.xmm r : Operand m).read ((Operand.mxcsr : Operand n).write t v) =
      (Operand.xmm r : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_df_write_df (v : BitVec 1) :
    (Operand.df : Operand 1).read ((Operand.df : Operand 1).write t v) = v := by
  simp

@[x86_compose] theorem Operand.read_df_write_reg {m n : Nat} (r : BitVec 5) (v : BitVec n) :
    (Operand.df : Operand m).read ((Operand.reg r : Operand n).write t v) =
      (Operand.df : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_df_write_mem {m n : Nat} (a : BitVec 64) (v : BitVec n) :
    (Operand.df : Operand m).read ((Operand.mem a : Operand n).write t v) =
      (Operand.df : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_df_write_xmm {m n : Nat} (r : BitVec 5) (v : BitVec n) :
    (Operand.df : Operand m).read ((Operand.xmm r : Operand n).write t v) =
      (Operand.df : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_df_write_mxcsr {m n : Nat} (v : BitVec n) :
    (Operand.df : Operand m).read ((Operand.mxcsr : Operand n).write t v) =
      (Operand.df : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_reg_write_df {m n : Nat} (r : BitVec 5) (v : BitVec n) :
    (Operand.reg r : Operand m).read ((Operand.df : Operand n).write t v) =
      (Operand.reg r : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_regHigh_write_df {m n : Nat} (r : BitVec 5) (v : BitVec n) :
    (Operand.regHigh r : Operand m).read ((Operand.df : Operand n).write t v) =
      (Operand.regHigh r : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_mem_write_df {m n : Nat} (a : BitVec 64) (v : BitVec n) :
    (Operand.mem a : Operand m).read ((Operand.df : Operand n).write t v) =
      (Operand.mem a : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_xmm_write_df {m n : Nat} (r : BitVec 5) (v : BitVec n) :
    (Operand.xmm r : Operand m).read ((Operand.df : Operand n).write t v) =
      (Operand.xmm r : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_mxcsr_write_df {m n : Nat} (v : BitVec n) :
    (Operand.mxcsr : Operand m).read ((Operand.df : Operand n).write t v) =
      (Operand.mxcsr : Operand m).read t := id rfl

/-! #### The x87 state

A read outside the x87 state after an x87 write, and an x87 read after a write outside it, is the
old read (`Operand.read_write_x87`, `Operand.read_x87_write`, with `Operand.NotX87` evaluated);
within the x87 state, the lemmas below. -/

attribute [x86_compose] Operand.NotX87 mmxFpr_setWidth

@[x86_compose] theorem Operand.read_write_x87' {m n : Nat} (op : Operand m) (hop : op.NotX87)
    (dst : Operand n) (hdst : ¬ dst.NotX87) (v : BitVec n) :
    op.read (dst.write t v) = op.read t := Operand.read_write_x87 t op hop dst hdst v

@[x86_compose] theorem Operand.read_x87_write' {m n : Nat} (op : Operand m) (hop : ¬ op.NotX87)
    (dst : Operand n) (hdst : dst.NotX87) (v : BitVec n) :
    op.read (dst.write t v) = op.read t := Operand.read_x87_write t op hop dst hdst v

@[x86_compose] theorem Operand.read_fpr_write_fpr (r r' : BitVec 3) (v : BitVec 80) :
    (Operand.fpr r : Operand 80).read ((Operand.fpr r' : Operand 80).write t v) =
      if r' = r then v else (Operand.fpr r : Operand 80).read t := by
  split
  · subst r'
    simp [Operand.read, Operand.write]
  · rename_i hne
    have hi : fprIndex r' ≠ fprIndex r := fun e =>
      hne (BitVec.eq_of_toNat_eq (Fin.mk.inj_iff.mp e))
    simp [Operand.read, Operand.write, Fin.val_ne_of_ne hi]

/-- An MMX register after an 80-bit write of a physical register: the written value's low 64
bits (`mmxFpr_setWidth` for an MMX write), or the old value. -/
@[x86_compose] theorem Operand.read_mmx_write_fpr (r r' : BitVec 3) (v : BitVec 80) :
    (Operand.mmx r : Operand 64).read ((Operand.fpr r' : Operand 80).write t v) =
      if r' = r then v.setWidth 64 else (Operand.mmx r : Operand 64).read t := by
  split
  · subst r'
    simp [Operand.read, Operand.write]
  · rename_i hne
    have hi : fprIndex r' ≠ fprIndex r := fun e =>
      hne (BitVec.eq_of_toNat_eq (Fin.mk.inj_iff.mp e))
    simp [Operand.read, Operand.write, Fin.val_ne_of_ne hi]

@[x86_compose] theorem Operand.read_fsw_write_fsw (v : BitVec 16) :
    (Operand.fsw : Operand 16).read ((Operand.fsw : Operand 16).write t v) = fswRest v := by
  simp

attribute [x86_compose] fswRest_fswRest fswRest_mmxStatus

@[x86_compose] theorem Operand.read_fsw_write_fcc {m n : Nat} (c : BitVec 4) (v : BitVec n) :
    (Operand.fsw : Operand m).read ((Operand.fcc c : Operand n).write t v) =
      (Operand.fsw : Operand m).read t := by
  simp only [Operand.read, Operand.write, fswRest_fswSetCC]

@[x86_compose] theorem Operand.read_fpr_write_fcc {m n : Nat} (r : BitVec 3) (c : BitVec 4)
    (v : BitVec n) :
    (Operand.fpr r : Operand m).read ((Operand.fcc c : Operand n).write t v) =
      (Operand.fpr r : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_mmx_write_fcc {m n : Nat} (r : BitVec 3) (c : BitVec 4)
    (v : BitVec n) :
    (Operand.mmx r : Operand m).read ((Operand.fcc c : Operand n).write t v) =
      (Operand.mmx r : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_ftw_write_fcc {m n : Nat} (c : BitVec 4) (v : BitVec n) :
    (Operand.ftw : Operand m).read ((Operand.fcc c : Operand n).write t v) =
      (Operand.ftw : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_fcw_write_fcc {m n : Nat} (c : BitVec 4) (v : BitVec n) :
    (Operand.fcw : Operand m).read ((Operand.fcc c : Operand n).write t v) =
      (Operand.fcw : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_fpuPtr_write_fcc {m n : Nat} (c : BitVec 4) (v : BitVec n) :
    (Operand.fpuPtr : Operand m).read ((Operand.fcc c : Operand n).write t v) =
      (Operand.fpuPtr : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_fsw_write_fpr {m n : Nat} (r : BitVec 3) (v : BitVec n) :
    (Operand.fsw : Operand m).read ((Operand.fpr r : Operand n).write t v) =
      (Operand.fsw : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_fpr_write_fsw {m n : Nat} (r : BitVec 3) (v : BitVec n) :
    (Operand.fpr r : Operand m).read ((Operand.fsw : Operand n).write t v) =
      (Operand.fpr r : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_fsw_write_mmx {m n : Nat} (r : BitVec 3) (v : BitVec n) :
    (Operand.fsw : Operand m).read ((Operand.mmx r : Operand n).write t v) =
      (Operand.fsw : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_mmx_write_fsw {m n : Nat} (r : BitVec 3) (v : BitVec n) :
    (Operand.mmx r : Operand m).read ((Operand.fsw : Operand n).write t v) =
      (Operand.mmx r : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_fsw_write_ftw {m n : Nat} (v : BitVec n) :
    (Operand.fsw : Operand m).read ((Operand.ftw : Operand n).write t v) =
      (Operand.fsw : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_fsw_write_fcw {m n : Nat} (v : BitVec n) :
    (Operand.fsw : Operand m).read ((Operand.fcw : Operand n).write t v) =
      (Operand.fsw : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_fsw_write_fpuPtr {m n : Nat} (v : BitVec n) :
    (Operand.fsw : Operand m).read ((Operand.fpuPtr : Operand n).write t v) =
      (Operand.fsw : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_ftw_write_ftw (v : BitVec 16) :
    (Operand.ftw : Operand 16).read ((Operand.ftw : Operand 16).write t v) = v := by
  simp

@[x86_compose] theorem Operand.read_ftw_write_fpr {m n : Nat} (r : BitVec 3) (v : BitVec n) :
    (Operand.ftw : Operand m).read ((Operand.fpr r : Operand n).write t v) =
      (Operand.ftw : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_fpr_write_ftw {m n : Nat} (r : BitVec 3) (v : BitVec n) :
    (Operand.fpr r : Operand m).read ((Operand.ftw : Operand n).write t v) =
      (Operand.fpr r : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_ftw_write_mmx {m n : Nat} (r : BitVec 3) (v : BitVec n) :
    (Operand.ftw : Operand m).read ((Operand.mmx r : Operand n).write t v) =
      (Operand.ftw : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_mmx_write_ftw {m n : Nat} (r : BitVec 3) (v : BitVec n) :
    (Operand.mmx r : Operand m).read ((Operand.ftw : Operand n).write t v) =
      (Operand.mmx r : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_ftw_write_fsw {m n : Nat} (v : BitVec n) :
    (Operand.ftw : Operand m).read ((Operand.fsw : Operand n).write t v) =
      (Operand.ftw : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_ftw_write_fcw {m n : Nat} (v : BitVec n) :
    (Operand.ftw : Operand m).read ((Operand.fcw : Operand n).write t v) =
      (Operand.ftw : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_ftw_write_fpuPtr {m n : Nat} (v : BitVec n) :
    (Operand.ftw : Operand m).read ((Operand.fpuPtr : Operand n).write t v) =
      (Operand.ftw : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_fcw_write_fcw (v : BitVec 16) :
    (Operand.fcw : Operand 16).read ((Operand.fcw : Operand 16).write t v) = v := by
  simp

@[x86_compose] theorem Operand.read_fcw_write_fpr {m n : Nat} (r : BitVec 3) (v : BitVec n) :
    (Operand.fcw : Operand m).read ((Operand.fpr r : Operand n).write t v) =
      (Operand.fcw : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_fpr_write_fcw {m n : Nat} (r : BitVec 3) (v : BitVec n) :
    (Operand.fpr r : Operand m).read ((Operand.fcw : Operand n).write t v) =
      (Operand.fpr r : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_fcw_write_mmx {m n : Nat} (r : BitVec 3) (v : BitVec n) :
    (Operand.fcw : Operand m).read ((Operand.mmx r : Operand n).write t v) =
      (Operand.fcw : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_mmx_write_fcw {m n : Nat} (r : BitVec 3) (v : BitVec n) :
    (Operand.mmx r : Operand m).read ((Operand.fcw : Operand n).write t v) =
      (Operand.mmx r : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_fcw_write_fsw {m n : Nat} (v : BitVec n) :
    (Operand.fcw : Operand m).read ((Operand.fsw : Operand n).write t v) =
      (Operand.fcw : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_fcw_write_ftw {m n : Nat} (v : BitVec n) :
    (Operand.fcw : Operand m).read ((Operand.ftw : Operand n).write t v) =
      (Operand.fcw : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_fcw_write_fpuPtr {m n : Nat} (v : BitVec n) :
    (Operand.fcw : Operand m).read ((Operand.fpuPtr : Operand n).write t v) =
      (Operand.fcw : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_fpuPtr_write_fpuPtr (v : BitVec 171) :
    (Operand.fpuPtr : Operand 171).read ((Operand.fpuPtr : Operand 171).write t v) = v := by
  simp

@[x86_compose] theorem Operand.read_fpuPtr_write_fpr {m n : Nat} (r : BitVec 3) (v : BitVec n) :
    (Operand.fpuPtr : Operand m).read ((Operand.fpr r : Operand n).write t v) =
      (Operand.fpuPtr : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_fpr_write_fpuPtr {m n : Nat} (r : BitVec 3) (v : BitVec n) :
    (Operand.fpr r : Operand m).read ((Operand.fpuPtr : Operand n).write t v) =
      (Operand.fpr r : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_fpuPtr_write_mmx {m n : Nat} (r : BitVec 3) (v : BitVec n) :
    (Operand.fpuPtr : Operand m).read ((Operand.mmx r : Operand n).write t v) =
      (Operand.fpuPtr : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_mmx_write_fpuPtr {m n : Nat} (r : BitVec 3) (v : BitVec n) :
    (Operand.mmx r : Operand m).read ((Operand.fpuPtr : Operand n).write t v) =
      (Operand.mmx r : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_fpuPtr_write_fsw {m n : Nat} (v : BitVec n) :
    (Operand.fpuPtr : Operand m).read ((Operand.fsw : Operand n).write t v) =
      (Operand.fpuPtr : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_fpuPtr_write_ftw {m n : Nat} (v : BitVec n) :
    (Operand.fpuPtr : Operand m).read ((Operand.ftw : Operand n).write t v) =
      (Operand.fpuPtr : Operand m).read t := id rfl

@[x86_compose] theorem Operand.read_fpuPtr_write_fcw {m n : Nat} (v : BitVec n) :
    (Operand.fpuPtr : Operand m).read ((Operand.fcw : Operand n).write t v) =
      (Operand.fpuPtr : Operand m).read t := id rfl

/-- A memory read after a memory write: the load of the stored-to memory. -/
@[x86_compose] theorem Operand.read_mem_write_mem {m n : Nat} (a b : BitVec 64) (v : BitVec n) :
    (Operand.mem b : Operand m).read ((Operand.mem a : Operand n).write t v) =
      memLoad (memStore t.external a v) b m := id rfl

/-- Reading back a store at the same address and size. -/
@[x86_compose] theorem memLoad_memStore_same (mem : Ram) (a : BitVec 64) {n : Nat} (v : BitVec n)
    (hn : n % 8 = 0) (h128 : n ≤ 128) : memLoad (memStore mem a v) a n = v :=
  memLoad_memStore mem a hn h128 v

/-- Reading back a store of any number of whole bytes up to `2^64` (a `REP` string store). -/
@[x86_compose] theorem memLoad_memStore_same_of_le (mem : Ram) (a : BitVec 64) {n : Nat}
    (v : BitVec n) (hn : n % 8 = 0) (hle : n / 8 ≤ 2 ^ 64) : memLoad (memStore mem a v) a n = v :=
  memLoad_memStore_of_le mem a hn hle v

/-- A 64-bit value is at most `2^64` (the byte count of a `REP` store, `8 * RCX` bits). -/
@[x86_compose] theorem BitVec.toNat_le_two_pow_64 (x : BitVec 64) : x.toNat ≤ 2 ^ 64 :=
  Nat.le_of_lt x.isLt

/-- The offsets `c₁` (`len₁` bytes) and `c₂` (`len₂` bytes) from the same base are apart. -/
def OffsetsApart (c₁ : BitVec 64) (len₁ : Nat) (c₂ : BitVec 64) (len₂ : Nat) : Prop :=
  len₁ ≤ (c₂ - c₁).toNat ∧ len₂ ≤ (c₁ - c₂).toNat

theorem OffsetsApart.ne {c₁ c₂ : BitVec 64} {len₁ len₂ : Nat} (h : OffsetsApart c₁ len₁ c₂ len₂)
    (base : BitVec 64) {i j : Nat} (hi : i < len₁) (hj : j < len₂) (hl : len₁ + len₂ < 2 ^ 64) :
    base + c₁ + BitVec.ofNat 64 i ≠ base + c₂ + BitVec.ofNat 64 j := by
  intro he
  rw [BitVec.add_assoc, BitVec.add_assoc] at he
  have he' := congrArg BitVec.toNat ((BitVec.add_right_inj base).mp he)
  obtain ⟨h1, h2⟩ := h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_sub] at he' h1 h2
  have := c₁.isLt
  have := c₂.isLt
  omega

/-- A load at offset `c₂` from a base after a store at an apart offset `c₁` from it. -/
@[x86_compose] theorem memLoad_memStore_apart (mem : Ram) (base c₁ c₂ : BitVec 64) {n : Nat}
    (v : BitVec n) (k : Nat) (h : OffsetsApart c₁ (n / 8) c₂ (k / 8)) (hn : n ≤ 128)
    (hk : k ≤ 128) :
    memLoad (memStore mem (base + c₁) v) (base + c₂) k = memLoad mem (base + c₂) k := by
  apply memLoad_congr
  intro j hj
  simp only [memByte, PhysicalMemory.read]
  rw [memStore_getElem?_of_ne]
  intro i hi
  exact h.ne base hi hj (by omega)

@[x86_compose] theorem memLoad_memStore_apart_left (mem : Ram) (base c₂ : BitVec 64) {n : Nat}
    (v : BitVec n) (k : Nat) (h : OffsetsApart 0 (n / 8) c₂ (k / 8)) (hn : n ≤ 128)
    (hk : k ≤ 128) :
    memLoad (memStore mem base v) (base + c₂) k = memLoad mem (base + c₂) k := by
  have := memLoad_memStore_apart mem base 0 c₂ v k h hn hk
  simpa using this

@[x86_compose] theorem memLoad_memStore_apart_right (mem : Ram) (base c₁ : BitVec 64) {n : Nat}
    (v : BitVec n) (k : Nat) (h : OffsetsApart c₁ (n / 8) 0 (k / 8)) (hn : n ≤ 128)
    (hk : k ≤ 128) :
    memLoad (memStore mem (base + c₁) v) base k = memLoad mem base k := by
  have := memLoad_memStore_apart mem base c₁ 0 v k h hn hk
  simpa using this

/-- A load after a store to a range apart from it (`RangeApart`), whatever the two bases: the old
load. Not in the simp set (its side condition is a fact about the start state, e.g. that the FS
area a segment-override load reads is apart from a stack slot); pass it with that fact. -/
theorem memLoad_memStore_of_rangeApart (mem : Ram) (a b : BitVec 64) {n : Nat} (v : BitVec n)
    (k : Nat) (h : RangeApart a (n / 8) b (k / 8)) :
    memLoad (memStore mem a v) b k = memLoad mem b k := by
  apply memLoad_congr
  intro j hj
  simp only [memByte, PhysicalMemory.read]
  rw [memStore_getElem?_of_ne]
  intro i hi
  exact h i hi j hj

/-- `OffsetsApart` on literals, by evaluation. -/
@[x86_compose] theorem offsetsApart_iff (c₁ c₂ : BitVec 64) (len₁ len₂ : Nat) :
    OffsetsApart c₁ len₁ c₂ len₂ ↔ len₁ ≤ (c₂ - c₁).toNat ∧ len₂ ≤ (c₁ - c₂).toNat := id Iff.rfl

/-- Reads of the start state are read from memory as `Operand.read` (the form effects use). -/
@[x86_compose] theorem memLoad_external {n : Nat} (a : BitVec 64) :
    memLoad t.external a n = (Operand.mem a : Operand n).read t := id rfl

end Reads

attribute [x86_compose] rax rbx rsi rdi

attribute [x86_compose] AddrMode.reg64 BitVec.add_right_inj AddrMode.addr Disp.value AddrMode.tail Disp.bytes
  AddrMode.addr32
  immBytes_length storeEffect BitVec.add_assoc Option.getD_some Option.getD_none
  Option.isNone_some Option.isNone_none Bool.and_true Bool.and_false Bool.true_and Bool.false_and
  Bool.not_true Bool.not_false List.filter_cons List.filter_nil List.map_cons List.map_nil
  List.cons_append List.nil_append List.any_cons List.any_nil Write.component_reg
  Write.component_mem Write.component_xmm Write.component_mxcsr Write.component_df
  Write.component_fpr Write.component_mmx Write.component_fsw Write.component_ftw
  Write.component_fcw Write.component_fpuPtr Write.component_fcc Component.fpr.injEq
  Operand.fpr.injEq
  Operand.mmx.injEq Bool.or_false
  Bool.false_or
  Bool.or_true Bool.true_or
  StatusFlags.ofRFLAGS_store Write.mk_eq_mk Effect.components List.mem_cons List.mem_nil_iff
  List.mem_singleton List.not_mem_nil beq_self_eq_true beq_iff_eq beq_eq_false_iff_ne Bool.not_eq_true'
  Component.reg.injEq Component.xmm.injEq Component.mem.injEq Operand.reg.injEq Operand.mem.injEq
  BitVec.ofNat_eq_ofNat ite_true ite_false and_true true_and and_false false_and or_false
  false_or or_true true_or not_true not_false_eq_true eq_self_iff_true ne_eq
  Option.some.injEq Option.isSome_some Option.isSome_none Bool.not_eq_false
  BitVec.reduceNeg BitVec.reduceAdd BitVec.reduceSub BitVec.reduceMul BitVec.reduceSetWidth BitVec.reduceSignExtend
  BitVec.reduceToNat BitVec.reduceXOr BitVec.reduceAnd BitVec.reduceOr BitVec.reduceNot
  reduceIte reduceDIte Nat.reduceAdd Nat.reduceSub Nat.reduceMul Nat.reduceDiv Nat.reduceMod
  reduceCtorEq Nat.reduceLeDiff Nat.reduceEqDiff Nat.reduceLT Nat.reduceGT List.length_cons List.length_nil
  List.length_append BitVec.setWidth_eq false_implies implies_true forall_eq
  forall_eq_or_imp and_imp forall_eq' forall_apply_eq_imp_iff₂ forall_apply_eq_imp_iff
  List.forall_mem_cons List.mem_append

/-- Encodability of a literal addressing shape, by `decide` (for the `hv` argument of the memory
triples). -/
instance (am : AddrMode) : Decidable am.Valid := by
  cases am <;> unfold AddrMode.Valid <;> infer_instance

/-! ### Stack frames -/

/-- RSP's value in `s`. -/
@[x86_compose] abbrev rspOf (s : RamState) : BitVec 64 := (Operand.reg 4 : Operand 64).read s

/--
A block precondition for code working on a stack frame: RIP = `p`; the `lo + hi` bytes from
`rsp - lo` are present in RAM, below 4 GiB and above the page tables' frames (`0x3000`, more than
`MemWritable` asks, which is only apart from the entries in them); the block's
`codeLen` bytes at `p` lie below 4 GiB and apart from the frame. Slots
`[rsp + c]` inside it are then readable, writable and apart from the code (`StackFramePre.readable`,
`StackFramePre.writable`, `StackFramePre.apart`), which `x86_mid` uses.
-/
structure StackFramePre (p : BitVec 64) (codeLen lo hi : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  bottom : 0x3000 + lo ≤ (rspOf s).toNat
  top : (rspOf s).toNat + hi ≤ 2 ^ 32
  present : ∀ i < lo + hi, (s.external[rspOf s - BitVec.ofNat 64 lo + BitVec.ofNat 64 i]?).isSome
  codeLow : p.toNat + codeLen ≤ 2 ^ 32
  codeApart : p.toNat + codeLen ≤ (rspOf s).toNat - lo ∨ (rspOf s).toNat + hi ≤ p.toNat

/-- The `len` bytes at offset `c` from RSP lie in the frame (`lo` below RSP, `hi` above), at any
alignment. Decidable for literal offsets. -/
def SlotIn (c : BitVec 64) (len lo hi : Nat) : Prop :=
  (c + BitVec.ofNat 64 lo).toNat + len ≤ lo + hi

instance (c : BitVec 64) (len lo hi : Nat) : Decidable (SlotIn c len lo hi) := by
  unfold SlotIn; infer_instance

namespace StackFramePre

variable {p : BitVec 64} {codeLen lo hi : Nat} {s : RamState}

theorem slot_toNat (h : StackFramePre p codeLen lo hi s) {c : BitVec 64} {len : Nat}
    (hc : SlotIn c len lo hi) :
    (rspOf s + c).toNat = (rspOf s).toNat - lo + (c + BitVec.ofNat 64 lo).toNat := by
  have h1 := hc
  unfold SlotIn at h1
  have hb := h.bottom
  have ht := h.top
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h1 ⊢
  have := c.isLt
  omega

theorem slot_byte (h : StackFramePre p codeLen lo hi s) {c : BitVec 64} {len : Nat}
    (hc : SlotIn c len lo hi) {i : Nat} (hi : i < len) :
    (s.external[rspOf s + c + BitVec.ofNat 64 i]?).isSome := by
  have hs := h.slot_toNat hc
  have h1 := hc
  unfold SlotIn at h1
  have hp := h.present ((c + BitVec.ofNat 64 lo).toNat + i) (by omega)
  have heq : rspOf s + c + BitVec.ofNat 64 i =
      rspOf s - BitVec.ofNat 64 lo + BitVec.ofNat 64 ((c + BitVec.ofNat 64 lo).toNat + i) := by
    apply BitVec.eq_of_toNat_eq
    have hb := h.bottom
    have ht := h.top
    rw [BitVec.toNat_add, hs]
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] at h1 ⊢
    have := c.isLt
    have := (rspOf s).isLt
    omega
  rw [heq]
  exact hp

/-- A slot of the frame can be read. -/
theorem readable (h : StackFramePre p codeLen lo hi s) (c : BitVec 64) {len : Nat}
    (hc : SlotIn c len lo hi) : MemReadable s (rspOf s + c) len := by
  refine ⟨?_, fun i hi => h.slot_byte hc hi⟩
  rw [h.slot_toNat hc]
  have h1 := hc
  unfold SlotIn at h1
  have := h.top
  have := h.bottom
  omega

/-- A slot of the frame can be written. -/
theorem writable (h : StackFramePre p codeLen lo hi s) (c : BitVec 64) {len : Nat}
    (hc : SlotIn c len lo hi) : MemWritable s (rspOf s + c) len := by
  have hs := h.slot_toNat hc
  have h1 := hc
  unfold SlotIn at h1
  have := h.top
  have := h.bottom
  refine ⟨by omega, fun i hi => h.slot_byte hc hi,
    PageTableEntriesApart.of_frames (.inr (by omega))⟩

/-- A slot of the frame is apart from the instruction at offset `off` of the block. -/
theorem apart (h : StackFramePre p codeLen lo hi s) (c : BitVec 64) {len : Nat}
    (hc : SlotIn c len lo hi) (off ilen : Nat) (hoff : off + ilen ≤ codeLen) :
    RangeApart (rspOf s + c) len (p + BitVec.ofNat 64 off) ilen := by
  have hs := h.slot_toNat hc
  have h1 := hc
  unfold SlotIn at h1
  have := h.top
  have := h.bottom
  have := h.codeLow
  have := h.codeApart
  apply RangeApart.of_toNat
  · omega
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · rw [hs]
    generalize (c + BitVec.ofNat 64 lo).toNat = d at h1
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

theorem apart0 (h : StackFramePre p codeLen lo hi s) (c : BitVec 64) {len : Nat}
    (hc : SlotIn c len lo hi) (ilen : Nat) (hoff : ilen ≤ codeLen) :
    RangeApart (rspOf s + c) len p ilen := by
  have := h.apart c hc 0 ilen (by omega)
  simpa using this

end StackFramePre

/-- The frame's slot at RSP itself can be read. -/
theorem StackFramePre.readable0 {p : BitVec 64} {codeLen lo hi : Nat} {s : RamState}
    (h : StackFramePre p codeLen lo hi s) {len : Nat} (hc : SlotIn 0 len lo hi) :
    MemReadable s (rspOf s) len := by
  have := h.readable 0 hc
  rwa [show rspOf s + 0 = rspOf s from BitVec.add_zero _] at this

/-- The frame's slot at RSP itself can be written. -/
theorem StackFramePre.writable0 {p : BitVec 64} {codeLen lo hi : Nat} {s : RamState}
    (h : StackFramePre p codeLen lo hi s) {len : Nat} (hc : SlotIn 0 len lo hi) :
    MemWritable s (rspOf s) len := by
  have := h.writable 0 hc
  rwa [show rspOf s + 0 = rspOf s from BitVec.add_zero _] at this

/-- The frame's slot at RSP itself is apart from the instruction at offset `off`. -/
theorem StackFramePre.apartRsp {p : BitVec 64} {codeLen lo hi : Nat} {s : RamState}
    (h : StackFramePre p codeLen lo hi s) {len : Nat} (hc : SlotIn 0 len lo hi) (off ilen : Nat)
    (hoff : off + ilen ≤ codeLen) : RangeApart (rspOf s) len (p + BitVec.ofNat 64 off) ilen := by
  have := h.apart 0 hc off ilen hoff
  rwa [show rspOf s + 0 = rspOf s from BitVec.add_zero _] at this

/-- The length of a closed list (an instruction encoding at literal operands, a block's bytes),
evaluated: the list is unfolded cell by cell. -/
simproc ↓ [x86_compose] reduceClosedListLength (List.length _) := fun e => do
  let_expr List.length _ l ← e | return .continue
  if e.hasFVar || e.hasMVar || l.isAppOf ``List.cons || l.isAppOf ``List.nil then
    return .continue
  let mut cur := l
  let mut n := 0
  repeat
    let c ← Lean.Meta.withTransparency .default <| Lean.Meta.whnf cur
    match_expr c with
    | List.cons _ _ t => n := n + 1; cur := t
    | List.nil _ => break
    | _ => return .continue
  let lit := Lean.mkNatLit n
  let pf ← Lean.Meta.mkAuxTheorem (← Lean.Meta.mkEq e lit) (← Lean.Meta.mkEqRefl lit)
  return .done { expr := lit, proof? := some pf }

/-! ### Tactics -/

/-- Normal form of composed effects: `Effect.seq` and the instruction effects unfolded, reads of
canonical states evaluated (simp set `x86_compose`), plus any lemmas given. -/
syntax "x86_norm" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| x86_norm $[[$ls,*]]? $[$loc]?) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    `(tactic| simp (config := { decide := true }) only [x86_compose, $ls,*] $[$loc]?)

/-- Close `Effect.Local e` for an instruction effect (simp set `x86_local`), or a composition. -/
macro "x86_local" : tactic => `(tactic| first
  | simp only [x86_local]
  | (apply Effect.Local.seq <;> simp only [x86_local]))

/-- Close `∀ x ∈ codeRange q bytes, x ∈ codeRange p all` for an instruction inside the block. -/
macro "x86_sub" : tactic => `(tactic| first
  | exact codeRange_mem_of_take (by decide +kernel)
  | exact codeRange_mem_of_drop _ (by decide +kernel))

/-- Close `∀ s, P s → ∀ w ∈ (E s).writes, w.Full` for a normalized effect. -/
macro "x86_full" : tactic => `(tactic| (
  intro _ _
  simp (config := { decide := true }) only [x86_compose, List.forall_mem_cons,
    List.forall_mem_nil, List.forall_mem_append, and_true, true_and]))

/-- Close a slot fact about a `StackFramePre` stack frame among the hypotheses (`x86_mid` and
`x86_begin` split the block's precondition into its fields): readable, writable, apart from an
instruction or the block, for a slot `[rsp + c]` or `[rsp]`. The frame and the slot's address are
matched up to reducible unfolding and instances, so a goal that is not a slot fails fast. -/
macro "x86_frame" : tactic => `(tactic| first
  | with_reducible_and_instances (exact StackFramePre.readable (by assumption) _ (by decide +kernel))
  | with_reducible_and_instances (exact StackFramePre.writable (by assumption) _ (by decide +kernel))
  | with_reducible_and_instances
      exact StackFramePre.apart (by assumption) _ (by decide +kernel) _ _ (by decide +kernel)
  | with_reducible_and_instances
      exact StackFramePre.apart0 (by assumption) _ (by decide +kernel) _ (by decide +kernel)
  | with_reducible_and_instances (exact StackFramePre.readable0 (by assumption) (by decide +kernel))
  | with_reducible_and_instances (exact StackFramePre.writable0 (by assumption) (by decide +kernel))
  | with_reducible_and_instances
      exact StackFramePre.apartRsp (by assumption) (by decide +kernel) _ _ (by decide +kernel))

/-- The writes of an effect miss the block's code: each written memory range is apart from it;
the ranges `x86_frame` (or a hypothesis) does not show apart are left as goals. -/
macro "x86_avoid" : tactic => `(tactic| (
  apply Effect.avoids_codeRange
  try x86_norm
  try simp only [x86_pre_simp]
  repeat' apply And.intro
  all_goals (try first
    | with_reducible assumption
    | x86_frame
    | with_reducible_and_instances (exact RangeApart.sub0 (by assumption) _ (by decide +kernel)))))

/-! ### The carry-over tactic -/

namespace Carry

open Lean Meta Elab Tactic

/-- The head constant of `ty`'s conclusion (its foralls stripped, at reducible transparency). -/
partial def conclHead (ty : Expr) : MetaM (Option Name) := do
  let ty ← whnfR ty
  match ty with
  | .forallE n d b bi => withLocalDecl n bi d fun x => conclHead (b.instantiate1 x)
  | _ => return ty.getAppFn.constName?

/-- The leading explicit hypotheses of lemma `n` about the effect: `true` for its
`Effect.Holds`, `false` for its `Obs`. -/
def leadingArgs (n : Name) : MetaM (Array Bool) := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs _ => do
    let mut out := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isExplicit then
        match d.type.getAppFn.constName? with
        | some ``Effect.Holds => out := out.push true
        | some ``Obs => out := out.push false
        | _ => break
    return out

/-- The carry-over lemmas (`@[x86_pre]`) with their conclusions' heads and leading arguments. -/
def preLemmas : MetaM (Array (Name × Option Name × Array Bool)) := do
  let ns ← labelled `x86_pre
  ns.mapM fun n => do
    let ci ← getConstInfo n
    return (n, ← conclHead ci.type, ← leadingArgs n)

/-- What the carry-over works with: the proofs that the block so far holds (`hH`) and that the
state after it agrees with the canonical one (`hO`), the state after it (`s'`), whether to
rewrite reads of `s'` (not at the block's start, where `s'` is the start state), and the
lemmas. -/
structure Ctx where
  hH : Term
  hO : Term
  sv : FVarId
  rewrite : Bool
  obs : Array (TSyntax `Lean.Parser.Tactic.simpLemma)
  pres : Array (Name × Option Name × Array Bool)

/-- `simp only` arguments: each lemma labelled `attr` applied to `arg`. -/
def labelledArgs (attr : Name) (arg : Term) :
    TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := withMainContext do
  let ns ← labelled attr
  let mut out := #[]
  for n in ns do
    let stx ← `($(mkIdent n):ident $arg:term)
    let ok ← try
        let s ← saveState
        discard <| Term.withoutErrToSorry <| elabTerm stx none
        s.restore
        pure true
      catch _ => pure false
    if ok then out := out.push (← `(Lean.Parser.Tactic.simpLemma| $stx:term))
  return out

/-- Close `AddrObs addr`: unfold the address function (`x86_addr`, `x86_pre_simp`) and rewrite
the reads of the second state into the first's (`x86_obs`). -/
elab "x86_addr_obs" : tactic => do
  unless (← instantiateMVars (← getMainTarget)).isAppOf ``AddrObs do
    throwError "x86_addr_obs: not an `AddrObs` goal"
  evalTactic (← `(tactic| refine fun t t' hob => ?_))
  let args ← labelledArgs `x86_obs (← `(hob))
  evalTactic (← `(tactic| simp only [x86_addr, x86_pre_simp, $args,*]))

/-- Close a side goal of a carry-over lemma: a hypothesis (the block's precondition is split into
its fields), an address function's `AddrObs`, or a fact about the canonical state after
normalizing it (`x86_norm`, `x86_pre_simp`): a hypothesis, a stack-frame slot (`x86_frame`). What
is left stays a goal, normalized. -/
macro "x86_side" : tactic => `(tactic| first
  | with_reducible assumption
  | (x86_addr_obs; done)
  | (try simp only [x86_pre_simp]
     try x86_norm
     try simp only [x86_pre_simp]
     first
       | done
       | with_reducible assumption
       | x86_frame
       | with_reducible_and_instances (exact RangeApart.sub (by assumption) _ _ (by decide +kernel))
       | with_reducible_and_instances (exact RangeApart.sub0 (by assumption) _ (by decide +kernel))
       | assumption
       | skip))

/-- The goal is a structure (or `∧`) to split into its fields. -/
def isStructGoal (g : MVarId) : MetaM Bool := do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  unless ← isProp ty do return false
  match ty.getAppFn.constName? with
  | some n =>
    if n == ``Iff || n == ``Eq || n == ``Ne || n == ``HEq then return false
    return isStructure (← getEnv) n
  | none => return false

/-- Close what can be closed of a side goal of a carry-over lemma (`x86_side`), leaving the
rest. -/
def side (g : MVarId) : TacticM (List MVarId) := do
  setGoals [g]
  try evalTactic (← `(tactic| x86_side)) catch _ => pure ()
  getGoals

/-- Carry a precondition over to `s'`: rewrite reads of `s'` to the canonical state, then apply
a carry-over lemma and close its side goals, or split a structure into its fields; a goal that
still mentions `s'` is introduced (a `∀` or `→`) or unfolded (a definition such as an instruction's
`…Ok` predicate) and carried over in turn. What is left is closed as a side goal if possible
(`x86_side`). Returns the goals left; `fuel` bounds the recursion. -/
partial def run (ctx : Ctx) (g : MVarId) (fuel : Nat := 64) : TacticM (List MVarId) := do
  if ← g.isAssigned then return []
  unless ← isProp (← g.getType) do return [g]
  if fuel == 0 then return ← side g
  setGoals [g]
  if ctx.rewrite then
    try evalTactic (← `(tactic| simp only [x86_pre_simp, $(ctx.obs),*])) catch _ => pure ()
  let [g] ← getGoals | return (← getGoals)
  try
    evalTactic (← `(tactic| with_reducible assumption))
    return []
  catch _ => setGoals [g]
  let ty ← instantiateMVars (← g.getType)
  let hd ← g.withContext (conclHead ty)
  for (n, hd', args) in ctx.pres do
    if hd'.isSome && hd != hd' then continue
    let saved ← saveState
    try
      let mut stx : Term := mkIdent n
      for a in args do
        stx ← if a then `($stx $(ctx.hH)) else `($stx $(ctx.hO))
      setGoals [g]
      withReducible <| evalTactic (← `(tactic| apply $stx))
      let gs ← getGoals
      let mut out := []
      for g' in gs do
        if ← g'.isAssigned then continue
        let t ← instantiateMVars (← g'.getType)
        if t.containsFVar ctx.sv && ctx.rewrite then
          out := out ++ (← run ctx g' (fuel - 1))
        else
          out := out ++ (← side g')
      return out
    catch _ =>
      saved.restore
  if ← g.withContext (isStructGoal g) then
    setGoals [g]
    let ok ← try
        withReducible <| evalTactic (← `(tactic| constructor))
        pure true
      catch _ => pure false
    if ok then
      let gs ← getGoals
      let mut out := []
      for g' in gs do
        out := out ++ (← run ctx g' (fuel - 1))
      return out
  if ctx.rewrite && ty.containsFVar ctx.sv then
    let tyR ← g.withContext (whnfR ty)
    if tyR.isForall then
      let (_, g') ← g.intro1P
      return ← run ctx g' (fuel - 1)
    if let some ty' ← g.withContext (unfoldDefinition? tyR) then
      return ← run ctx (← g.change ty') (fuel - 1)
    setGoals [g]
    try
      evalTactic (← `(tactic| simp only [x86_compose, x86_pre_simp, $(ctx.obs),*]))
    catch _ => pure ()
    let [g'] ← getGoals | return (← getGoals)
    return ← side g'
  side g

/-- Add hypothesis `h` and its parts as hypotheses: a conjunction is split all the way (its
parts added, not the conjunction), a structure is added and split into its fields (`depth` levels
of structures); returns the new hypotheses. -/
partial def splitHypAux (h : Expr) (depth : Nat) : TacticM (Array FVarId) := do
  let g ← getMainGoal
  g.withContext do
    let ty0 ← instantiateMVars (← inferType h)
    let ty ← whnf ty0
    unless ← isProp ty do return #[]
    if ty.isAppOfArity ``And 2 then
      let a := ty.appFn!.appArg!
      let b := ty.appArg!
      let l ← splitHypAux (mkApp3 (mkConst ``And.left) a b h) depth
      let r ← splitHypAux (mkApp3 (mkConst ``And.right) a b h) depth
      return l ++ r
    let fv ← if h.isFVar then pure h.fvarId! else do
      let g ← getMainGoal
      let g' ← g.assert (← mkFreshUserName `hP) ty0 h
      let (fv, g'') ← g'.intro1P
      replaceMainGoal [g'']
      pure fv
    let mut out := if h.isFVar then #[] else #[fv]
    if depth == 0 then return out
    let some n := ty.getAppFn.constName? | return out
    if n == ``Iff || n == ``Eq || n == ``Ne || n == ``HEq then return out
    let env ← getEnv
    unless isStructure env n do return out
    for f in getStructureFields env n do
      let proj ← try (← getMainGoal).withContext (mkProjection (mkFVar fv) f) catch _ => continue
      let pty ← (← getMainGoal).withContext do instantiateMVars (← inferType proj)
      unless ← (← getMainGoal).withContext (isProp pty) do continue
      out := out ++ (← splitHypAux proj (depth - 1))
    return out

/-- Simplify hypotheses `fvs` with the `simp only` call `stx` (no error if nothing changes). -/
def simpHyps (stx : Syntax) (fvs : Array FVarId) : TacticM Unit := do
  if fvs.isEmpty then return
  let g ← getMainGoal
  g.withContext do
    let { ctx, simprocs, dischargeWrapper, .. } ← mkSimpContext stx (eraseLocal := false)
    dischargeWrapper.with fun discharge? => do
      let fvs ← fvs.filterM fun fv => return (← g.getDecl).lctx.contains fv
      try
        let (r, _) ← simpGoal g ctx (simprocs := simprocs) (discharge? := discharge?)
          (simplifyTarget := false) (fvarIdsToSimp := fvs)
        match r with
        | none => replaceMainGoal []
        | some (_, g') => replaceMainGoal [g']
      catch _ => pure ()

/-- Split hypothesis `h` into its fields, normalized (`x86_compose`, then `x86_pre_simp`) to the
form `x86_side` brings goals to. -/
def splitHyp (h : Expr) (depth : Nat) : TacticM Unit := do
  let fvs ← splitHypAux h depth
  let fresh : TacticM (Array FVarId) := do
    let g ← getMainGoal
    g.withContext do
      let lctx := (← g.getDecl).lctx
      return lctx.foldl (init := #[]) fun acc d =>
        if d.userName.hasMacroScopes && d.userName.eraseMacroScopes == `hP then
          acc.push d.fvarId
        else acc
  simpHyps (← `(tactic| simp only [x86_pre_simp])) fvs
  if (← getGoals).isEmpty then return
  simpHyps (← `(tactic| simp (config := { decide := true }) only [x86_compose])) (← fresh)
  if (← getGoals).isEmpty then return
  simpHyps (← `(tactic| simp only [x86_pre_simp])) (← fresh)

/-- The precondition of the next instruction after the block so far (`x86_mid`), with the
block's precondition `hP`, the block so far `hH` and its canonical state `hO`. -/
elab "x86_carry_mid " hP:ident hH:ident hO:ident : tactic => do
  let g ← getMainGoal
  let some hPd := (← g.getDecl).lctx.findFromUserName? hP.getId | throwError "no {hP}"
  splitHyp (mkFVar hPd.fvarId) 4
  evalTactic (← `(tactic| have hO1 := $hO true))
  evalTactic (← `(tactic| obtain ⟨_, hg⟩ := Effect.Holds.ofRFLAGS_eq $hH))
  evalTactic (← `(tactic| first
    | refine ⟨?_, Effect.Local.avoids (by x86_local) hO1 ?_⟩
    | refine ⟨?_, ?_⟩))
  let [gpre, gav] ← getGoals | throwError "x86_carry_mid: unexpected goals"
  let hHt : Term := hH
  let hOt ← `(hO1)
  let hgt ← `(Lean.Parser.Tactic.simpLemma| hg)
  let obs ← labelledArgs `x86_obs hOt
  let inv ← labelledArgs `x86_inv hHt
  let sv ← gpre.withContext do
    let ty ← instantiateMVars (← inferType (← elabTerm hHt none))
    match ty.getAppArgs.back? with
    | some (.fvar v) => pure v
    | _ => throwError "x86_carry_mid: no state after the block"
  let ctx : Ctx := { hH := hHt, hO := hOt, sv, rewrite := true, obs := obs ++ inv.push hgt,
                     pres := ← preLemmas }
  let rest ← run ctx gpre
  setGoals [gav]
  try evalTactic (← `(tactic| x86_avoid)) catch _ => pure ()
  let rest' ← getGoals
  setGoals (rest ++ rest')

/-- The first instruction's precondition from the block's (`x86_begin`). -/
elab "x86_carry_begin" : tactic => do
  evalTactic (← `(tactic| intro $(mkIdent `s) $(mkIdent `hP)))
  let g ← getMainGoal
  let some hPd := (← g.getDecl).lctx.findFromUserName? `hP | throwError "no hP"
  splitHyp (mkFVar hPd.fvarId) 4
  let g ← getMainGoal
  let some sd := (← g.getDecl).lctx.findFromUserName? `s | throwError "no s"
  let ctx : Ctx := { hH := ← `(Effect.start_holds $(mkIdent `s)),
                     hO := ← `(Effect.start_obs $(mkIdent `s)),
                     sv := sd.fvarId, rewrite := false, obs := #[], pres := ← preLemmas }
  let rest ← run ctx g
  setGoals rest

/-- The first instruction's writes miss the block's code (`x86_begin`). -/
elab "x86_carry_av" : tactic => do
  evalTactic (← `(tactic| intro $(mkIdent `s) $(mkIdent `hP)))
  let g ← getMainGoal
  let some hPd := (← g.getDecl).lctx.findFromUserName? `hP | throwError "no hP"
  splitHyp (mkFVar hPd.fvarId) 4
  evalTactic (← `(tactic| x86_avoid))

/-- Prove a precondition after an effect from its facts in the canonical state, the hypotheses
of an `of_holds` lemma (`h : e.Holds s s'`, `ho : Obs (e.after s true) s'`). -/
elab "x86_of_holds " hH:ident hO:ident : tactic => do
  try evalTactic (← `(tactic| simp only [x86_pre_simp] at *)) catch _ => pure ()
  evalTactic (← `(tactic| obtain ⟨_, hg⟩ := Effect.Holds.ofRFLAGS_eq $hH))
  let g ← getMainGoal
  let hHt : Term := hH
  let hOt : Term := hO
  let hgt ← `(Lean.Parser.Tactic.simpLemma| hg)
  let obs ← labelledArgs `x86_obs hOt
  let inv := (← labelledArgs `x86_inv hHt).push hgt
  let sv ← g.withContext do
    let ty ← instantiateMVars (← inferType (← elabTerm hHt none))
    match ty.getAppArgs.back? with
    | some (.fvar v) => pure v
    | _ => throwError "x86_of_holds: no state after the effect"
  let ctx : Ctx := { hH := hHt, hO := hOt, sv, rewrite := true, obs := obs ++ inv,
                     pres := ← preLemmas }
  let rest ← run ctx g
  setGoals rest

end Carry

/-- The precondition of the next instruction after the block so far, and its writes missing the
block's code (the `mid` goal of `x86_then`). The block's precondition `hP` is split into its fields;
the precondition is carried over by the `@[x86_pre]` lemmas (`x86_carry_mid`). What is left are the
facts that depend on the data, as goals about the start state `s` (the state after the block is
`s'`, the block so far `hH`, its canonical state `hO`). -/
macro "x86_mid" : tactic => do
  let (s, s', hP, hH, hO) := (Lean.mkIdent `s, Lean.mkIdent `s', Lean.mkIdent `hP,
    Lean.mkIdent `hH, Lean.mkIdent `hO)
  `(tactic| (
    intro $s $s' $hP $hH $hO
    x86_carry_mid $hP $hH $hO))

/-- Start a block with its first instruction's triple `t` (at the block's address). The goal must
be `Triple P code (Effect.post _)`; the first instruction's precondition is carried over from `P`
(split into its fields) as in `x86_mid`, and the side goals not closed automatically come after
the main one. -/
macro "x86_begin " t:term : tactic => `(tactic| (
  refine Triple.block_first ?k $t ?sub ?pre ?av
  try (case sub => x86_sub)
  try (case' pre => x86_carry_begin)
  try (case' av => x86_carry_av)
  case' k => x86_norm))

/-- The next instruction of a block: its triple `t`, composed with `Triple.seq_block`, the composed
effect normalized. Side goals not closed automatically come after the main one. -/
macro "x86_then " t:term : tactic => `(tactic| (
  refine Triple.block_then ?k $t ?loc ?sub ?full ?mid
  try (case loc => x86_local)
  try (case sub => x86_sub)
  try (case full => x86_full)
  try (case' mid => x86_mid)
  case' k => x86_norm))

/-- End a block: the composed effect implies the stated one (given by the lemmas, e.g. its
definition, and algebra the comparison needs). -/
syntax "x86_finish" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| x86_finish $[[$ls,*]]?) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    `(tactic| (
      apply Triple.block_end
      intro s s' _ hH
      apply hH.weaken
      · x86_norm [$ls,*]
      · x86_norm [$ls,*]
      · intro i; cases i <;> x86_norm [$ls,*]
      · x86_norm [$ls,*]))

/-- Prove `Effect.Local` of an effect from its definition (the lemmas given): every read is of
the observable state (operands, general-purpose registers, MXCSR, the non-status bits of RFLAGS,
addresses), the flags depend on the old flags at most flag by flag. -/
syntax "effect_local" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| effect_local [$ls,*]) => `(tactic| (
    refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_, fun t t' h i hi => ?_,
      fun t => ?_⟩
    · simp [$ls,*, h.read_reg, h.read_mem, h.read_xmm, h.read_regHigh, h.read_mxcsr, h.read_df,
      h.read_fpr, h.read_mmx, h.read_fsw, h.read_ftw, h.read_fcw, h.read_fpuPtr, h.read_gpr8,
      h.read_byteReg, h.gpr, h.mxcsr, h.dfBit, h.rflags, h.cs, AddrMode.addr_obs h,
      AddrMode.addr32_obs h]
    · simp [$ls,*, h.read_reg, h.read_mem, h.read_xmm, h.read_regHigh, h.read_mxcsr, h.read_df,
      h.read_fpr, h.read_mmx, h.read_fsw, h.read_ftw, h.read_fcw, h.read_fpuPtr, h.read_gpr8,
      h.read_byteReg, h.gpr, h.mxcsr, h.dfBit, h.rflags, h.cs, AddrMode.addr_obs h,
      AddrMode.addr32_obs h]
    · simp [$ls,*, h.read_reg, h.read_mem, h.read_xmm, h.read_regHigh, h.read_mxcsr, h.read_df,
      h.read_fpr, h.read_mmx, h.read_fsw, h.read_ftw, h.read_fcw, h.read_fpuPtr, h.read_gpr8,
      h.read_byteReg, h.gpr, h.mxcsr, h.dfBit, h.rflags, h.cs, AddrMode.addr_obs h,
      AddrMode.addr32_obs h]
    · cases i <;> simp_all [$ls,*, Effect.flag, StatusFlagsOutcome.get, StatusFlags.get, StatusFlagsOutcome.ofStatusFlags,
        h.read_reg, h.read_mem, h.read_xmm, h.read_regHigh, h.read_mxcsr, h.read_df,
      h.read_fpr, h.read_mmx, h.read_fsw, h.read_ftw, h.read_fcw, h.read_fpuPtr, h.read_gpr8,
      h.read_byteReg, h.gpr, h.mxcsr, h.dfBit, h.rflags, h.cs, AddrMode.addr_obs h,
          AddrMode.addr32_obs h] <;>
        split <;> simp_all
    · simp [$ls,*, Write.Full, Operand.Full]))

end X86Proofs
