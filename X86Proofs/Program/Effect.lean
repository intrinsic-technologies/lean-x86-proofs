import X86Proofs.Program.Triple
import X86Proofs.Program.ComposeAttr

/-!
# Effects: one shape for every instruction's postcondition

Every instruction triple has the postcondition `Effect.post e` for an effect `e : RamState →
Effect`, which lists, as functions of the start state `s`:

- `rip`: the next RIP;
- `writes`: each location the instruction writes (a register or memory operand, MXCSR, the
  direction flag) with its new value;
- `flags`: what it does to the six status flags, each set to a value or left undefined, or
  `none` if it leaves them alone.

The values are stated directly (RAX is this, ZF is that), never as "some value satisfying …", so
a later instruction's precondition can read them off. The one exception are values lean-x86 draws
from its oracle: undefined flags (`none`) and undefined x87 condition codes (a write of
`Operand.fcc m` with the defined codes in the mask `m`; the codes outside it are some value).

`Effect.Holds e s s'` says `s'` is `s` with exactly that effect: RIP, the written locations and the
flags as listed, and everything else as before (`AgreesExcept` over the components the effect
lists, `Effect.components`). The frame list is derived from the writes, so no triple writes it by
hand.

Two rules work on any effect:

- `Triple.of_effect`: a triple from a step with the effect (`StepEffect`, which every encoding of a
  one-step form states as `<encoding>_effect_step`, e.g. `xor_r64_r64_effect_step`). The code staying in memory follows from the effect avoiding
  the code bytes (`Effect.Avoids`).
- `Triple.seq_append`: two effect triples in sequence, on the concatenated code. Each effect must avoid the
  other triple's code; the result relates the start and end states through the intermediate one.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- `o` allows the flag value `b`: `some v` allows only `v`, `none` (undefined) allows
anything. -/
def FlagAllows : Option Bool → Bool → Prop
  | some v, b => b = v
  | none, _ => True

/-- What an instruction does to each of the six status flags: `some v` sets it to `v`, `none`
leaves it undefined (lean-x86 takes it from the oracle). A flag the instruction does not write is
`some` of its old value. -/
structure StatusFlagsOutcome where
  CF : Option Bool
  PF : Option Bool
  AF : Option Bool
  ZF : Option Bool
  SF : Option Bool
  OF : Option Bool

/-- Every flag set, to its value in `f`. -/
def StatusFlagsOutcome.ofStatusFlags (f : StatusFlags) : StatusFlagsOutcome :=
  ⟨some f.CF, some f.PF, some f.AF, some f.ZF, some f.SF, some f.OF⟩

/-- The flag values `f` are allowed by `e`. -/
def StatusFlagsOutcome.Allows (e : StatusFlagsOutcome) (f : StatusFlags) : Prop :=
  FlagAllows e.CF f.CF ∧ FlagAllows e.PF f.PF ∧ FlagAllows e.AF f.AF ∧ FlagAllows e.ZF f.ZF ∧
    FlagAllows e.SF f.SF ∧ FlagAllows e.OF f.OF

/-- A write: operand `dst` (a general-purpose register, memory, an XMM register, MXCSR, the
direction flag, or a part of the x87 state; `n` bits) gets the value `val`. A write of the x87
condition codes `Operand.fcc m` states only the codes selected by `m`: the others may change to
values the effect does not give (an x87 instruction leaves them undefined); `Operand.fcc 0`
states none. -/
structure Write where
  {n : Nat}
  dst : Operand n
  val : BitVec n

/-- The component of the state a write touches: a register, or the `n / 8` bytes at a memory
address (`Operand.component`). -/
def Write.component (w : Write) : Component := w.dst.component

@[simp] theorem Write.component_reg {n : Nat} (r : BitVec 5) (v : BitVec n) :
    (⟨.reg r, v⟩ : Write).component = .reg r := rfl

@[simp] theorem Write.component_mem {n : Nat} (addr : BitVec 64) (v : BitVec n) :
    (⟨.mem addr, v⟩ : Write).component = .mem addr (n / 8) := rfl

@[simp] theorem Write.component_xmm {n : Nat} (r : BitVec 5) (v : BitVec n) :
    (⟨.xmm r, v⟩ : Write).component = .xmm r := rfl

@[simp] theorem Write.component_regHigh {n : Nat} (r : BitVec 5) (v : BitVec n) :
    (⟨.regHigh r, v⟩ : Write).component = .reg r := rfl

@[simp] theorem Write.component_mxcsr {n : Nat} (v : BitVec n) :
    (⟨.mxcsr, v⟩ : Write).component = .mxcsr := rfl

@[simp] theorem Write.component_df {n : Nat} (v : BitVec n) :
    (⟨.df, v⟩ : Write).component = .df := rfl

@[simp] theorem Write.component_fpr {n : Nat} (r : BitVec 3) (v : BitVec n) :
    (⟨.fpr r, v⟩ : Write).component = .fpr r := rfl

@[simp] theorem Write.component_mmx {n : Nat} (r : BitVec 3) (v : BitVec n) :
    (⟨.mmx r, v⟩ : Write).component = .fpr r := rfl

@[simp] theorem Write.component_fsw {n : Nat} (v : BitVec n) :
    (⟨.fsw, v⟩ : Write).component = .fsw := rfl

@[simp] theorem Write.component_ftw {n : Nat} (v : BitVec n) :
    (⟨.ftw, v⟩ : Write).component = .ftw := rfl

@[simp] theorem Write.component_fcw {n : Nat} (v : BitVec n) :
    (⟨.fcw, v⟩ : Write).component = .fcw := rfl

@[simp] theorem Write.component_fpuPtr {n : Nat} (v : BitVec n) :
    (⟨.fpuPtr, v⟩ : Write).component = .fpuPtr := rfl

@[simp] theorem Write.component_fcc {n : Nat} (m : BitVec 4) (v : BitVec n) :
    (⟨.fcc m, v⟩ : Write).component = .fcc := rfl

/-- After `s'`, every write in the list holds: its operand reads its value. -/
def Write.AllHold (s' : RamState) : List Write → Prop
  | [] => True
  | [w] => w.dst.read s' = w.val
  | w :: ws => w.dst.read s' = w.val ∧ Write.AllHold s' ws

/-- An instruction's effect from a given start state: next RIP, the writes, and the status flags
(`none` if untouched). -/
structure Effect where
  rip : BitVec 64
  writes : List Write := []
  flags : Option StatusFlagsOutcome := none

/-- The components an effect may change, its write footprint: the written
locations, the flags (if written) and RIP. -/
def Effect.components (e : Effect) : List Component :=
  e.writes.map Write.component ++
    (match e.flags with
      | some _ => [.flags]
      | none => []) ++ [.rip]

/-- The status flags of `s'` are as `e` says. (DF is a write, `Operand.df`; the other bits of
RFLAGS, and the status flags if `e` leaves them alone, are kept by `AgreesExcept`.) -/
def Effect.FlagsHold (e : Effect) (s' : RamState) : Prop :=
  match e.flags with
  | some fe => fe.Allows (StatusFlags.ofRFLAGS s'.RFLAGS)
  | none => True

theorem StatusFlagsOutcome.allows_ofStatusFlags (f : StatusFlags) : (StatusFlagsOutcome.ofStatusFlags f).Allows f :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Flags stored into RFLAGS are allowed if the flags are. -/
theorem StatusFlagsOutcome.allows_store {fe : StatusFlagsOutcome} {f : StatusFlags} (h : fe.Allows f)
    (r : BitVec 64) : fe.Allows (StatusFlags.ofRFLAGS (f.store r)) := by
  rw [StatusFlags.ofRFLAGS_store]
  exact h

/-- `s'` is `s` with effect `e`: RIP, the writes and the flags as listed, everything else (outside
`e.components` and the per-step bookkeeping) as before. -/
structure Effect.Holds (e : Effect) (s s' : RamState) : Prop where
  rip : s'.RIP = e.rip
  writes : Write.AllHold s' e.writes
  flags : e.FlagsHold s'
  agrees : AgreesExcept e.components s s'

/-- The postcondition of a triple with effect `e`. -/
def Effect.post (e : RamState → Effect) (s s' : RamState) : Prop := (e s).Holds s s'

/-- No memory write of `e` touches the bytes of `code`. -/
def Effect.Avoids (e : Effect) (code : CodeMap) : Prop :=
  ∀ x ∈ code, ∀ c ∈ e.components, ¬ c.Covers x.1

/-- An effect that writes no memory avoids any code. -/
theorem Effect.Avoids.of_noMem {e : Effect} (h : ∀ c ∈ e.components, ∀ x, ¬ c.Covers x)
    (code : CodeMap) : e.Avoids code :=
  fun x _ c hc => h c hc x.1

/-- Code that an effect avoids stays in memory. -/
theorem Effect.Holds.codeIn {e : Effect} {s s' : RamState} {code : CodeMap} (h : e.Holds s s')
    (hav : e.Avoids code) (hin : CodeIn code s) : CodeIn code s' :=
  CodeIn.of_agreesExcept h.agrees hav hin

/-- Two effects in sequence change only the components of both. -/
theorem Effect.Holds.trans {e₁ e₂ : Effect} {s s₁ s₂ : RamState} (h₁ : e₁.Holds s s₁)
    (h₂ : e₂.Holds s₁ s₂) : AgreesExcept (e₁.components ++ e₂.components) s s₂ :=
  h₁.agrees.trans h₂.agrees

/--
One step with effect `e`: from every ready state with `code` in memory satisfying `pre`, `step`
runs normally to a state that is ready to step and is the start state with effect `e s`. Every
encoding of a one-step instruction form states this as `<encoding>_effect_step`, and its triple follows by
`Triple.of_effect`; a proof about a whole run (`Program/Execution.lean`) uses it directly, step by
step, through `StepEffect.advances` and `StepEffect.returns`.
-/
def StepEffect [Bindings] (pre : RamState → Prop) (code : CodeMap) (e : RamState → Effect) :
    Prop :=
  ∀ s, ReadyToStep s → CodeIn code s → pre s → ∃ s',
    X86.Machine.step s = some (.next s') ∧ ReadyToStep s' ∧ (e s).Holds s s'

/-- A step with an effect under a precondition is one under any stronger precondition. -/
theorem StepEffect.mono_pre [Bindings] {pre pre' : RamState → Prop} {code : CodeMap}
    {e : RamState → Effect} (h : StepEffect pre code e) (hpre : ∀ s, pre' s → pre s) :
    StepEffect pre' code e :=
  fun s hready hcode hs => h s hready hcode (hpre s hs)

namespace Triple

variable [Bindings] {pre pre₁ pre₂ : RamState → Prop} {code code₁ code₂ : CodeMap}
  {e e₁ e₂ : RamState → Effect}

/--
A triple from a step with an effect (`StepEffect pre code e`). If that effect avoids the code, the
triple with postcondition `Effect.post e` holds (with one step).
-/
theorem of_effect (hav : ∀ s, pre s → (e s).Avoids code) (h : StepEffect pre code e) :
    Triple pre code (Effect.post e) :=
  of_step fun s hready hcode hpre => by
    obtain ⟨s', hstep, hready', hh⟩ := h s hready hcode hpre
    exact ⟨s', hstep, hready', hh.codeIn (hav s hpre) hcode, hh⟩

/--
Sequencing two effect triples on the concatenated code. The first effect must avoid the second
triple's code and the second effect the first's (`hav₁`, `hav₂`); the first postcondition must lead
to the second precondition (`hmid`).
-/
theorem seq_append (h₁ : Triple pre₁ code₁ (Effect.post e₁)) (h₂ : Triple pre₂ code₂ (Effect.post e₂))
    (hav₁ : ∀ s, pre₁ s → (e₁ s).Avoids code₂) (hav₂ : ∀ s, pre₂ s → (e₂ s).Avoids code₁)
    (hmid : ∀ s s', pre₁ s → (e₁ s).Holds s s' → pre₂ s') :
    Triple pre₁ (code₁ ++ code₂) fun s s₂ => ∃ s₁, (e₁ s).Holds s s₁ ∧ (e₂ s₁).Holds s₁ s₂ := by
  intro s hready hcode hpre
  obtain ⟨hcode₁, hcode₂⟩ := CodeIn.append_iff.mp hcode
  obtain ⟨n₁, hready₁, hcode₁', hpost₁⟩ := h₁ s hready hcode₁ hpre
  have hpre₂ := hmid _ _ hpre hpost₁
  obtain ⟨n₂, hready₂, hcode₂', hpost₂⟩ :=
    h₂ _ hready₁ (hpost₁.codeIn (hav₁ s hpre) hcode₂) hpre₂
  refine ⟨n₂ + n₁, ?_⟩
  rw [nextStates_add]
  exact ⟨hready₂, CodeIn.append_iff.mpr ⟨hpost₂.codeIn (hav₂ _ hpre₂) hcode₁', hcode₂'⟩, _,
    hpost₁, hpost₂⟩

end Triple

attribute [x86_compose] StatusFlagsOutcome.ofStatusFlags

end X86Proofs
