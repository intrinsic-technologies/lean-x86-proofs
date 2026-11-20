import X86Proofs.Program.Code
import X86Proofs.Program.Agrees

/-!
# Hoare triples over lean-x86's `step`

Phase 1 of Myreen, Gordon and Slind's *Decompilation into Logic — Improved* (FMCAD 2012): a
triple per instruction, derived from its step theorem, and rules that compose triples into
program proofs.

`Triple pre code post`: from any state that is ready to step, has `code` in memory and satisfies
`pre`, running some number of steps reaches a state that is again ready to step, still has `code`
in memory, and is related to the start state by `post`. The postcondition is a relation between
the start and the end state, so it can say "RAX is the old RAX xor the old RBX" and "everything
else is as before" without naming the old values in the precondition.

A triple promises to keep its own code in memory. Unlike the paper it does not quantify over
extra code: an instruction that writes memory cannot keep arbitrary other code intact, only the
code outside the bytes it writes. Adding code to a triple (`Triple.subset_code`, `Triple.add_code`)
therefore asks that the postcondition keep the added code, which an `AgreesExcept`
postcondition does for code outside its memory components (`CodeIn.of_agreesExcept`).

States are lean-x86's `RamState`, and `nextState` is one `step`: its `.next` state if it returns
one, else the state unchanged. This conflates a program that has ended or failed with one that stutters
in place; triples here only ever use states where `step` returns `.next`, but a triple whose
postcondition holds of its start state is satisfied with zero steps whatever `step` does.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- One step: the `.next` state of `step s`, or `s` itself if `step` ends, fails or is
undefined. -/
def nextState [Bindings] (s : RamState) : RamState :=
  match X86.Machine.step s with
  | some (.next s') => s'
  | _ => s

/-- `n` steps. -/
def nextStates [Bindings] (n : Nat) (s : RamState) : RamState := Nat.repeat nextState n s

theorem nextState_of_step [Bindings] {s s' : RamState} (h : X86.Machine.step s = some (.next s')) :
    nextState s = s' := by
  simp [nextState, h]

theorem nextStates_zero [Bindings] (s : RamState) : nextStates 0 s = s := rfl

theorem nextStates_one [Bindings] (s : RamState) : nextStates 1 s = nextState s := rfl

theorem nextStates_add [Bindings] (m n : Nat) (s : RamState) :
    nextStates (m + n) s = nextStates m (nextStates n s) := by
  induction m with
  | zero => simp [nextStates_zero]
  | succ m ih => rw [Nat.add_right_comm]; exact congrArg nextState ih

/--
`Triple pre code post`: from any state `s` that is ready to step, has `code` in memory and
satisfies `pre s`, some number of steps reaches a state `s'` that is ready to step, still has
`code` in memory, and satisfies `post s s'`.
-/
def Triple [Bindings] (pre : RamState → Prop) (code : CodeMap)
    (post : RamState → RamState → Prop) : Prop :=
  ∀ s : RamState, ReadyToStep s → CodeIn code s → pre s →
    ∃ n, ReadyToStep (nextStates n s) ∧ CodeIn code (nextStates n s) ∧ post s (nextStates n s)

namespace Triple

variable [Bindings] {pre pre' mid : RamState → Prop} {post post' post₁ post₂ :
  RamState → RamState → Prop} {code code' : CodeMap}

/--
Sequencing. If `post₁` leads to the second triple's precondition, running the first triple and
then the second relates the start and end states by the composition of the two postconditions.
-/
theorem seq (h₁ : Triple pre code post₁) (h₂ : Triple mid code post₂)
    (hmid : ∀ s s', pre s → post₁ s s' → mid s') :
    Triple pre code fun s s'' => ∃ s', post₁ s s' ∧ post₂ s' s'' := by
  intro s hready hcode hpre
  obtain ⟨n₁, hready₁, hcode₁, hpost₁⟩ := h₁ s hready hcode hpre
  obtain ⟨n₂, hready₂, hcode₂, hpost₂⟩ := h₂ _ hready₁ hcode₁ (hmid _ _ hpre hpost₁)
  refine ⟨n₂ + n₁, ?_⟩
  rw [nextStates_add]
  exact ⟨hready₂, hcode₂, _, hpost₁, hpost₂⟩

/--
A triple still holds for any larger code (every byte of `code` is in `code'`), if its
postcondition keeps that code in memory (`hkeep`; for an `AgreesExcept` postcondition,
`CodeIn.of_agreesExcept`).
-/
theorem subset_code (h : Triple pre code post) (hsub : ∀ x ∈ code, x ∈ code')
    (hkeep : ∀ s s', pre s → post s s' → CodeIn code' s → CodeIn code' s') :
    Triple pre code' post := by
  intro s hready hcode hpre
  obtain ⟨n, hready', -, hpost⟩ := h s hready (hcode.mono hsub) hpre
  exact ⟨n, hready', hkeep _ _ hpre hpost hcode, hpost⟩

/-- Adding code at the end: `{pre} code {post}` gives `{pre} code ++ more {post}` if `post`
keeps `more` in memory. -/
theorem add_code (h : Triple pre code post) (more : CodeMap)
    (hkeep : ∀ s s', pre s → post s s' → CodeIn more s → CodeIn more s') :
    Triple pre (code ++ more) post := by
  intro s hready hcode hpre
  have hboth := CodeIn.append_iff.mp hcode
  obtain ⟨n, hready', hcode', hpost⟩ := h s hready hboth.1 hpre
  exact ⟨n, hready', CodeIn.append_iff.mpr ⟨hcode', hkeep _ _ hpre hpost hboth.2⟩, hpost⟩

/-- Consequence: strengthen the precondition, weaken the postcondition. -/
theorem conseq (h : Triple pre code post) (hpre : ∀ s, pre' s → pre s)
    (hpost : ∀ s s', pre' s → post s s' → post' s s') : Triple pre' code post' := by
  intro s hready hcode hpre'
  obtain ⟨n, hready', hcode', hp⟩ := h s hready hcode (hpre s hpre')
  exact ⟨n, hready', hcode', hpost _ _ hpre' hp⟩

/-- A triple from a one-step (`nextState`) fact. -/
theorem of_nextState
    (h : ∀ s, ReadyToStep s → CodeIn code s → pre s →
      ReadyToStep (nextState s) ∧ CodeIn code (nextState s) ∧ post s (nextState s)) :
    Triple pre code post :=
  fun s hready hcode hpre => ⟨1, h s hready hcode hpre⟩

/--
A triple from a step theorem. If, from every ready state with `code` in memory satisfying `pre`,
`step` runs normally to a state that is ready to step, still has `code` in memory and satisfies
`post`, the triple holds (with one step).
-/
theorem of_step
    (h : ∀ s, ReadyToStep s → CodeIn code s → pre s → ∃ s',
      X86.Machine.step s = some (.next s') ∧ ReadyToStep s' ∧ CodeIn code s' ∧ post s s') :
    Triple pre code post :=
  of_nextState fun s hready hcode hpre => by
    obtain ⟨s', hstep, hready', hcode', hpost⟩ := h s hready hcode hpre
    rw [nextState_of_step hstep]
    exact ⟨hready', hcode', hpost⟩

end Triple

end X86Proofs
