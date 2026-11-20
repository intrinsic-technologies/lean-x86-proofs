import X86Proofs.Program.ReadWrite.Stack
import Prelude.Execution.Termination

/-!
# Executions: runs of the return-boundary runner

lean-x86's `Runner.run boundary fuel s` steps `s` until it reaches the caller's return boundary
(RIP and RSP both as in `boundary`) or runs out of fuel. A program theorem is stated about it, so a
proof about a whole function composes runner executions:

- `Advances boundary n s t`: `n` steps from `s` reach `t` without hitting the boundary.
- `Returns boundary n s t`: within `n` steps from `s` the run reaches the boundary, at `t`.
- `AtBoundary boundary t`: `t` is at the boundary, RIP its return address and RSP its stack
  pointer.

`Advances.trans` and `Advances.returns` compose them; `Advances.of_step` and `Returns.of_step` make
one from a single architectural step, and `StepEffect.advances` and `StepEffect.returns` from an
instruction's step with its effect (`<encoding>_effect_step`). A return ends at the boundary
(`Returns.atBoundary`). `Returns.unique` gives the least fuel and the unique final state
`Prelude.UniqueExecution` asks for, for a run to `returnBoundary s`: `nearReturn64Boundary_eq` shows
that lean-x86's `Prelude.nearReturn64Boundary`, which pops the return address with `Pop_Stack`,
succeeds with that boundary when the return slot is readable.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- Running `m + n` steps is running `m`, then (if the run neither returned nor failed) `n` more
from where it stopped. -/
theorem runSteps_add (transition : RamState → Option RunStepResult)
    (m n : Nat) (s : RamState) :
    runSteps transition (m + n) s =
      (runSteps transition m s).bind (fun result =>
        match result with
        | .outOfFuel t => runSteps transition n t
        | result => some result) := by
  induction m generalizing s with
  | zero => simp [runSteps]
  | succ m ih =>
      simp only [Nat.succ_add, runSteps]
      cases h : transition s with
      | none => rfl
      | some result =>
          cases result <;> simp [ih]

/-- A run that returned within `m` steps returns the same state with any more fuel. -/
theorem runSteps_returned_add (transition : RamState → Option RunStepResult)
    {m : Nat} {s t : RamState}
    (h : runSteps transition m s = some (.returned t)) (n : Nat) :
    runSteps transition (m + n) s = some (.returned t) := by
  rw [runSteps_add, h]
  rfl

/-- `fuel` runner steps from `s` reach `t` without reaching the return boundary. -/
noncomputable def Advances [instBindings : X86.Machine.Bindings]
    (boundary : ReturnBoundary) (fuel : Nat) (s t : RamState) : Prop :=
  Runner.run boundary fuel s = some (.outOfFuel t)

/-- Within `fuel` runner steps from `s` the run reaches the return boundary, at `t`. -/
noncomputable def Returns [instBindings : X86.Machine.Bindings]
    (boundary : ReturnBoundary) (fuel : Nat) (s t : RamState) : Prop :=
  Runner.run boundary fuel s = some (.returned t)

/-- The machine is at the boundary: the runner returns there. -/
def AtBoundary (boundary : ReturnBoundary) (t : RamState) : Prop :=
  t.RIP = boundary.rip ∧ t.GPR[4] = boundary.rsp

/-- Zero steps advance exactly to the start state. -/
@[simp] theorem advances_zero [instBindings : X86.Machine.Bindings]
    (boundary : ReturnBoundary) (s t : RamState) :
    Advances boundary 0 s t ↔ s = t := by
  simp [Advances, Runner.run, runSteps]

/-- One runner step that continues is a one-step advance. -/
theorem advances_one [instBindings : X86.Machine.Bindings]
    {boundary : ReturnBoundary} {s t : RamState}
    (h : Runner.step boundary s = some (.next t)) :
    Advances boundary 1 s t := by
  simp [Advances, Runner.run, runSteps, h]

/-- One runner step that reaches the boundary is a one-step return. -/
theorem returns_one [instBindings : X86.Machine.Bindings]
    {boundary : ReturnBoundary} {s t : RamState}
    (h : Runner.step boundary s = some (.returned t)) :
    Returns boundary 1 s t := by
  simp [Returns, Runner.run, runSteps, h]

/-- Advances compose: `m` steps to `t`, then `n` steps to `u`. -/
theorem Advances.trans [instBindings : X86.Machine.Bindings]
    {boundary : ReturnBoundary} {m n : Nat} {s t u : RamState}
    (h₁ : Advances boundary m s t) (h₂ : Advances boundary n t u) :
    Advances boundary (m + n) s u := by
  unfold Advances Runner.run at *
  rw [runSteps_add, h₁]
  exact h₂

/-- An advance followed by a return is a return. -/
theorem Advances.returns [instBindings : X86.Machine.Bindings]
    {boundary : ReturnBoundary} {m n : Nat} {s t u : RamState}
    (h₁ : Advances boundary m s t) (h₂ : Returns boundary n t u) :
    Returns boundary (m + n) s u := by
  unfold Advances Returns Runner.run at *
  rw [runSteps_add, h₁]
  exact h₂

/-- A return within `m` steps is one within any `n ≥ m` steps, to the same state. -/
theorem Returns.mono [instBindings : X86.Machine.Bindings]
    {boundary : ReturnBoundary} {m n : Nat} {s t : RamState}
    (h : Returns boundary m s t) (hle : m ≤ n) :
    Returns boundary n s t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact runSteps_returned_add _ h k

/-- A successful architectural step continues unless it reaches the caller's boundary. -/
theorem Advances.of_step [Bindings] {boundary : ReturnBoundary} {s t : RamState}
    (h : Machine.step s = some (.next t))
    (hne : t.RIP ≠ boundary.rip ∨ t.GPR[4] ≠ boundary.rsp) :
    Advances boundary 1 s t := by
  apply advances_one
  rcases hne with hip | hsp
  · simp [Runner.step, h, hip]
  · simp only [Runner.step, h, Option.map_some]
    change some (if t.RIP == boundary.rip && t.GPR[4] == boundary.rsp then
      RunStepResult.returned t else RunStepResult.next t) = _
    simp [hsp]

/-- A successful architectural step reaches the caller when both RIP and RSP match. -/
theorem Returns.of_step [Bindings] {boundary : ReturnBoundary} {s t : RamState}
    (h : Machine.step s = some (.next t))
    (hip : t.RIP = boundary.rip) (hsp : t.GPR[4] = boundary.rsp) :
    Returns boundary 1 s t := by
  apply returns_one
  simp only [Runner.step, h, Option.map_some]
  change some (if t.RIP == boundary.rip && t.GPR[4] == boundary.rsp then
      RunStepResult.returned t else RunStepResult.next t) = _
  simp [hip, hsp]

/-- A runner step that returns does so at the boundary: RIP at its return address, RSP at its
stack pointer. -/
theorem Runner.step_returned [Bindings] {boundary : ReturnBoundary} {s t : RamState}
    (h : Runner.step boundary s = some (.returned t)) : AtBoundary boundary t := by
  unfold Runner.step at h
  cases hs : Machine.step s with
  | none => simp [hs] at h
  | some r =>
    rw [hs] at h
    cases r with
    | next u =>
      simp only [Option.map_some, Option.some.injEq] at h
      split at h
      · rename_i hb
        cases h
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        exact ⟨hb.1, hb.2⟩
      · cases h
    | ended _ _ => simp at h
    | failed _ _ => simp at h

/-- The runner returns only at the boundary: the final state's RIP and RSP are the boundary's. -/
theorem Returns.atBoundary [Bindings] {boundary : ReturnBoundary} :
    ∀ {n : Nat} {s t : RamState}, Returns boundary n s t → AtBoundary boundary t
  | 0, _, _, h => by simp [Returns, Runner.run, runSteps] at h
  | n + 1, s, t, h => by
    unfold Returns Runner.run at h
    simp only [runSteps] at h
    cases hs : Runner.step boundary s with
    | none => simp [hs] at h
    | some r =>
      rw [hs] at h
      cases r with
      | next u => exact Returns.atBoundary (n := n) h
      | returned u =>
        have hu : u = t := by simpa using h
        subst hu
        exact Runner.step_returned hs
      | ended _ _ => simp at h
      | failed _ => simp at h
      | reachedOSEntry _ _ => simp at h

/--
An instruction's step with its effect (`<encoding>_effect_step`) as one runner step that continues: if
the effect's next RIP is not the boundary's, one step from a ready state with the code in memory
and the precondition advances to a ready state with the effect.
-/
theorem StepEffect.advances [Bindings] {pre : RamState → Prop} {code : CodeMap}
    {e : RamState → Effect} (h : StepEffect pre code e) {boundary : ReturnBoundary}
    {s : RamState} (hready : ReadyToStep s) (hcode : CodeIn code s) (hpre : pre s)
    (hne : (e s).rip ≠ boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ (e s).Holds s t := by
  obtain ⟨t, hstep, hready', he⟩ := h s hready hcode hpre
  exact ⟨t, Advances.of_step hstep (.inl (he.rip ▸ hne)), hready', he⟩

/--
An instruction's step with its effect as the runner step that returns: if the effect's next RIP
is the boundary's and the effect leaves RSP at the boundary's, one step from a ready state with the
code in memory and the precondition returns, at a state with the effect.
-/
theorem StepEffect.returns [Bindings] {pre : RamState → Prop} {code : CodeMap}
    {e : RamState → Effect} (h : StepEffect pre code e) {boundary : ReturnBoundary}
    {s : RamState} (hready : ReadyToStep s) (hcode : CodeIn code s) (hpre : pre s)
    (hip : (e s).rip = boundary.rip) (hsp : ∀ t, (e s).Holds s t → t.GPR[4] = boundary.rsp) :
    ∃ t, Returns boundary 1 s t ∧ (e s).Holds s t := by
  obtain ⟨t, hstep, -, he⟩ := h s hready hcode hpre
  exact ⟨t, Returns.of_step hstep (he.rip.trans hip) (hsp t he), he⟩

/--
The return boundary of a plain 64-bit near return from `s`: RIP is the 8 bytes at RSP, and RSP
advances past them. This is lean-x86's `Prelude.nearReturn64Boundary s` when the return slot can
be read (`nearReturn64Boundary_eq`).
-/
def returnBoundary (s : RamState) : ReturnBoundary :=
  { rip := (Operand.mem (stackPtr s) : Operand 64).read s, rsp := stackPtr s + 8 }

/--
lean-x86's `Prelude.nearReturn64Boundary` pops the return address with `Pop_Stack`; with the flat
stack segment and the 8 bytes at RSP readable, it succeeds with `returnBoundary s`.
-/
theorem nearReturn64Boundary_eq [Bindings] (s : RamState) (h : DataReady s)
    (hss : s.SS = userStackSegment) (hr : MemReadable s (stackPtr s) 8) :
    Prelude.nearReturn64Boundary s = .ok (returnBoundary s) := by
  unfold Prelude.nearReturn64Boundary
  dsimp only
  rw [show s.regValue .rsp = stackPtr s from rfl, popStack_run s h hss (stackPtr s) hr]
  rfl

/--
A terminating deterministic runner has a least successful fuel and a unique final state, relative
to the boundary `Prelude.nearReturn64Boundary` computes.
-/
theorem Returns.unique_of_boundary [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {fuel : Nat} (hb : Prelude.nearReturn64Boundary s = .ok boundary)
    (h : Returns boundary fuel s t) :
    ∃ least, Prelude.UniqueExecution s least t := by
  classical
  have leastFuel (n : Nat) (hn : Returns boundary n s t) :
      ∃ least, Returns boundary least s t ∧
        ∀ other, Returns boundary other s t → least ≤ other := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      by_cases hsmall : ∃ other, other < n ∧ Returns boundary other s t
      · obtain ⟨other, hlt, hother⟩ := hsmall
        exact ih other hlt hother
      · exact ⟨n, hn, fun other hother => Nat.le_of_not_lt fun hlt =>
          hsmall ⟨other, hlt, hother⟩⟩
  obtain ⟨least, hleast, hmin⟩ := leastFuel fuel h
  refine ⟨least, boundary, hb, hleast, ?_⟩
  intro n final hrun
  have heq : final = t := by
    have hleft := Returns.mono hrun (Nat.le_max_left n least)
    have hright := Returns.mono hleast (Nat.le_max_right n least)
    unfold Returns at hleft hright
    rw [hright] at hleft
    simpa using hleft.symm
  subst final
  exact ⟨hmin n hrun, rfl⟩

/--
A run from `s` that returns to `returnBoundary s` is the unique execution
`Prelude.UniqueExecution` asks for, when `s` reads its return slot through the flat stack segment.
-/
theorem Returns.unique [Bindings] {s t : RamState} {fuel : Nat} (hdata : DataReady s)
    (hss : s.SS = userStackSegment) (hr : MemReadable s (stackPtr s) 8)
    (h : Returns (returnBoundary s) fuel s t) :
    ∃ least, Prelude.UniqueExecution s least t :=
  Returns.unique_of_boundary (nearReturn64Boundary_eq s hdata hss hr) h

end X86Proofs
