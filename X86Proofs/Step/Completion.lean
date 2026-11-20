import X86Proofs.Core.Run

/-!
# The decoded-instruction completion boundary

After the dispatched decoder returns normally, lean-x86's generated `Fetch_And_Execute` clears
the repeat flag (`Repeat_String_Operation`) unless the instruction is an effective repeat-prefixed
string instruction
(or its out-of-profile REX2 exemption), so the repeat flag does not remain set beyond the string
instruction that set it. Faults and nontermination bypass the cleanup. This file names that
wrapper (`completeDecoded`) and its effect on the state (`finishDecoded`); it does not replace the
generated dispatcher or decode an opcode.

`finishDecoded` is the repeat-flag cleanup inside `Fetch_And_Execute`. It is not `finishStep`
(`Step/ReadyToStepCore.lean`), which `Step` applies afterwards to the state `Fetch_And_Execute`
returns: it updates RIP (to `Next_IP` unless the instruction branched, is still repeating or is an
MSR-list operation in progress). A step proof meets them in that order:
`eq_of_finishDecoded (fun t => some (StepResult.next (finishStep t)))`.
-/
namespace X86Proofs
open X86 X86.Runtime X86.Helpers

/-- Effective legacy REP-string classification, using the byte already read by the scan.
REX2 is excluded by `ScanOpcode`, so its dispatcher exemption cannot occur here. -/
def scanPreservesRepeat (op : BitVec 8) (ctx : Instruction_Context) : Bool :=
  ctx.rep_prefix != 0 &&
    (op == 108 || op == 109 || op == 110 ||
     op == 111 || op == 164 || op == 165 ||
     op == 166 || op == 167 || op == 170 ||
     op == 171 || op == 172 || op == 173 ||
     op == 174 || op == 175)

theorem scanPreservesRepeat_escape (ctx : Instruction_Context) :
    scanPreservesRepeat 0x0F ctx = false := by
  simp [scanPreservesRepeat]

/-- State at decoded completion. Other instruction fields and the external state are unchanged. -/
def finishDecoded {σ : Type} (preserveRepeat : Bool) (s : State σ) : State σ :=
  if preserveRepeat then s
  else { s with Repeat_String_Operation := false }

/-- The completion wrapper of generated `Fetch_And_Execute`: run the dispatched decoder, then clear
the repeat flag (`Repeat_String_Operation`) unless the instruction keeps it. Faults and
nontermination bypass cleanup. -/
def completeDecoded {σ α : Type} (preserveRepeat : Bool)
    (action : PartialSpecM Exception (State σ) α) : PartialSpecM Exception (State σ) Unit := do
  let _ ← action
  if !preserveRepeat then
    modify ({ · with Repeat_String_Operation := false })

/-- Discarding a successful decoder value before or after the completion wrapper agrees.
Generated mutable-context dispatch returns an unused context; ordinary decoders return Unit. -/
theorem completeDecoded_discard {σ α : Type} (p : Bool)
    (a : PartialSpecM Exception (State σ) α) :
    completeDecoded p a = completeDecoded p (a >>= fun _ => pure ()) := by
  simp only [completeDecoded, bind_assoc, pure_bind]

/-- The wrapper depends only on the actual run, including divergence and fault state. -/
theorem completeDecoded_run_congr {σ : Type} (p : Bool)
    {a b : PartialSpecM Exception (State σ) Unit} {s t : State σ}
    (h : a.run s = b.run t) :
    (completeDecoded p a).run s = (completeDecoded p b).run t := by
  simp only [completeDecoded, Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind] at *
  rw [h]

/-- Compare generated dispatchers that return different unused bookkeeping values. -/
theorem completeDecoded_run_congr_discard {σ α β : Type} (p : Bool)
    {a : PartialSpecM Exception (State σ) α} {b : PartialSpecM Exception (State σ) β}
    {s t : State σ}
    (h : (a >>= fun _ => pure ()).run s = (b >>= fun _ => pure ()).run t) :
    (completeDecoded p a).run s = (completeDecoded p b).run t := by
  rw [completeDecoded_discard p a, completeDecoded_discard p b]
  exact completeDecoded_run_congr p h

/-- A normal decoded return passes through the generated completion transformer. -/
theorem completeDecoded_run_ok {σ : Type} (p : Bool)
    (a : PartialSpecM Exception (State σ) Unit) {s t : State σ}
    (h : a.run s = some (.ok (), t)) :
    (completeDecoded p a).run s = some (.ok (), finishDecoded p t) := by
  unfold completeDecoded
  rw [partialSpecM_bind_run _ _ h]
  cases p <;> rfl

/-- Divergence is preserved at this boundary. -/
theorem completeDecoded_run_none {σ : Type} (p : Bool)
    (a : PartialSpecM Exception (State σ) Unit) {s : State σ}
    (h : a.run s = none) : (completeDecoded p a).run s = none := by
  simp only [completeDecoded, Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind] at *
  rw [h]
  rfl

/-- A fault, including its state, bypasses decoded completion. -/
theorem completeDecoded_run_error {σ : Type} (p : Bool)
    (a : PartialSpecM Exception (State σ) Unit) {s t : State σ} {e : Error Exception}
    (h : a.run s = some (.error e, t)) :
    (completeDecoded p a).run s = some (.error e, t) := by
  simp only [completeDecoded, Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind,
    ExceptT.bindCont] at *
  rw [h]
  rfl

/-- Cleanup is an identity on an already clear completion, irrespective of the source repeat flag
(`Repeat_String_Operation`). -/
theorem finishDecoded_of_clear {σ : Type} (p : Bool) (s : State σ)
    (hr : s.Repeat_String_Operation = false) :
    finishDecoded p s = s := by
  cases p
  · simp only [finishDecoded, Bool.false_eq_true, ↓reduceIte]
    cases s
    cases hr
    rfl
  · rfl

/-- Remove decoded cleanup from an observed result when the actual endpoint already has the
repeat flag (`Repeat_String_Operation`) clear. The caller supplies the endpoint fact; no source
invariant is added. -/
theorem eq_of_finishDecoded {σ α : Type} {p : Bool} {t : State σ} {a : α}
    (f : State σ → α) (hr : t.Repeat_String_Operation = false)
    (h : a = f (finishDecoded p t)) : a = f t := by
  rwa [finishDecoded_of_clear p t hr] at h

end X86Proofs
