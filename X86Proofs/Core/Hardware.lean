import X86

/-!
# The hardware meaning of lean-x86's replaceable helpers

lean-x86 makes linear-to-physical translation (`Translate_Linear_To_Physical.Semantics`) and event
delivery (`Handle_Vectored_Event.Semantics`) parameters of the helpers that call them, so that a
userspace VM can supply its own. `X86.Machine.step` defaults them to the generated hardware
implementations (`defaultSemantics`); lean-x86 provides the same choice for clients that call
individual helpers as scoped instances in `X86.Machine.Hardware`.

The proofs here are about the bare machine, so every helper they state means its hardware version.
These instances are lean-x86's, scoped to `X86Proofs` so that each file in the namespace (or
opening it) has them without opening `X86.Machine.Hardware`.

The scoped `X86.Accelerate` instance makes proofs take each accelerator at its source
implementation. `X86.Accelerate.fast_eq` relates them; `accelerated_eq_self` provides its
`X86.accelerated` form here so callers do not unfold that wrapper in multiple files.
-/

namespace X86Proofs

open X86.Machine

/-- Translation is the generated page walk (`X86.Machine.Hardware`'s instance). -/
scoped instance [Bindings] {σ : Type} [PhysicalMemory σ] :
    X86.Helpers.Translate_Linear_To_Physical.Semantics σ :=
  X86.Helpers.Translate_Linear_To_Physical.defaultSemantics

/-- Event delivery is the generated one (`X86.Machine.Hardware`'s instance). -/
scoped instance [Bindings] {σ : Type} [PhysicalMemory σ]
    [X86.Helpers.Translate_Linear_To_Physical.Semantics σ] :
    X86.Helpers.Handle_Vectored_Event.Semantics σ :=
  X86.Helpers.Handle_Vectored_Event.defaultSemantics

/-- Proofs use the source implementation of every proved accelerator. -/
scoped instance {α : Type} (source : α) : X86.Accelerate source := ⟨source, rfl⟩

/-- The `X86.accelerated` form of `X86.Accelerate.fast_eq`, owned here to keep the wrapper
unfolding in one file. -/
theorem accelerated_eq_self {α : Type} (source : α) [X86.Accelerate source] :
    X86.accelerated source = source := X86.Accelerate.fast_eq

end X86Proofs
